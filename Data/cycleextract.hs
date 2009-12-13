{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Cycleextract where

import List(genericIndex)
data Braun a = Conb a (Braun a) (Braun a)

data BraunRef a = Conr a (BraunRef a) (BraunRef a)
                | Ref Integer deriving (Show)

size (Ref _) = 1
size (Conr _ x y) = 1 + size x + size y

mymod n 0 = 0
mymod n m = mod n m

floorlg2 x =
    case x `div` 2 of
      0 -> 0
      y -> 1 + floorlg2 y

--myincr :: Nat -> Nat -> Nat
myincr real mod =
  mymod (2^(floorlg2 (1+real))) mod

--memo :: Nat -> (Prod Nat Nat) -> Option Nat
memo n (p,i) =
    case (compare p n, compare i (myincr p n)) of
      (LT,EQ) -> Just p
      _ -> Nothing
{-
action :: (Sum (Prod (Prod Nat Nat) ((Prod Nat Nat) -> Option Nat))
          (Prod (Prod a1 (CoList a1)) Nat)) -> Sum
          (Prod (Prod Nat Nat) ((Prod Nat Nat) -> Option Nat))
          (Prod (Prod a1 (CoList a1)) Nat)
-}
type LHS x = (x,x,(x,x) -> Maybe x)
type RHS x a = (a,[a],x)
type Trip' x a = Either (LHS x) (RHS x a)
type Trip a = Trip' Integer a

action :: Trip a -> Trip a
action (Left (real,mod,f)) =
    Left (real+1,mod,
          case f (mymod real mod, myincr real mod) of
            Just _ -> f
            Nothing -> 
                (\(p,i) ->
                 if (p == mymod real mod) && (i == myincr real mod)
                 then Just real
                 else f (p,i)))
action (Right (_,[],sofar)) = Left (1+sofar,1+sofar,memo (1+sofar))
action (Right (_,hed:tyl,sofar)) = Right (hed,tyl,1+sofar)
{-
mat' :: (Prod a1 (CoList a1)) -> (CoList a1) -> Nat -> a1
mat' whole rem n =
  case n of
    O ->
      (case rem of
         Nil -> (case whole of
                   Pair ans x -> ans)
         Cons ans c -> ans)
    S m ->
      (case rem of
         Nil -> mat' whole (case whole of
                              Pair x rest -> rest) m
         Cons a rest -> mat' whole rest m)

mat :: (Prod a1 (CoList a1)) -> Nat -> a1
mat whole n =
  mat' whole (case whole of
                Pair hed tyl -> Cons hed tyl) n
-}
{-
trunk :: (Prod a1 (CoList a1)) -> (Braun
            (Sum (Prod (Prod Nat Nat) ((Prod Nat Nat) -> Option Nat))
            (Prod (Prod a1 (CoList a1)) Nat))) -> BraunRef 
            a1
-}
trunkate :: [a] -> Braun (Trip a) -> BraunRef a
trunkate whole (Conb (Left (real,mod,f)) od ev) =
    case f (mymod real mod,myincr real mod) of
      Just bak -> Ref bak
      Nothing -> Conr (whole `genericIndex` (mymod real mod)) 
                      (trunkate whole od) 
                      (trunkate whole ev)
trunkate whole (Conb (Right (hed,c,n)) od ev) =
    Conr hed (trunkate whole od)
             (trunkate whole ev)
{-
cycle :: (() -> (() -> ()) -> () -> Braun ()) -> a1 -> (CoList 
         a1) -> BraunRef a1
-}
iterateSlow :: (a->a) -> a -> Braun a
iterateSlow f x =
  let g z = f (f z)
      y = f x 
  in Conb x (iterateSlow g y) (iterateSlow g (f y))

instance Functor Braun where
    fmap f (Conb h o e) = Conb (f h) (fmap f o) (fmap f e)

oddFromEven :: (a -> a) -> a -> Braun a -> Braun a
oddFromEven f x  ~(Conb h od ev) =
    Conb x (oddFromEven f (f h) ev) (fmap f od)

iterateFast :: (a -> a) -> a -> Braun a
iterateFast f x =
    let ev = fmap f od
        od = oddFromEven f (f x) ev
    in
      Conb x od ev

bcycle' iter hed tyl =
  trunkate (hed:tyl)
    (iter action (Right (hed,tyl,0)))

bcycle x xs = bcycle' iterateFast x xs

display m f =
    [((i,j),k) | i <- [0..(m-1)], j <- [0..(m-1)], k <- case f (i,j) of Just v -> [v]; _ -> []]

--prin :: Show a => Trip a -> String
prin (Left (x,y,f)) = show (x,y, display y f)
prin x@(Right y) = show y

beta' i m s = 
    case (i+i) `mod` m of
      1 -> s+1
      j -> beta' j m (s+1)
beta m = 
    if (m `mod` 2 == 1) && (m >= 3)
    then beta' 2 m 1
    else 1

oddpart n = 
    case n `quotRem` 2 of
      (m,0) -> oddpart m
      _ -> n

bound n = 
    let m = oddpart n
        r = floorlg2 (n`div`m)
    in 
      2^(r+1) * m * beta m + 2^(r+1) - 1

order 0 = []
order 1 = [True]
order 2 = [False]
order n =
    case n`quotRem`2 of
      (m,0) -> False:(order (m-1))
      (m,1) -> True:(order m)

srat' g (Ref n) b = 
    let (h,o,e) = srat g (order n)
    in srat' g (Conr h o e) b
srat' g (Conr h o e) [] = (h,o,e)
srat' g (Conr _ o _) (True:b) = srat' g o b
srat' g (Conr _ _ e) (False:b) = srat' g e b

srat g b = srat' g g b
rat g b = 
    let (h,_,_) = srat g b 
    in h

{-
rat (bcycle 0 [1]) (order 7)
rat (Conr 0 (Conr 1 (Ref 1) (Ref 1)) (Conr 0 (Ref 2) (Ref 2))) [True,True,True]
srat (Conr 0 (Conr 1 (Ref 1) (Ref 1)) (Conr 0 (Ref 2) (Ref 2))) [True,True,True]
srat' (Conr 0 (Conr 1 (Ref 1) (Ref 1)) (Conr 0 (Ref 2) (Ref 2))) (Conr 0 (Conr 1 (Ref 1) (Ref 1)) (Conr 0 (Ref 2) (Ref 2))) [True,True,True]
srat' (Conr 0 (Conr 1 (Ref 1) (Ref 1)) (Conr 0 (Ref 2) (Ref 2))) (Conr 1 (Ref 1) (Ref 1)) [True,True]
srat' (Conr 0 (Conr 1 (Ref 1) (Ref 1)) (Conr 0 (Ref 2) (Ref 2))) (Ref 1) [True]
srat (Conr 0 (Conr 1 (Ref 1) (Ref 1)) (Conr 0 (Ref 2) (Ref 2))) (order 1)
srat (Conr 0 (Conr 1 (Ref 1) (Ref 1)) (Conr 0 (Ref 2) (Ref 2))) [True]
srat' (Conr 0 (Conr 1 (Ref 1) (Ref 1)) (Conr 0 (Ref 2) (Ref 2))) (Conr 0 (Conr 1 (Ref 1) (Ref 1)) (Conr 0 (Ref 2) (Ref 2))) [True]
-}

bat (Conb h _ _) [] = h
bat (Conb _ o _) (True:b) = bat o b
bat (Conb _ _ e) (False:b) = bat e b

lcycle x xs =
    let ans = nex x xs
        nex x [] = x:ans
        nex x (y:ys) = x:(nex y ys)
    in ans

fromList x = fmap head (iterateFast tail x)

ncycle x xs = fromList (lcycle x xs)

{-
*Cycleextract> [(j,let (x:xs) = [0..j] in let a = ncycle x xs in let b = bcycle x xs in and [bat a i == rat b i | i <- fmap order [0..1000]]) | j <- [0..100]]
-}