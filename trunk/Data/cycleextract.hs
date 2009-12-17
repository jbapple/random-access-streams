{-# OPTIONS_GHC -cpp -fglasgow-exts #-}
{-# LANGUAGE ScopedTypeVariables #-}
{- For Hugs, use the option -F"cpp -P -traditional" -}

module Cycleextract where

import qualified Debug.Trace as D
import List(genericIndex,nub,genericLength)
import qualified Data.Map as M
import qualified Data.Set as S
import Maybe

data BS a = BS a (BS a) (BS a)

data BraunRef a = Branch a (BraunRef a) (BraunRef a)
                | Ref [Bool] 
                  deriving (Show)

size (Ref _) = 1
size (Branch _ x y) = 1 + size x + size y

mymod n 0 = 0
mymod n m = mod n m

------------------
floorlg2 0 = 0
floorlg2 1 = 0
floorlg2 x = 1 + floorlg2 (x `div` 2)

increm real len =
  mod (2^(floorlg2 (1+real))) len

memo n = M.fromList [((p,increm p n),p) | p <- [0..(n-1)]]

type Fin x = (x,x,M.Map (x,x) x)
type Unk x a = (a,[a],x)
type Trak' x a = Either (Fin x) (Unk x a)
type Trak a = Trak' Integer a
{-
action x@(Left (r,_,_)) = 
    D.trace ("Left:"++(show r)++"\n") action' x
action x@(Right (_,_,r)) = 
    D.trace ("Right: "++(show r)++"\n") action' x
  -}
action = action'  

action' :: Trak a -> Trak a
action' (Left (real,len,f)) =
    Left (real+1,len,
          let addr = (mod real len, increm real len)
          in case M.lookup addr f of
               Just _ -> f
               Nothing -> M.insert addr real f)
action' (Right (_,[],sofar)) = Left (1+sofar,1+sofar,memo (1+sofar))
action' (Right (_,hed:tyl,sofar)) = Right (hed,tyl,1+sofar)

checkBack :: [a] -> Trak a -> Either a [Bool]
checkBack whole (Left (real,len,f)) =
    case M.lookup (mod real len,increm real len) f of
      Just bak -> Right (order bak)
      Nothing -> Left (whole `genericIndex` (mod real len)) 
checkBack _ (Right (hed,_,_)) = Left hed

kill :: BS (Either a [Bool]) -> BraunRef a
kill (BS (Left h) o e) = Branch h (kill o) (kill e)
kill (BS (Right v) _ _) = Ref v
    
trunc :: [a] -> BS (Trak a) -> BraunRef a
trunc w x = kill (fmap5 (checkBack w) x)

main = 
    do n <- readLn
       let (x:xs) = [1..n]
       print (bcycle x xs)

unref x = let ans = unref' ans x
          in ans
unref' cont (Ref v) = substream cont v
unref' cont (Branch h o e) = BS h (unref' cont o) (unref' cont e)
substream x [] = x
substream (BS _ o _) (True:r) = substream o r
substream (BS _ _ e) (False:r) = substream e r

{-
Branch 0 (Branch 1 (Branch 3 (Branch 7 (Branch 15 (Branch 12 _ _) (Branch 9 (Branch 3 (Branch 10 (Branch 5 (Branch 14 (Branch 13 (Branch 11 (Branch 7 (Branch 18 (Branch 2 (Branch 8 (Branch 1 (Branch 6 (Branch 16 (Branch 17 *** Exception: stack overflow
-}

{-
trace (bcycle 0 [1..18]) (map (== '0') "0000100000000000000")
*** Exception: stack overflow
-}

{-
trunc whole (BS (Left (real,len,f)) od ev) =
    case f (mod real len,increm real len) of
      Just bak -> Ref (order bak)
      Nothing -> Branch (whole `genericIndex` (mod real len)) 
                        (trunc whole od) 
                        (trunc whole ev)
trunc whole (BS (Right (hed,_,_)) od ev) =
    Branch hed (trunc whole od)
               (trunc whole ev)
-}
bcycle' iter hed tyl =
  trunc (hed:tyl)
    (iter action (Right (hed,tyl,0)))

bcycle x xs = bcycle' iterateFast x xs
----------------------------------------


{-
cycle :: (() -> (() -> ()) -> () -> BS ()) -> a1 -> (CoList 
         a1) -> BraunRef a1
-}
iterateSlow :: (a->a) -> a -> BS a
iterateSlow f x =
  let g z = f (f z)
      y = f x 
  in BS x (iterateSlow g y) (iterateSlow g (f y))

instance Functor BS where
    fmap f (BS h o e) = BS (f h) (fmap3 f o) (fmap4 f e)

fmap5 = fmap
fmap3 = fmap
fmap4 = fmap
fmap2 = fmap
fmap1 = fmap

oddFromEven :: (a -> a) -> a -> BS a -> BS a
oddFromEven f x  ~(BS h od ev) =
    BS x (oddFromEven f (f h) ev) (fmap2 f od)

iterateFast :: (a -> a) -> a -> BS a
iterateFast f x =
    let ev = fmap1 f od
        od = oddFromEven f (f x) ev
    in
      BS x od ev


display m f =
    [((i,j),k) | i <- [0..(m-1)], j <- [0..(m-1)], k <- case f (i,j) of Just v -> [v]; _ -> []]

--prin :: Show a => Trak a -> String
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

bound :: Integer -> Integer
bound n = 
    let m = oddpart n
        r = floorlg2 (n`div`m)
    in 
      2^(r+1) * m * beta m + 2^(r+1) - 1

order :: Integer -> [Bool]
order 0 = []
order 1 = [True]
order 2 = [False]
order n =
    case n`quotRem`2 of
      (m,0) -> False:(order (m-1))
      (m,1) -> True:(order m)

toInt :: [Bool] -> Integer
toInt [] = 0
toInt (True:x) = 1 + 2*(toInt x)
toInt (False:x) = 2 + 2*(toInt x)

list = order

{-
context g (Branch h o e) [] = (h,o,e)
context g (Branch _ o _) (True:b) = context g o b
context g (Branch _ _ e) (False:b) = context g e b
context g (Ref n) b = triple g (n++b)

triple g b = context g g b
trace g b = 
    let (h,_,_) = triple g b 
    in h
-}
context g (Branch v _ _) [] = v
context g (Branch _ o _) (True:r) = context g o r
context g (Branch _ _ e) (False:r) = context g e r
context g (Ref p) r = context g g (p++r)

trace g b = context g g b
{-
context g (Branch h o e) [] = (h,o,e)
context g (Branch _ o _) (True:b) = context g o b
context g (Branch _ _ e) (False:b) = context g e b
context g (Ref n) b = context g g (n++b)

trace g b = 
    let (h,_,_) = context g g b 
    in h
-}
{-
rat (bcycle 0 [1]) (order 7)
rat (Branch 0 (Branch 1 (Ref 1) (Ref 1)) (Branch 0 (Ref 2) (Ref 2))) [True,True,True]
srat (Branch 0 (Branch 1 (Ref 1) (Ref 1)) (Branch 0 (Ref 2) (Ref 2))) [True,True,True]
srat' (Branch 0 (Branch 1 (Ref 1) (Ref 1)) (Branch 0 (Ref 2) (Ref 2))) (Branch 0 (Branch 1 (Ref 1) (Ref 1)) (Branch 0 (Ref 2) (Ref 2))) [True,True,True]
srat' (Branch 0 (Branch 1 (Ref 1) (Ref 1)) (Branch 0 (Ref 2) (Ref 2))) (Branch 1 (Ref 1) (Ref 1)) [True,True]
srat' (Branch 0 (Branch 1 (Ref 1) (Ref 1)) (Branch 0 (Ref 2) (Ref 2))) (Ref 1) [True]
srat (Branch 0 (Branch 1 (Ref 1) (Ref 1)) (Branch 0 (Ref 2) (Ref 2))) (order 1)
srat (Branch 0 (Branch 1 (Ref 1) (Ref 1)) (Branch 0 (Ref 2) (Ref 2))) [True]
srat' (Branch 0 (Branch 1 (Ref 1) (Ref 1)) (Branch 0 (Ref 2) (Ref 2))) (Branch 0 (Branch 1 (Ref 1) (Ref 1)) (Branch 0 (Ref 2) (Ref 2))) [True]
-}

bat (BS h _ _) [] = h
bat (BS _ o _) (True:b) = bat o b
bat (BS _ _ e) (False:b) = bat e b

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

twoOdd :: Integer -> [(Integer,Integer)]
twoOdd n = [(i,j) | i <- uniq [(2^k) `mod` n| k <- [0..(n-1)]], j <- [0..(n-1)]]
{-
*Cycleextract> and [let j = 2*i+1 in 2 * (genericLength $ twoOdd j) + 1 == bound j | i <- [0..1000]]
-}

uniq = S.toList . S.fromList

twoGroup :: Integer -> [(Integer,Integer)]
twoGroup n = 
    case n `quotRem` 2 of
      (_,1) -> twoOdd n
      (m,0) -> let half = twoGroup m
                   side v (incr,offs) = ((2*incr)`mod`n, (2*offs+v)`mod`n)
                   oddSide = side 1
                   evenSide = side 2
               in (1,0):(map oddSide half)++(map evenSide half)

twist :: BS a -> [a] -> Integer -> ((Integer,Integer) -> BS a) -> (Integer,Integer) -> BS a
twist top whole n fynd (incr,offs) =
    if increm offs n == incr
    then substream top (list incr)
    else BS (whole `genericIndex` (offs`mod`n))
            (fynd ((2*incr)`mod`n, (offs+incr)`mod`n))
            (fynd ((2*incr)`mod`n, (offs+2*incr)`mod`n))

memory :: BS a -> [a] -> Integer -> M.Map (Integer,Integer) (BS a)
memory (top :: BS a) whole n = 
    let b :: [(Integer,Integer)]
        b = twoGroup n
        init :: [((Integer,Integer),BS a)]
        init = map (\x -> (x,twist top whole n fynd x)) b
        save :: M.Map (Integer,Integer) (BS a)
        save = M.fromList init
        fynd :: (Integer,Integer) -> BS a
        fynd addr = case M.lookup addr save of
                      Just v -> v
                      _ -> error $ ((show b)++"\n"++(show addr))
    in save

act _ _ (Right (_,y:ys,n)) = Right (y,ys,n+1)
act top whole (Right (_,[],n)) = Left (memory top whole (n+1), n+1, n+1)
act _ _ (Left (f, real, len)) = Left (f, real+1, len)

addrOf loc len = (increm loc len, loc`mod`len)

trundle (BS (Right (h,_,_)) o e) = BS h (trundle o) (trundle e)
trundle (BS (Left (f,loc,len)) _ _) = 
    let addr = addrOf loc len
    in case M.lookup addr f of
         Just v -> v
         _ -> error ((show addr)++"\n"++(show loc)++"\n"++(show len)++"\n"++(show $ map fst $ M.toList f))

qcycle w ws = let ans = trundle (iterateFast (act ans (w:ws))
                                             (Right (w,ws,0)))
              in ans