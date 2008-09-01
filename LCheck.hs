{-# LANGUAGE PatternSignatures #-}

--import qualified Data.RandomAccessStream as S
import Data.RandomAccessStream
import Test.QuickCheck hiding ((==>))
import Test.LazySmallCheck hiding (cons)
import qualified Test.SmallCheck as T
--import Test.SmallCheck
import Control.Applicative

import Prelude hiding (head, tail, map, scanl, scanl1, iterate, take,
  drop, takeWhile, dropWhile, repeat, cycle, filter, (!!), zip, unzip,
  unzip3, zipWith, words, unwords, lines, unlines, break, span,
  splitAt, zipWith3, zip3, concat, concatMap, lookup,(++))

import qualified Data.List as L

lCheck = 
    do
      {-
      putStrLn "toList . fromList == id"
      smallCheck 11 (\(x::[Bool]) -> L.take (length x) (toList (fromList x)) == x)
      
      putStrLn "dropWithCons == drop"
      smallCheck 5 (\(z'::FiniteStream Bool) m -> 
                        let z = toStream z' 
                        in equalUpTo 40 (dropWithCons m z) (drop m z) == EQ)
      
      putStrLn "fmap id == id"
      smallCheck 8 (\(x::Bool,y) -> 
                        let z = cycle (x:y) 
                        in equalUpTo 64 z (fmap id z) == EQ)

      putStrLn "fmap (f . g) == fmap f . fmap g"
      quickCheck (\(x::Int,y) (f::Int -> Int) g -> 
                      let z = cycle (x:y) in
                      equalUpTo 1000 (fmap (f . g) z) (fmap f (fmap g z)) == EQ)

      putStrLn "return a >> k == k a"
      quickCheck (\(a::Int) (k'::Int -> FiniteStream Int) -> 
                      let k = toStream . k' in
                      equalUpTo 200 (return a >>= k) (k a) == EQ)

      putStrLn "m >>= return == m"
      smallCheck 7 (\(x::Bool,y) -> 
                        let m = cycle (x:y) 
                        in equalUpTo 56 (m >>= return) m == EQ)

      putStrLn "(m >>= (\\x -> k x >>= h)) == ((m >>= k) >>= h)"
      quickCheck (\(x::Int,y) (k'::Int -> FiniteStream Int) (h'::Int -> FiniteStream Int) -> 
                      let m = cycle (x:y) 
                          k = toStream . k'
                          h = toStream . h'
                      in 
                      equalUpTo 75 (m >>= (\x -> k x >>= h)) ((m >>= k) >>= h) == EQ)

      putStrLn "(fmap f xs) (xs >>= return . f)"
      quickCheck (\(f::Int -> Int) (y::Int,z) -> let xs = cycle (y:z) in equalUpTo 500 (fmap f xs) (xs >>= return . f) == EQ)

      putStrLn "pure id <*> v = v"
      smallCheck 8 (\(x::Bool,y) -> 
                        let v = cycle (x:y)
                        in equalUpTo 64 (pure id <*> v) v == EQ)

      putStrLn "pure (.) <*> u <*> v <*> w = u <*> (v <*> w)"
      quickCheck (\(u' :: FiniteStream (Int -> Int))
                   (v' :: FiniteStream (Int -> Int))
                   (w' :: FiniteStream Int) ->
                   let u = toStream u'
                       v = toStream v'
                       w = toStream w'
                   in equalUpTo 300 (pure (.) <*> u <*> v <*> w) (u <*> (v <*> w)) == EQ)

      putStrLn "pure f <*> pure x = pure (f x)"
      quickCheck (\(f :: Int -> Int)
                   (x :: Int) ->
                   equalUpTo 1000 (pure f <*> pure x) (pure (f x)) == EQ)

      putStrLn "u <*> pure y = pure ($ y) <*> u"
      quickCheck (\(u' :: FiniteStream (Int -> Int))
                   (y :: Int) ->
                   let u = toStream u'
                   in equalUpTo 600 (u <*> pure y) (pure ($ y) <*> u) == EQ)

      putStrLn "fmap f x = pure f <*> x"
      quickCheck (\(f :: Int -> Int)
                   x' ->
                   let x = toStream x'
                   in equalUpTo 600 (fmap f x) (pure f <*> x) == EQ)

      putStrLn "y = tail (cons x y)"
      smallCheck 5 (\(x :: Int)
                     y' ->
                     let y = toStream y'
                     in equalUpTo 40 y (tail $ cons x y) == EQ)

      putStrLn "x = head (cons x y)"
      smallCheck 6 (\(x :: [Int])
                     y' ->
                     let y = toStream y'
                     in x == head (cons x y))

      putStrLn "head (intersperse x y) = head y"
      smallCheck 5 (\(x::[[Int]])
                    y' ->
                    let y = toStream y'
                    in head (intersperse x y) == head y)

      putStrLn "head (tail (intersperse x y)) = x"
      smallCheck 5 (\(x::[Int])
                    y' ->
                    let y = toStream y'
                    in head (tail (intersperse x y)) == x)

      putStrLn "tail (tail (intersperse x y)) = intersperse x (tail y)"
      smallCheck 3 (\(x::[Int])
                    y' ->
                    let y = toStream y'
                    in equalUpTo 32 (tail $ tail $ intersperse x y) (intersperse x $ tail y) == EQ)
      
      putStrLn "head (interleave x y) == head x"
      smallCheck 7 (\(x' :: FiniteStream [Int])
                    y' ->
                    let x = toStream x'
                        y = toStream y'
                    in head (interleave x y) == head x)

      putStrLn "head (tail (interleave x y)) == head y"
      smallCheck 7 (\(x' :: FiniteStream [Int])
                    y' ->
                    let x = toStream x'
                        y = toStream y'
                    in head (tail (interleave x y)) == head y)

      putStrLn "tail $ tail $ interleave x y == interleave (tail x) (tail y)"
      smallCheck 3 (\(x' :: FiniteStream [Int])
                    y' ->
                    let x = toStream x'
                        y = toStream y'
                    in equalUpTo 56 (tail (tail (interleave x y))) (interleave (tail x) (tail y)) == EQ)
      
      putStrLn "null x && not (all null y) => intercalate x y == concat y"
      smallCheck 4 (\(y'::FiniteStream [Int]) ->
                     let y = toStream y'
                     in concatable y' ==> equalUpTo 50 (intercalate [] y) (concat y) == EQ)
      
      putStrLn "null (head y) && not (null x) ==> head (intercalate x y) == head x"
      smallCheck 6 (\(y'::FiniteStream [[Int]]) 
                      xh xt ->
                      let y = toStream y'
                          x = xh:xt
                      in null (head y) ==> head (intercalate x y) == L.head x)
      
      putStrLn "not (null (head y)) ==> head (intercalate x y) == head (head y)"
      smallCheck 8 (\(y'::FiniteStream [[Int]]) x ->
                    let y = toStream y'
                    in not (null (head y)) ==> head (intercalate x y) == L.head (head y))
      
      putStrLn "null (head y) && not (null x) ==> tail (intercalate x y) == ((tail x) ++ (intercalate x (tail y)))"
      smallCheck 3 (\(y'::FiniteStream [Bool]) xh xt ->
                    let y = cons [] $ toStream y'
                        x = xh:xt
                    in equalUpTo 100 (tail (intercalate x y)) ((L.tail x) ++ (intercalate x (tail y))) == EQ)
      
      putStrLn "not (null (head y)) && not (all null y) ==> tail (intercalate x y) == intercalate x (cons (L.tail (head y)) (tail y))"
      smallCheck 3 (\yhh yht (y'::FiniteStream [Bool]) x ->
                    let y = cons (yhh:yht) $ toStream y'
                    in concatable y' ==> 
                       equalUpTo 10 (tail (intercalate x y)) (intercalate x (cons (L.tail (head y)) (tail y))) == EQ)
      
      putStrLn "head (transpose x) = map head x"
      smallCheck 6 (\(y' :: FiniteStream (FiniteStream Int)) ->
                    let y = toStream (fmap toStream y')
                    in equalUpTo 20 (head $ transpose y) (map head y) == EQ)

      putStrLn "tail (transpose x) = transpose (map tail x)"
      smallCheck 4 (\(y' :: FiniteStream (FiniteStream [Bool])) ->
                    let y = toStream (fmap toStream y')
                        little = upTo 20 take
                    in (little $ tail $ transpose y) == (little $ transpose $ map tail y))
      
      putStrLn "not (null (head x)) => head (concat x) = L.head (head x))"
      smallCheck 6 (\(xhh :: [Int]) xht x' ->
                    let x = cons (xhh:xht) $ toStream x'
                    in head (concat x) == L.head (head x))

      putStrLn "null (head x) && not (all null x) => concat x == concat (tail x)"
      smallCheck 4 (\(x' :: FiniteStream [[Bool]]) ->
                    let x = cons [] $ toStream x'
                    in concatable x' ==> equalUpTo 25 (concat x) (concat (tail x)) == EQ)

      putStrLn "not (null (head x)) && not (all null x) => tail (concat x) == (L.tail (head x))++(concat (tail x))"
      smallCheck 3 (\xhh xht (x' :: FiniteStream [[Bool]]) ->
                    let x = cons (xhh:xht) $ toStream x'
                    in concatable x' ==> equalUpTo 25 (tail $ concat x) ((L.tail $ head x) ++ (concat $ tail x)) == EQ)
      
      putStrLn "not (all null $ map f x) ==> concatMap f x == concat (map f x)"
      quickCheck (\(f::[Int] -> [Int]) (x' :: FiniteStream [Int]) ->
                  let x = toStream x'
                  in concatable (fmap f x') ==> equalUpTo 1800 (concatMap f x) (concat $ map f x) == EQ)
      
      putStrLn "head (iterate f x) == x"
      quickCheck (\f (x :: [[[Int]]]) ->
                  head (iterate f x) == x)

      putStrLn "tail (iterate f x) == iterate f (f x)"
      quickCheck (\f (x :: [Bool]) ->
                  equalUpTo 1000 (tail $ iterate f x) (iterate f (f x)) == EQ)
      
      putStrLn "head (repeat x) == x"
      smallCheck 6 (\(x::[Int]) -> head (repeat x) == x)

      putStrLn "tail (repeat x) == repeat x"
      smallCheck 5 (\(x::[Int]) -> equalUpTo 100 (tail $ repeat x) (repeat x) == EQ)
      
      putStrLn "head (cycle (x:xs)) == x"
      smallCheck 6 (\(x::[Int]) xs -> head (cycle (x:xs)) == x)

      putStrLn "tail (cycle (x:xs)) == xs ++ (cycle (x:xs)"
      smallCheck 3 (\(x::[Int]) xs -> equalUpTo 15 (tail $ cycle (x:xs)) (xs ++ cycle (x:xs)) == EQ)
      -}
      putStrLn "head (scanl f z x) == z"
      quickCheck (\f (z::[[[Int]]]) (x' :: FiniteStream Bool) ->
                  let x = toStream x'
                  in head (scanl f z x) == z)

      putStrLn "tail (scanl f z x) == scanl f (f z $ head x) (tail x)"
      quickCheck (\f (z :: Either Int Int) (x' :: FiniteStream [Bool]) ->
                  let x = toStream x'
                  in equalUpTo 500 (tail $ scanl f z x) (scanl f (f z $ head x) (tail x)) == EQ)

instance Serial Ordering where
    series =    cons0 EQ
             \/ cons0 LT
             \/ cons0 GT

concatable (FiniteStream x y) = not (null x) || not (all null y)
x &&& y = lift x *&* lift y