{-# LANGUAGE DeriveDataTypeable #-}

-- {-# OPTIONS -fglasgow-exts #-}

{- | 

A stream is an infinite list.
Using lists, or traditional, linear streams, definind in "Data.Stream" as

> data Stream a = Cons a (Stream a)

@Θ(i)@ time is required to access the @i@'th element from the head of the stream. 
This module offers Data.RandomAccessStream.'Stream', taking only @O(lg i)@ time to access the @i@'th element, but @Θ(lg n)@ time to perform a 'cons'.

Of course, streams are infinite, so it is not clear what it means to take @Θ(f(n))@ time to perform an operation, since there is no @n@ implicitly defined as the size of the stream. 
Traversing the first 2^i-1 elements of a RandomAccessStream (using 'fromList', for instance) takes Ω(2^i-1) time.
If it takes time t to traverse these elements, it will take t+Ω(i) time to traverse them after calling 'cons'.
If a linear stream were used instead, the traversal time would have only increased to t+1.

There are random access lists with constant-time cons, such as Data.Sequence.
However, they are not safe under circular constructions like

@let dangerousBees = cons 'b' dangerousBees@

-}

module Data.RandomAccessStream 
    (Stream(..)
     -- * Basic Functions
    ,cons
    ,head
    ,tail
     ,(++)
    ,(+++)
    -- * Transformations
    ,map
    ,intersperse
    ,interleave
    ,intercalate
    ,transpose
    -- * Special folds
    ,concat
    ,concatMap
    -- * Building streams
    ,iterate
    ,repeat
    ,cycle
    ,cycleFinite
    -- ** Scans
    ,scanl
    ,scanl1
    -- ** Unfolding
    ,unfoldr
    -- * Sublists and substreams
    -- ** Finite approximations
    ,upTo
    ,compareUpTo
    ,compareUnequal
    ,equalUpTo
    -- ** Extracting sublists and substreams
    ,everyNth
    ,take
    ,drop
    ,dropWithCons
    ,splitAt
    ,splitAtWithCons
    ,takeWhile
    ,dropWhile
    ,dropWhileWithCons
    ,span
    ,spanWithCons
    ,break
    ,breakWithCons
    ,stripPrefix
    ,group
    ,groupSafe
    ,inits
    ,tails
    -- ** Predicates
    ,isPrefixOf
    -- * Searching
    ,lookup
    ,find
    ,filter
    ,partition 
    -- * Indexing
    ,(!!)
    ,adjust
    ,elemIndex
    ,elemIndices
    ,findIndex
    ,findIndices 
    -- * Conversions
    ,fromList
    ,toList
--    ,fromLinearStream
--    ,toLinearStream
     -- ** Zips
    ,zip
    ,zip3
    ,zip4
    ,zip5
    ,zip6
    ,zip7
    ,zipWith
    ,zipWith3
    ,zipWith4
    ,zipWith5
    ,zipWith6
    ,zipWith7
    ,unzip
    ,unzip3
    ,unzip4
    ,unzip5
    ,unzip6
    ,unzip7
    -- * Special Streams
    -- ** Functions on Strings
    ,lines
    ,words
    ,unlines
    ,unwords
    -- ** Set operations
    ,nub
    ,delete
    ,(\\)
    ,union
    ,intersect
    -- ** Ordered lists
    ,insert
    -- * Generalized functions
    -- ** The @By@ operations
    -- *** User-supplied equality (replacing an @Eq@ context)
    -- | The predicate is assumed to define an equivalence.
    , nubBy 
    , deleteBy
    , deleteFirstsBy
    , unionBy       
    , intersectBy   
    , groupBy       
    , groupBySafe
    -- *** User-supplied comparison (replacing an @Ord@ context)
    -- | The function is assumed to define a total ordering.
    , insertBy      

    -- ** The @generic@ operations
     
    , genericTake   
    , genericDrop
    , genericDropWithCons
    , genericSplitAt
    , genericSplitAtWithCons
    , genericIndex  
--    ,memoize
    )
where

import Prelude hiding (head, tail, map, scanl, scanl1, iterate, take,
  drop, takeWhile, dropWhile, repeat, cycle, filter, (!!), zip, unzip,
  unzip3, zipWith, words, unwords, lines, unlines, break, span,
  splitAt, zipWith3, zip3, concat, concatMap, lookup, (++),catch)

import Control.Applicative
import qualified Data.List as L
import Maybe
import Data.Typeable
import Data.Generics.Basics
import Test.QuickCheck
import Array
-- TODO: zipper

data Stream a = Stream a (Stream a) (Stream a) 
   deriving (Data,Typeable)

instance Functor Stream where
    fmap f ~(Stream p q r) = Stream (f p) (fmap f q) (fmap f r)

instance Monad Stream where
    return a = repeat a
    x >>= f =
        jn $ fmap f x
        where
          jn ~(Stream p q r) = 
              Stream (hd p) (q >>= od) (r >>= ev)
          hd (Stream h _ _) = h
          od (Stream _ o _) = o
          ev (Stream _ _ e) = e

{- | 
Θ(lg n).
Adds an element onto the head of the 'Stream'.
If traversing the first n elements of a stream x takes time t, traversing the first n elements of (cons y x) takes t + Θ(lg n) time.
The extra cost is incurred at the elements at positions 2^i-1, counting from 0.
-}
cons :: a -> Stream a -> Stream a
cons x ~(Stream p q r) = Stream x (cons p r) q

{- | 
Θ(lg n).
Removes an element from the head of the 'Stream'.
If traversing the first n+1 elements of a stream x takes time t, traversing the first n elements of (tail x) takes t + Θ(lg n) time.
The extra cost is incurred just before the elements at positions 2^i-2, counting from 0.
-}
tail :: Stream a -> Stream a
tail ~(Stream _ q r) = Stream (head q) r (tail q)

-- | O(1). The first element in a stream.
head :: Stream a -> a
head (Stream p _ _) = p

{- |

Appends a list onto the front of a stream without incurring a 'cons'-ing costs.
See also '+++'.
If traversing the first n elements of a list x takes time t, traversing the first n elements of x++y takes time t+O(n).
If a list x has n elements, and traversing them takes time t, and traversing the first m elements of a stream y takes time s, the traversing the first n+m elements of x++y takes time t + s + Θ(n+m).

Compared with '+++', '++' is faster except when the size of the list is a small fraction of the number of elements of the stream that eventually get forced.

On the other hand, '++' loses any sharing information in the stream. So, not only is 

> ([1] ++ repeat 2) `genericIndex` (10^60)

not as fast as if we had used '+++', it also needs to allocate a list
of size 10^60 before returning the answer.

-}

{-# INLINE (++) #-}
(++) :: [a] -> Stream a -> Stream a
x ++ y = fromList $ (L.++) x $ toList y


{-# RULES
"toList/fromList" forall a . toList (fromList a) = a
"fromList/toList" forall a . fromList (toList a) = a
  #-}

{-# RULES
"filter/cycle" forall f a . L.filter f (L.cycle a) = L.cycle (L.filter f a)
 #-}

{- |

Appends a list onto the front of a stream.
It traversing the first n elements of a list x takes time t, and traversing the first m elements of a stream y takes time s, the traversing the first n+m elements of x++y takes time t + s + Θ(n+m).


If the list has length n and n+k elements from the resulting stream are forced, we traverse an
extra 1 thunk at each of the first n elements, plus lg ((k+n)!/k!)
additional thunks, distributed with a complicated density throughout
the stream, including the initial n elements.

Compared with '++', '+++' is faster only when n is small compared to
k.

'+++' also maintains sharing information, so 

> ([1] +++ repeat 2) `genericIndex` (10^60)

actually does not allocate more than O(lg (10^60)) new cells.

-}

{-# INLINE (+++) #-}
(+++) :: [a] -> Stream a -> Stream a
x +++ y = foldr cons y x


-- | Applies the given function to every element of the stream
map :: (a -> b) -> Stream a -> Stream b
map = fmap

-- | O(lg n) thunks at positions 2^i-4. Inserts an element between
-- every pair of adjacent elements in the input stream.
--
-- > intersperse y x == interleave x (repeat y)
--
intersperse :: a -> Stream a -> Stream a
intersperse y x = interleave x (repeat y)

{- | 
Θ(lg n) thunks placed at positions 2^i-4. @interleave x y@
creates a stream that alternates between the values in x and y,
starting with x.

> interleave (fromList [0,2 ..]) (fromList [1,3 ..]) == fromList [0..]

-}
interleave :: Stream a -> Stream a -> Stream a
interleave x y = Stream (head x) y (tail x)

{- |

Θ(|result|) thunks, O(1) at each element of the result. @intercalate x
y@ concatenates the elements of y, using x as glue. Every place where
two lists form y are joined, x in inserted.

-}
{-# INLINE intercalate #-}
intercalate :: [a] -> Stream [a] -> Stream a
intercalate x = fromList . L.intercalate x . toList

-- | O(n) thunks, O(1) at each element of the result.
transpose :: Stream (Stream a) -> Stream (Stream a)
transpose = map fromList . fromList . L.transpose . L.map toList . toList

-- | O(n) thunks, O(1) at each element of the result. See 'Data.List.concat'.
concat :: Stream [a] -> Stream a
concat = fromList . L.concat . toList

-- | O(n) thunks, O(1) at each element of the result. See 'Data.List.concatMap'.
concatMap :: (a -> [b]) -> Stream a -> Stream b
concatMap f = fromList . L.concatMap f . toList


--TODO: ||ism

oddFromEven f x ~(Stream h od ev) =
    Stream x (oddFromEven f (f h) ev) (fmap f od)

{- | 

Forcing n elements of the result traverses Θ(n) thunks, O(1) at each
element of result. The passed function is called n times.

-}
iterate :: (a -> a) -> a -> Stream a
iterate f x =
    let ev = fmap f od
        od = oddFromEven f (f x) ev
    in
      Stream x od ev

{- |
O(1). Turns a value into an stream containing only that value.
-}
repeat :: a -> Stream a
repeat x = let y = Stream x y y in y


-- This could be faster. for instance, cycle [0,1] is Stream 0 (repeat 1) (repeat 0)
-- Is that really faster? Repeat still puts thunks everywhere
-- Would take up less memory.

-- | O(1) thunk at each element of result stream. Fails if argument is
-- the empty list.
{-# INLINE cycle #-}
cycle :: [a] -> Stream a
cycle = fromList . L.cycle

{-
head $ cycleFinite $ replicate (10^6) 2
*** Exception: stack overflow
-}

{-
*Data.RandomAccessStream> L.genericLength [1..(10^8)]
*** Exception: stack overflow
*Data.RandomAccessStream> length [1..(10^8)]
100000000
-}

{-
*Data.RandomAccessStream> length $  replicate (2^31) 2
0

generic replicate
-}

{- |

cycleFinite turns a finite list into a stream. Unlike cycle, it
actually preserves sharing. Calling it on an infinite list causes
non-termination.

-}
cycleFinite :: [a] -> Stream a
cycleFinite (x:xs) =
    let l = gl xs
        gl = L.foldl' (\x y -> 1+x) 0
        y = listArray (0,l) (x:xs)
        f i j = let k = (j+j) `mod` (l+1)
                    od = (i+j) `mod` (l+1)
                    ev = (i+j+j) `mod` (l+1)
                in Stream (y ! i) (f od k) (f ev k)

        in 
          f 0 1

cycleFiniteSafe :: (a,[a]) -> Stream a
cycleFiniteSafe (x,[]) = repeat x
cycleFiniteSafe x@(_,(_:_)) = cycleFiniteArray x ! 1 ! 0

type CycleArray a = Array Int (Array Int (Stream a))

-- allocates n^2 memory. Above version works, memoized, but vacuum does not show memoization
-- use intmap for incr maps, since incrs are only 2^i mod n
cycleFiniteArray :: (a,[a]) -> CycleArray a
cycleFiniteArray (x,[]) = listArray (0,0) [listArray (0,0) [repeat x]]
cycleFiniteArray (x,xs@(_:_)) =
    let l = gl xs
        gl = L.foldl' (\x y -> 1+x) 0
        y = listArray (0,l) (x:xs)
        lim = 1+l
        incrStart 0 i = repeat (y!(i`mod`lim))
        incrStart j i = 
            let zero = i`mod`lim
                one = (i+j)`mod`lim
                two = (one+j)`mod`lim
                incr = (j+j)`mod`lim
                next = incrMemo ! incr
            in
              Stream (y!zero) (next ! one) (next ! two)
        incrMemo = 
            listArray (0,l) 
              [listArray (0,l) 
                 [incrStart incr start | start <- [0..l]] 
                   | incr <- [0..l]]
    in
      incrMemo

incrAt n = 2^(incrAtHelp (n+1))

incrAtHelp n = 
    case n`div`2 of
      0 -> 0
      m -> 1 + (incrAtHelp m)

cyclePossiblyFiniteSafe :: (a,[a]) -> Stream a
cyclePossiblyFiniteSafe (x,xs) = 
    cyclePossiblyTrunc $ iterate (cyclePossiblyHelp (x,xs)) (0,Left (x,xs))

--make use either memoized version
cyclePossiblyHelp :: (a,[a]) -> (Int,Either (a,[a]) (CycleArray a)) -> (Int,Either (a,[a]) (CycleArray a))
cyclePossiblyHelp t (n,Left (x,[]))     = (n+1,Right $ cycleFiniteArray t)
cyclePossiblyHelp _ (n,Left (x,(y:ys))) = (n+1,Left (y,ys))
cyclePossiblyHelp _ (n,Right x)         = (n+1,Right x)
--iterative deeepening
--cyclePossiblyFinite :: 

cyclePossiblyTrunc :: Stream (Int,Either (a,[a]) (CycleArray a)) -> Stream a
cyclePossiblyTrunc (Stream (_,Left (hd,_)) od ev) =
    Stream hd (cyclePossiblyTrunc od) (cyclePossiblyTrunc ev)
cyclePossiblyTrunc (Stream (n,Right s) _ _) = 
    let (_,y) = bounds s
        len = 1+y
    in
    s ! ((incrAt n)`mod`len) ! (n`mod`len)


{-
cyclePossiblyFiniteSafe2 :: (a,[a]) -> Stream a
cyclePossiblyFiniteSafe2 (x,xs) = 
    let ans = cyclePossiblyTrunc2 $ iterate (cyclePossiblyHelp2 ans (x,xs)) (0,Left (x,xs))

--make use either memoized version
--cyclePossiblyHelp2 :: (a,[a]) -> (Int,Either (a,[a]) (CycleArray a)) -> (Int,Either (a,[a]) (CycleArray a))
cyclePossiblyHelp2 ans t (n,Left (x,[]))     = (n+1,Right $ cycleFiniteArray2 ans t)
cyclePossiblyHelp2 _   _ (n,Left (x,(y:ys))) = (n+1,Left (y,ys))
cyclePossiblyHelp2 _   _ (n,Right x)         = (n+1,Right x)
--iterative deeepening
--cyclePossiblyFinite :: 

--cyclePossiblyTrunc2 :: Stream (Int,Either (a,[a]) (CycleArray a)) -> Stream a
cyclePossiblyTrunc2 (Stream (_,Left (hd,_)) od ev) =
    Stream hd (cyclePossiblyTrunc2 od) (cyclePossiblyTrunc2 ev)
cyclePossiblyTrunc2 (Stream (n,Right s) _ _) = 
    let (_,y) = bounds s
        len = 1+y
    in
    s ! ((incrAt n)`mod`len) ! (n`mod`len)

--cycleFiniteArray :: (a,[a]) -> CycleArray a
cycleFiniteArray2 ans (_,[]) = listArray (0,0) [listArray (0,0) [ans]]
cycleFiniteArray2 ans (x,xs@(_:_)) =
    let l = gl xs
        gl = L.foldl' (\x y -> 1+x) 0
        y = listArray (0,l) (x:xs)
        lim = 1+l
        incrStart 0 i = repeat (y!(i`mod`lim))
        incrStart j i = 
            let zero = i`mod`lim
                one = (i+j)`mod`lim
                two = (one+j)`mod`lim
                incr = (j+j)`mod`lim
                next = incrMemo ! incr
            in
              if goodPair j i
              then depth i ans
              else Stream (y!zero) (next ! one) (next ! two)
        goodPair j i = 
            (i < l) &&
            (j < (2^
        incrMemo = 
            listArray (0,l) 
              [listArray (0,l) 
                 [incrStart incr start | start <- [0..l]] 
                   | incr <- [0..l]]
    in
      incrMemo

cyclePossiblyTrunc2' ans (Stream (_,Left (hd,_)) od ev) =
    Stream hd (cyclePossiblyTrunc2' od) (cyclePossiblyTrunc2' ev)
cyclePossiblyTrunc2' ans (Stream (n,Right s) _ _) = 
    let (_,y) = bounds s
        len = 1+y
    in
    s ! ((incrAt n)`mod`len) ! (n`mod`len)
-}


-- | Θ(n).
{-# INLINE scanl #-}
scanl :: (a -> b -> a) -> a -> Stream b -> Stream a
scanl f z = fromList . L.scanl f z . toList

-- | Θ(n).
{-# INLINE scanl1 #-}
scanl1 :: (a -> a -> a) -> Stream a -> Stream a
scanl1 f = fromList . L.scanl1 f . toList

-- | Θ(n).
unfoldr :: (c -> (a,c)) -> c -> Stream a
unfoldr f x = fmap fst $ iterate (idify f) (f x)
    where
      idify :: (c -> (a,c)) -> (a,c) -> (a,c)
      idify m (_,n) = m n


{- |

@Θ(n)@. Turns the first n items into a list. Returns the empty list if
@n<=0@.

-}
{-# INLINE take #-}
take :: Int -> Stream a -> [a]
take = genericTake

{-# INLINE genericTake #-}
genericTake :: (Integral x) => x -> Stream a -> [a]
genericTake (n+1) = L.genericTake (n+1) . toList
genericTake _ = const []

-- | See 'dropWithCons'.
{-# INLINE drop #-}
drop :: Int -> Stream a -> Stream a
drop = genericDrop

{-# INLINE genericDrop #-}
genericDrop :: (Integral x) => x -> Stream a -> Stream a
genericDrop n = fromList . listGenericDrop n . toList


-- The genericDrop in Data.List fails on negative inputs
listGenericDrop :: (Integral x) => x -> [a] -> [a]
listGenericDrop (n+1) (_:xs) = listGenericDrop n xs
listGenericDrop _ x = x


{-|

If you drop m items and inspect n items from the remaining stream,
'dropWithCons' takes

* Θ(lg (m-1+n) + lg (m-2+n) + . . . + lg n) time for the m calls to
  'tail' that construct the dropped list and advance to the head of
  the remaining list.

* no time to construct the remaining stream.

Doing so by turning it into a linear stream, then turning it back into
a RandomAccessStream, as in 'drop' takes

* Θ(m) time to construct the dropped list and advance to the head of
  the remaining stream.

* Θ(n) time to construct the remaining RandomAccessStream.

When n is much larger than m, 'dropWithCons' may be the faster
choice. If n and m are close, 'drop' might be faster.

-}
dropWithCons :: Int -> Stream a -> Stream a
dropWithCons = genericDropWithCons

genericDropWithCons :: (Integral x) => x -> Stream a -> Stream a
genericDropWithCons (n+1) s = genericDropWithCons n (tail s)
genericDropWithCons _ s = s

-- | See 'Data.List.splitAt' for functionality. For complexity, see
-- note at 'dropWithCons'.
splitAt :: Int -> Stream a -> ([a],Stream a)
splitAt = genericSplitAt

genericSplitAt :: (Integral x) => x -> Stream a -> ([a],Stream a)
genericSplitAt n s = 
    let (p,q) = listGenericSplitAt n $ toList s
    in (p,fromList q)

-- The genericSplitAt in Data.List errors on negative arguments
listGenericSplitAt :: Integral x => x -> [a] -> ([a],[a])
listGenericSplitAt (n+1) (x:xs) =
    let (y,z) = listGenericSplitAt n xs
    in (x:y,z)
listGenericSplitAt _ x = ([],x)

-- | See complexity note at 'dropWithCons'.
splitAtWithCons :: Int -> Stream a -> ([a],Stream a)
splitAtWithCons = genericSplitAtWithCons

genericSplitAtWithCons :: (Integral x) => x -> Stream a -> ([a],Stream a)
genericSplitAtWithCons (n+1) s =
    let (p,q) = genericSplitAtWithCons n (tail s)
    in ((head s) : p, q)
genericSplitAtWithCons _ s = ([],s)

-- | Θ(|result|).
takeWhile :: (a -> Bool) -> Stream a -> [a]
takeWhile f = L.takeWhile f. toList

-- | See 'Data.List.dropWhile' for functionality. For complexity, see
-- note at 'dropWithCons'.
dropWhile :: (a -> Bool) -> Stream a -> Stream a
dropWhile f = fromList . L.dropWhile f . toList

-- | See complexity note at 'dropWithCons'.
dropWhileWithCons :: (a -> Bool) -> Stream a -> Stream a
dropWhileWithCons f x = 
    let h = head x
        t = tail x
    in
      if (f h)
      then dropWhileWithCons f t
      else x

-- | See 'Data.List.span' for functionality. For complexity, see
-- note at 'dropWithCons'.
-- Note that inspecting the 'Stream' in the result will fail if the
-- predicate is 'True' on all items in the stream.
span :: (a -> Bool) -> Stream a -> ([a],Stream a)
span f x = 
    let (p,q) = L.span f $ toList x
    in
      (p,fromList q)

-- | See complexity note at 'dropWithCons'.
spanWithCons :: (a -> Bool) -> Stream a -> ([a],Stream a)
spanWithCons f x =
    if (f $ head x)
    then
        let (p,q) = spanWithCons f (tail x)
        in ((head x):p,q)
    else
        ([],x)

-- | See 'Data.List.break' for functionality. For complexity, see
-- note at 'dropWithCons'.
-- Note that inspecting the 'Stream' in the result will fail if the
-- predicate is 'False' on all items in the stream.
break :: (a -> Bool) -> Stream a -> ([a],Stream a)
break p = span (not . p)

-- | See complexity note at 'dropWithCons'.
breakWithCons :: (a -> Bool) -> Stream a -> ([a],Stream a)
breakWithCons p = spanWithCons (not . p)

-- | See 'Data.List.stripPrefix' for functionality. For complexity, see
-- note at 'dropWithCons'.
stripPrefix :: Eq a => [a] -> Stream a -> Maybe (Stream a)
stripPrefix x = fmap fromList . L.stripPrefix x . toList

-- | See complexity note at 'dropWithCons'.
stripPrefixWithCons :: Eq a => [a] -> Stream a -> Maybe (Stream a)
stripPrefixWithCons [] y = Just y
stripPrefixWithCons (x:xs) y = 
    if x == (head y)
    then stripPrefixWithCons xs (tail y)
    else Nothing

group :: (Eq a) => Stream a -> Stream [a]
group = groupBy (==)

groupSafe :: (Eq a) => Stream a -> Stream (a,[a])
groupSafe = groupBySafe (==)
            
groupBy :: (a -> a -> Bool) -> Stream a -> Stream [a]
groupBy f = fromList . L.groupBy f . toList

groupBySafe :: (a -> a -> Bool) -> Stream a -> Stream (a,[a])
groupBySafe f = fromList . listGroupBySafe f . toList

listGroupBySafe :: (a -> a -> Bool) -> [a] -> [(a,[a])]
listGroupBySafe _  [] =  []
listGroupBySafe eq (x:xs) =  (x,ys) : listGroupBySafe eq zs
    where (ys,zs) = L.span (eq x) xs

inits :: Stream a -> Stream [a]
inits = zipWith ($) (map take nats) . repeat

nats :: (Integral x) => Stream x
nats = iterate (+1) 0

tails :: Stream a -> Stream (Stream a)
tails = iterate tail

isPrefixOf :: Eq a => [a] -> Stream a -> Bool
isPrefixOf x = L.isPrefixOf x . toList

-- | Returns the first @b@ correspinding to an @a@ equal to the given
-- argument. If there is no such equal key, this function never returns.
lookup :: Eq a => a -> Stream (a,b) -> b
lookup x = fromJust . L.lookup x . toList

-- | Returns the first value in the 'Stream' for which the predicate
-- is 'True'. If there is no such value, this function never returns.
find :: (a -> Bool) -> Stream a -> a
find f = fromJust . L.find f. toList

-- | Returns only the values for which the predicate is true. There
-- must be an infinite number of these, or some inspectinos of the
-- result will not terminate.
filter :: (a -> Bool) -> Stream a -> Stream a
filter f x = fromList $ L.filter f $ toList x

partition :: (a -> Bool) -> Stream a -> (Stream a, Stream a)    
partition f = splitEither . fmap (\x -> if f x then Left x else Right x)

splitEither :: Stream (Either a b) -> (Stream a,Stream b)
splitEither x = 
    let (p,q) = listSplitEither $ toList x
    in
      (fromList p, fromList q)

listSplitEither (x:xs) =
    let (p,q) = listSplitEither xs
    in
      case x of
        Left y -> (y:p,q)
        Right z -> (p,z:q)

{- |
   
   @Θ(lg i)@. Find the element at index @i@. Calls error and shows @i@ if @i<0@.

-}
(!!) :: Stream a -> Int -> a
(!!) = genericIndex

listAppend x y = foldr (:) y x

genericIndex :: (Integral x) => Stream a -> x -> a
genericIndex x n =
    if n < 0
    then error $ listAppend "Streams have no values at negative indices like " (show $ toInteger n)
    else at x n
at ~(Stream h _ _) 0 = h
at ~(Stream _ q r) n = 
    case n `mod` 2 of
      0 -> at r (n `div` 2 - 1)
      1 -> at q ((n-1) `div` 2)

{- |

@Θ(lg i)@. Changes the value at position @i@ by applying function
@f@. If @i < 0@, does nothing.

-}
adjust :: (a -> a) -> Int -> Stream a -> Stream a
adjust = genericAdjust

genericAdjust :: (Integral x) => (a -> a) -> x -> Stream a -> Stream a
genericAdjust f 0 ~(Stream x od ev) = Stream (f x) od ev
genericAdjust f n ~v@(Stream x od ev) =
    case compare n 0 of
      LT -> v
      EQ -> Stream (f x) od ev
      GT -> case n `mod` 2 of
              0 -> genericAdjust f (n `div` 2 - 1) ev
              1 -> genericAdjust f ((n-1) `div` 2) od

elemIndex :: Eq a => a -> Stream a -> Int
elemIndex x = head . elemIndices x

elemIndices :: Eq a => a -> Stream a -> Stream Int
elemIndices x = findIndices (x ==)

findIndex :: (a -> Bool) -> Stream a -> Int
findIndex f = head . findIndices f

findIndices :: (a -> Bool) -> Stream a -> Stream Int
findIndices f = fromList . L.findIndices f . toList

-- | O(n). Inspection of the result will fails if the argument is not
-- infinite.
fromList :: [a] -> Stream a
fromList y = fmap L.head $ iterate L.tail y

{-
-- | Θ(n)
fromLinearStream :: S.Stream a -> Stream a
fromLinearStream y = fmap S.head $ iterate S.tail y
-}

zip :: Stream a -> Stream b -> Stream (a,b)
zip = zipWith (,)

unzip :: Stream (a,b) -> (Stream a, Stream b)
unzip ~(Stream (x,y) od ev) = 
    let ~(p,q) = unzip od
        ~(r,s) = unzip ev
    in
      (Stream x p r, Stream y q s)

zipWith :: (a -> b -> c) -> Stream a -> Stream b -> Stream c
zipWith f ~(Stream x y z) ~(Stream a b c) =
    Stream (f x a) (zipWith f y b)
                  (zipWith f z c)

zip3 :: Stream a -> Stream b -> Stream c -> Stream (a,b,c)
zip3 = zipWith3 (,,)

unzip3 :: Stream (a,b,c) -> (Stream a,Stream b,Stream c)
unzip3 ~(Stream (x,y,z) od ev) = 
    let ~(p,q,t) = unzip3 od
        ~(r,s,u) = unzip3 ev
    in
      (Stream x p r, Stream y q s, Stream z t u)

zipWith3 :: (a -> b -> c -> d) -> Stream a -> Stream b -> Stream c -> Stream d
zipWith3 f ~(Stream x xod xev)
           ~(Stream y yod yev)
           ~(Stream z zod zev) =
           Stream (f x y z) (zipWith3 f xod yod zod) (zipWith3 f xev yev zev)

zip4 :: Stream a -> Stream b -> Stream c -> Stream d -> Stream (a,b,c,d)
zip4 = zipWith4 (,,,)

unzip4 :: Stream (a,b,c,d) -> (Stream a,Stream b,Stream c,Stream d)
unzip4 ~(Stream (x,y,z,h) od ev) = 
    let ~(p,q,t,i) = unzip4 od
        ~(r,s,u,j) = unzip4 ev
    in
      (Stream x p r, Stream y q s, Stream z t u,Stream h i j)

zipWith4 :: (a -> b -> c -> d -> e) -> Stream a -> Stream b -> Stream c -> Stream d -> Stream e
zipWith4 f ~(Stream x xod xev)
           ~(Stream y yod yev)
           ~(Stream z zod zev) 
           ~(Stream p pod pev) =
           Stream (f x y z p) (zipWith4 f xod yod zod pod) (zipWith4 f xev yev zev pev)

zip5 ::  Stream a -> Stream b -> Stream c -> Stream d -> Stream e -> Stream (a,b,c,d,e)
zip5 = zipWith5 (,,,,)

unzip5 :: Stream (a,b,c,d,e) -> (Stream a,Stream b,Stream c,Stream d,Stream e)
unzip5 ~(Stream (x,y,z,h,k) od ev) = 
    let ~(p,q,t,i,l) = unzip5 od
        ~(r,s,u,j,m) = unzip5 ev
    in
      (Stream x p r, Stream y q s, Stream z t u,Stream h i j,Stream k l m)

zipWith5 :: (a -> b -> c -> d -> e -> f) -> 
            Stream a -> Stream b -> Stream c -> Stream d -> Stream e -> Stream f
zipWith5 f ~(Stream x xod xev)
           ~(Stream y yod yev)
           ~(Stream z zod zev) 
           ~(Stream p pod pev)
           ~(Stream q qod qev) =
           Stream (f x y z p q) 
             (zipWith5 f xod yod zod pod qod) 
             (zipWith5 f xev yev zev pev qev)

zip6 ::  Stream a -> Stream b -> Stream c -> Stream d -> Stream e -> Stream f -> Stream (a,b,c,d,e,f)
zip6 = zipWith6 (,,,,,)

unzip6 :: Stream (a,b,c,d,e,f) -> (Stream a,Stream b,Stream c,Stream d,Stream e,Stream f)
unzip6 ~(Stream (x,y,z,h,k,n) od ev) = 
    let ~(p,q,t,i,l,o) = unzip6 od
        ~(r,s,u,j,m,w) = unzip6 ev
    in
      (Stream x p r, Stream y q s, Stream z t u,Stream h i j,Stream k l m,Stream n o w)

zipWith6 :: (a -> b -> c -> d -> e -> f -> g) -> 
            Stream a -> Stream b -> Stream c -> Stream d -> Stream e -> Stream f -> Stream g
zipWith6 f ~(Stream x xod xev)
           ~(Stream y yod yev)
           ~(Stream z zod zev) 
           ~(Stream p pod pev)
           ~(Stream q qod qev)
           ~(Stream r rod rev) =
           Stream (f x y z p q r) 
             (zipWith6 f xod yod zod pod qod rod)
             (zipWith6 f xev yev zev pev qev rev)

zip7 ::  Stream a -> Stream b -> Stream c -> Stream d -> Stream e -> Stream f -> Stream g -> Stream (a,b,c,d,e,f,g)
zip7 = zipWith7 (,,,,,,)

unzip7 :: Stream (a,b,c,d,e,f,g) -> (Stream a,Stream b,Stream c,Stream d,Stream e,Stream f,Stream g)
unzip7 ~(Stream (x,y,z,h,k,n,v) od ev) = 
    let ~(p,q,t,i,l,o,vv) = unzip7 od
        ~(r,s,u,j,m,w,vvv) = unzip7 ev
    in
      (Stream x p r, Stream y q s, Stream z t u,Stream h i j,Stream k l m,Stream n o w,Stream v vv vvv)

zipWith7 :: (a -> b -> c -> d -> e -> f -> g -> h) -> 
            Stream a -> Stream b -> Stream c -> Stream d -> Stream e -> Stream f -> Stream g -> Stream h
zipWith7 f ~(Stream x xod xev)
           ~(Stream y yod yev)
           ~(Stream z zod zev) 
           ~(Stream p pod pev)
           ~(Stream q qod qev)
           ~(Stream r rod rev)
           ~(Stream s sod sev) =
           Stream (f x y z p q r s) 
             (zipWith7 f xod yod zod pod qod rod sod)
             (zipWith7 f xev yev zev pev qev rev sev)

lines :: Stream Char -> Stream [Char]
lines = fromList . L.lines . toList

words :: Stream Char -> Stream [Char]
words = fromList . L.words . toList

unlines :: Stream [Char] -> Stream Char
unlines = fromList . L.unlines. toList

unwords :: Stream [Char] -> Stream Char
unwords = fromList . L.unwords. toList

nub :: Eq a => Stream a -> Stream a 
nub = nubBy (==)

nubBy :: (a -> a -> Bool) -> Stream a -> Stream a
nubBy f = fromList . L.nubBy f . toList
{-
    let (y:ys) = toList x
    in
      fromList $ y : (L.nubBy f $ L.filter (not . f y) ys)
-}
delete :: Eq a => a -> Stream a -> Stream a
delete = deleteBy (==)

(\\) :: Eq a => Stream a -> [a] -> Stream a
(\\) = deleteFirstsBy (==)

-- | 'union' does not behave the same way as 'Data.List.union', by
-- necessity. 'union' eliminates all duplicatees, whether in the first
-- or second argument.
union :: Eq a => Stream a -> Stream a -> Stream a
union = unionBy (==)

-- | See comment on 'union'.
unionBy :: (a -> a -> Bool) -> Stream a -> Stream a -> Stream a
unionBy f x y = nubBy f (interleave x y)

intersect :: Eq a => Stream a -> Stream a -> Stream a
intersect = intersectBy (==)

insert :: Ord a => a -> Stream a -> Stream a
insert = insertBy compare

deleteBy :: (a -> a -> Bool) -> a -> Stream a -> Stream a
deleteBy f x = fromList . L.deleteBy f x . toList
    
deleteFirstsBy :: (a -> a -> Bool) -> Stream a -> [a] -> Stream a
deleteFirstsBy f x [] = x
deleteFirstsBy f x (y:ys) = deleteFirstsBy f (deleteBy f y x) ys

intersectBy :: (a -> a -> Bool) -> Stream a -> Stream a -> Stream a
intersectBy f x y = map fst $
                    filter (uncurry f) $ 
                    fromList $ 
                    flatten $ 
                    cartesianProduct (toList x) (toList y)

--cartesianProduct :: S.Stream a -> S.Stream a -> S.Stream (S.Stream (a,a))
cartesianProduct (x:xs) ys =
    (L.zip (L.repeat x) ys) : (cartesianProduct xs ys)

{-
streamConcat :: S.Stream [a] -> S.Stream a
streamConcat (S.Cons x xs) = foldr S.Cons (streamConcat xs) x
-}
--flatten :: S.Stream (S.Stream a) -> S.Stream a
flatten = L.concat . takeFrom 1
{-
streamGenericTake :: Integer -> S.Stream a -> [a]
streamGenericTake 0 _ = []
streamGenericTake (n+1) (S.Cons x xs) = x : (streamGenericTake n xs)

streamGenericDrop :: Integer -> S.Stream a -> S.Stream a
streamGenericDrop 0 x = x
streamGenericDrop (n+1) (S.Cons x xs) = streamGenericDrop n xs
-}
--takeFrom :: Integer -> S.Stream (S.Stream a) -> S.Stream [a]
takeFrom n x = (L.genericTake n (L.map L.head x)) :
               (takeFrom (n+1) $
                foldr (:) (L.genericDrop n x) $
                L.genericTake n $ 
                L.map L.tail x)

insertBy :: (a -> a -> Ordering) -> a -> Stream a -> Stream a
insertBy f x = fromList . L.insertBy f x . toList

-- | Given two unequal streams, returns their ordering.
compareUnequal :: Ord a => Stream a -> Stream a -> Ordering
compareUnequal x y = compare (toList x) (toList y)

{- |

Cuts a stream down to the given size by taking some limited number of
elements from that stream, then recursively cutting them down to
size. If @i<=0@, returns the empty list.

-}
upTo :: (Integral x) => x -> (x -> a -> b) -> Stream a -> [b]
upTo 0 _ _ = []
upTo (n+1) f x = upTo' (n+1) f (toList x)
upTo m _ _ = []

upTo' 0 _ _ = []
upTo' (n+1) f ~(x:xs) = (f n x):(upTo' n f xs)

{- |

Compares two streams up to the given depth. If the returned value is
'EQ', this does not indicate that the streams are equal, only that
they do not differ up to the given depth. If the returned value is
'LT' or 'GT', then the whole streams do, in fact, have that ordering.

-}
compareUpTo :: (Integral x, Ord a) => x -> Stream a -> Stream a -> Ordering
compareUpTo n x y = compare (upTo n (const id) x) 
                            (upTo n (const id) y)

-- | See 'compareUpTo'.
equalUpTo :: (Integral x, Ord a) => x -> Stream a -> Stream a -> Ordering
equalUpTo n x y = compare (upTo n (const id) x) 
                          (upTo n (const id) y)



--unsigned
-- cache quotRem calls
-- cost?
-- Cost: if n = 2^j * l, where l is odd, x/(2^j) thunks 
-- at first x nodes
{- | 

Returns every nth element. I'm not sure of the exact time complexity,
but it gets a speedup from every power of 2 that divides n. I suspect
the time complexity is Θ(e + r*m) where n is r * 2^e and m elements of
the result stream are forced.

-}
everyNth :: (Integral x) => x -> Stream a -> Stream a
everyNth n x = everyNth' n 0 x
--everyNth' :: Int -> Int -> Stream a -> Stream a
everyNth' 1 _ x = x
everyNth' n m ~y@(Stream x od ev) =
    let (qn,rn) = n `quotRem` 2
        (qm,rm) = m `quotRem` 2
    in
      case (rn,rm) of
        (0,0) -> 
            if qm == 0
            then cons x (everyNth' qn (qn-1) ev)
            else everyNth' qn (qm-1) ev
        (1,0) ->
            if qm == 0
            then Stream x (everyNth' n qn od) (everyNth' n (n-1) ev)
            else everyL n m y
                -- joinS (everyNth' n (qm-1) ev) (everyNth' n (qn+qm) od) 
        (0,1) -> everyNth' qn qm od
        (1,1) -> everyL n m y
                -- joinS (everyNth' n qm od) (everyNth' n (qn+qm) ev) 

everyL n m = fromList . everyL' n m . toList
everyL' n 0 (x:xs) = x : (everyL' n (n-1) xs)
everyL' n (m+1) (_:xs) = everyL' n m xs

{- | 

Extracts a list from a random access stream. For some constant @c@,
places no more than @c@ thunks at each node in the result.

-}
toList :: Stream a -> [a]
toList t = toList' [t]
toList' x = 
    let heads = L.map head x
        (ods,evs) = breakParity x in
    heads `listAppend` toList' (ods `listAppend` evs)

pairup (Stream _ od ev) = (od,ev)
breakParity = L.unzip . L.map pairup

{- | 

Extracts a linear stream from a random access stream. For some
constant @c@, places no more than @c@ thunks at each node in the
result.

-}
{-
toLinearStream :: Stream a -> S.Stream a
toLinearStream t = toLinearStream' [t]
toLinearStream' x = 
    let heads = L.map head x
        (ods,evs) = breakParity x in
    L.foldr S.Cons (toLinearStream' (ods `listAppend` evs)) heads
-}
interleaveL [] x = x
interleaveL x [] = x
interleaveL (x:xs) (y:ys) = x : y : interleaveL xs ys
{-
memoize :: ((Integer -> a) -> Integer -> a) -> Stream a
memoize f = 
    let x = Stream (f (x !!) 0)
                  (memoize (\g y -> f (at x) (2*y+1)))
                  (memoize (\g y -> f (at x) (2*(y+1))))
    in x
-}


-- cycle first, for safety?
-- unfold version
-- require one element

instance Applicative Stream where
    pure x = repeat x
    x <*> y = zipWith ($) x y

instance Arbitrary a => Arbitrary (Stream a) where
    arbitrary = 
        do
          h <- arbitrary
          od <- arbitrary
          ev <- arbitrary
          return $ Stream h od ev
    coarbitrary x v =
        do
          n <- (arbitrary :: Gen Int)
          coarbitrary (take (abs n) x) v
