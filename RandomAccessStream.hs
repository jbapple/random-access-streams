{-# OPTIONS -fglasgow-exts -fbang-patterns #-}

{- | 

Using traditional, linear streams, definind in "Data.Stream" as

> Stream a = Cons a (Stream a)

requires O(n) time to access the nth element. This module offers
"Data.RandomAccessStream".'Stream', taking O(lg n) time to access the nth
element, but O(lg n) time to perform a 'cons'.

Of course, streams are infinite, so it is not clear what it means to
take O(f(n)) time to perform an operation at the head of the
stream. We can instead give the cost of an operation as the number and
location of new thunks introduced.

For instance, the cons operation on simple lists:

> cons x xs = x:xs

puts one thunk between the 0th element and the rest of the list.

On the other hand, the 'cons' operation for random access streams puts
one thunk before each element at position 2^i-1. If x is a
random access stream with no thunks in the first 2^i-1 elements,
traversing them (using 'fromList', for instance) takes O(2^i-1)
time. If, before traversing these elements, we call 'cons', the
traversal takes O(2^i-1/+i/) time. This is longer than the time taken
if we were to have used a linear steam: O(2^i).

On the other hand, looking up or modifying the element at location i
takes only O(lg i) time. These operations take O(i) time on a
traditional linear stream.

-}

module Data.RandomAccessStream 
    (Stream
     -- * Basic Functions
    ,cons
    ,head
    ,tail
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
    -- ** Scans
    ,scanl
    ,scanl1
    -- ** Unfolding
    ,unfold
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
    ,fromLinearStream
    ,toLinearStream
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

     ,FiniteStream(..)
     ,toStream
     ,(++)
    )
where

import Prelude hiding (head, tail, map, scanl, scanl1, iterate, take,
  drop, takeWhile, dropWhile, repeat, cycle, filter, (!!), zip, unzip,
  unzip3, zipWith, words, unwords, lines, unlines, break, span,
  splitAt, zipWith3, zip3, concat, concatMap, lookup, (++))

import qualified Data.Stream as S
import Control.Applicative
import qualified Data.List as L
import Maybe
import Data.Typeable
import Data.Generics.Basics
import Test.QuickCheck
import Test.LazySmallCheck hiding (cons)
--import qualified LazySmallCheck as T
--import Test.SmallCheck
import Control.Exception
import System.IO.Unsafe

-- TODO: actual QC properties. Small check, too?

-- TODO: zipper

data Stream a = Stream a (Stream a) (Stream a) 
   deriving (Data,Typeable) --,Show)

(++) :: [a] -> Stream a -> Stream a
x ++ y = foldr cons y x

data FiniteStream a = FiniteStream a [a] deriving (Show)

toStream :: FiniteStream a -> Stream a
toStream (FiniteStream x y) = cycle (x:y)

instance Functor FiniteStream where
    fmap f (FiniteStream x y) = FiniteStream (f x) (fmap f y)

instance Arbitrary a => Arbitrary (FiniteStream a) where
    arbitrary = 
        do
          x <- arbitrary
          y <- arbitrary
          return $ FiniteStream x y
    coarbitrary (FiniteStream x y) = coarbitrary x . coarbitrary y

instance Functor Stream where
    fmap f ~(Stream p q r) = Stream (f p) (fmap f q) (fmap f r)

instance Monad Stream where
    return a = repeat a
    x >>= f =
        jn $ fmap f x
        where
          jn ~(Stream p q r) = 
              Stream (hd p) (q >>= od) (r >>= ev)
          hd ~(Stream h _ _) = h
          od ~(Stream _ o _) = o
          ev ~(Stream _ _ e) = e

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

{-
data Tree a = Tree a (Maybe (Tree a)) (Maybe (Tree a)) deriving (Show)

unperform :: Maybe (Tree a) -> Stream a
unperform Nothing = error "\0sdfsd" --throw $ ErrorCall "nothing" --error "nothing"
unperform (Just (Tree h od ev)) = 
    Stream h (unperform od) (unperform ev)

perform :: Stream a -> Maybe (Tree a)
perform x = unsafePerformIO $ 
    do
      y <- try (evaluate x)
      case y of
        Right (Stream h od ev) ->
            return $ Just $ Tree h (perform od) (perform ev)
        Left _ -> return Nothing
{-
        Left (ErrorCall ('\0':p)) -> return $ Nothing
        Left e -> throw e
-}
-}
{-
instance Show a => Show (Stream a) where
    show = show . perform
-}
{-
instance Show a => Show (Stream a) where
    show x =
        unsafePerformIO
answer :: a -> (a -> IO b) -> (Pos -> IO b) -> IO b
answer a known unknown =
  do res <- try (evaluate a)
     case res of
       Right b -> known b
       Left (ErrorCall ('\0':p)) -> unknown (map fromEnum p)
       Left e -> throw e
-}
instance Serial a => Serial (FiniteStream a) where
    series = cons2 FiniteStream

{-
instance Serial a => Serial (Stream a) where
    series = cons3 Stream -- \/ T.cons (error "nil")
-}
{-
instance Serial a => Serial (Tree a) where
    series = cons3 Tree
-}
-- | O(lg n). Adds an element onto the head of the 'Stream'. If the
-- first n elements of a stream x are already forced, traversing the
-- first n elements of (cons y x) takes O(n + lg n) time. The new
-- thinks are just before the elements at positions 2^i-1, counting
-- from 0.
cons :: a -> Stream a -> Stream a
cons x ~(Stream p q r) = Stream x (cons p r) q

-- | O(lg n). Removes an element from the head of the 'Stream'. If the
-- first n+1 elements of a stream x are already forced, traversing the
-- first n elements of (tail x) takes O(n + lg n) time. The new
-- thinks are just before the elements at positions 2^i-2, counting
-- from 0.
tail :: Stream a -> Stream a
tail ~(Stream _ q r) = Stream (head q) r (tail q)

-- | O(1). The first element in a stream.
head :: Stream a -> a
head ~(Stream p _ _) = p

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
O(lg n) thunks placed at positions 2^i-4. @interleave x y@
creates a stream that alternates between the values in x and y,
starting with x.

> interleave (fromList [0,2 ..]) (fromList [1,3 ..]) == fromList [0..]

-}
interleave :: Stream a -> Stream a -> Stream a
interleave x y = Stream (head x) y (tail x)

{- |

O(|result|) thunks, O(1) at each element of the result. @intercalate x
y@ concatenates the elements of y, using x as glue. Every place where
two lists form y are joined, x in inserted.

-}
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

{- | O(n), with O(n) calls to the passed function.
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
repeat x = let y = repeat x in Stream x y y


-- This could be faster. for instance, cycle [0,1] is Stream 0 (repeat 1) (repeat 0)
-- Is that really faster? Repeat still puts thinks everywhere
-- | O(n).
cycle :: [a] -> Stream a
cycle = fromList . L.cycle

-- | O(n).
scanl :: (a -> b -> a) -> a -> Stream b -> Stream a
scanl f z = fromList . L.scanl f z . toList

-- | O(n).
scanl1 :: (a -> a -> a) -> Stream a -> Stream a
scanl1 f = fromList . L.scanl1 f . toList

-- | O(n).
unfold :: (c -> (a,c)) -> c -> Stream a
unfold f x = fmap fst $ iterate (idify f) (f x)
    where
      idify :: (c -> (a,c)) -> (a,c) -> (a,c)
      idify m (_,n) = m n


{- |

@O(n)@. Turns the first n items into a list. Returns the empty list if
@n<=0@.

-}
take :: Int -> Stream a -> [a]
take = genericTake

genericTake :: (Integral x) => x -> Stream a -> [a]
genericTake (n+1) x = L.genericTake (n+1) (toList x)
genericTake _ _ = []

-- | See 'dropWithCons'.
drop :: Int -> Stream a -> Stream a
drop = genericDrop

genericDrop :: (Integral x) => x -> Stream a -> Stream a
genericDrop n = fromList . listGenericDrop n . toList


-- The genericDrop in Data.List fails on negative inputs
listGenericDrop :: (Integral x) => x -> [a] -> [a]
listGenericDrop (n+1) (_:xs) = listGenericDrop n xs
listGenericDrop _ x = x


{-|

If you drop m items and inspect n items from the remaining stream,
'dropWithCons' takes

* O(lg (m-1+n) + lg (m-2+n) + . . . + lg n) time for the m calls to
  'tail' that construct the dropped list and advance to the head of
  the remaining list.

* no time to construct the remaining stream.

Doing so by turning it into a linear stream, then turning it back into
a RandomAccessStream, as in 'drop' takes

* O(m) time to construct the dropped list and advance to the head of
  the remaining stream.

* O(n) time to construct the remaining RandomAccessStream.

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
genericSplitAtWithCons 0 s = ([],s)
genericSplitAtWithCons (n+1) s =
    let (p,q) = genericSplitAtWithCons n (tail s)
    in ((head s) : p, q)

-- | O(|result|).
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
            
groupBy :: (a -> a -> Bool) -> Stream a -> Stream [a]
groupBy f = fromList . L.groupBy f . toList

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
   
   @O(lg i)@. Find the element at index @i@. Calls error and shows @i@ if @i<0@.

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

@O(lg i)@. Changes the value at position @i@ by applying function
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

-- | O(n)
fromLinearStream :: S.Stream a -> Stream a
fromLinearStream y = fmap S.head $ iterate S.tail y

zip :: Stream a -> Stream b -> Stream (a,b)
zip = zipWith (,)

zip3 :: Stream a -> Stream b -> Stream c -> Stream (a,b,c)
zip3 = zipWith3 (,,)

zip4 :: Stream a -> Stream b -> Stream c -> Stream d -> Stream (a,b,c,d)
zip4 = zipWith4 (,,,)

zip5 ::  Stream a -> Stream b -> Stream c -> Stream d -> Stream e -> Stream (a,b,c,d,e)
zip5 = zipWith5 (,,,,)

zip6 ::  Stream a -> Stream b -> Stream c -> Stream d -> Stream e -> Stream f -> Stream (a,b,c,d,e,f)
zip6 = zipWith6 (,,,,,)

zip7 ::  Stream a -> Stream b -> Stream c -> Stream d -> Stream e -> Stream f -> Stream g -> Stream (a,b,c,d,e,f,g)
zip7 = zipWith7 (,,,,,,)

zipWith :: (a -> b -> c) -> Stream a -> Stream b -> Stream c
zipWith f ~(Stream x y z) ~(Stream a b c) =
    Stream (f x a) (zipWith f y b)
                  (zipWith f z c)

zipWith3 :: (a -> b -> c -> d) -> Stream a -> Stream b -> Stream c -> Stream d
zipWith3 f ~(Stream x xod xev)
           ~(Stream y yod yev)
           ~(Stream z zod zev) =
           Stream (f x y z) (zipWith3 f xod yod zod) (zipWith3 f xev yev zev)

zipWith4 :: (a -> b -> c -> d -> e) -> Stream a -> Stream b -> Stream c -> Stream d -> Stream e
zipWith4 f ~(Stream x xod xev)
           ~(Stream y yod yev)
           ~(Stream z zod zev) 
           ~(Stream p pod pev) =
           Stream (f x y z p) (zipWith4 f xod yod zod pod) (zipWith4 f xev yev zev pev)

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

{- 

Turns a list of pairs into a pair of lists.

-}
unzip :: Stream (a,b) -> (Stream a, Stream b)
unzip ~(Stream (x,y) od ev) = 
    let ~(p,q) = unzip od
        ~(r,s) = unzip ev
    in
      (Stream x p r, Stream y q s)

unzip3 :: Stream (a,b,c) -> (Stream a,Stream b,Stream c)
unzip3 ~(Stream (x,y,z) od ev) = 
    let ~(p,q,t) = unzip3 od
        ~(r,s,u) = unzip3 ev
    in
      (Stream x p r, Stream y q s, Stream z t u)

unzip4 :: Stream (a,b,c,d) -> (Stream a,Stream b,Stream c,Stream d)
unzip4 ~(Stream (x,y,z,h) od ev) = 
    let ~(p,q,t,i) = unzip4 od
        ~(r,s,u,j) = unzip4 ev
    in
      (Stream x p r, Stream y q s, Stream z t u,Stream h i j)

unzip5 :: Stream (a,b,c,d,e) -> (Stream a,Stream b,Stream c,Stream d,Stream e)
unzip5 ~(Stream (x,y,z,h,k) od ev) = 
    let ~(p,q,t,i,l) = unzip5 od
        ~(r,s,u,j,m) = unzip5 ev
    in
      (Stream x p r, Stream y q s, Stream z t u,Stream h i j,Stream k l m)

unzip6 :: Stream (a,b,c,d,e,f) -> (Stream a,Stream b,Stream c,Stream d,Stream e,Stream f)
unzip6 ~(Stream (x,y,z,h,k,n) od ev) = 
    let ~(p,q,t,i,l,o) = unzip6 od
        ~(r,s,u,j,m,w) = unzip6 ev
    in
      (Stream x p r, Stream y q s, Stream z t u,Stream h i j,Stream k l m,Stream n o w)

unzip7 :: Stream (a,b,c,d,e,f,g) -> (Stream a,Stream b,Stream c,Stream d,Stream e,Stream f,Stream g)
unzip7 ~(Stream (x,y,z,h,k,n,v) od ev) = 
    let ~(p,q,t,i,l,o,vv) = unzip7 od
        ~(r,s,u,j,m,w,vvv) = unzip7 ev
    in
      (Stream x p r, Stream y q s, Stream z t u,Stream h i j,Stream k l m,Stream n o w,Stream v vv vvv)

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
                    fromLinearStream $ 
                    flatten $ 
                    cartesianProduct (toLinearStream x) (toLinearStream y)

cartesianProduct :: S.Stream a -> S.Stream a -> S.Stream (S.Stream (a,a))
cartesianProduct (S.Cons x xs) ys =
    S.Cons (S.zip (S.repeat x) ys) $
     cartesianProduct xs ys

streamConcat :: S.Stream [a] -> S.Stream a
streamConcat (S.Cons x xs) = foldr S.Cons (streamConcat xs) x

flatten :: S.Stream (S.Stream a) -> S.Stream a
flatten = streamConcat . takeFrom 1

streamGenericTake :: Integer -> S.Stream a -> [a]
streamGenericTake 0 _ = []
streamGenericTake (n+1) (S.Cons x xs) = x : (streamGenericTake n xs)

streamGenericDrop :: Integer -> S.Stream a -> S.Stream a
streamGenericDrop 0 x = x
streamGenericDrop (n+1) (S.Cons x xs) = streamGenericDrop n xs

takeFrom :: Integer -> S.Stream (S.Stream a) -> S.Stream [a]
takeFrom n x = S.Cons (streamGenericTake n (S.map S.head x)) $ 
               takeFrom (n+1) $
               foldr S.Cons (streamGenericDrop n x) $
               streamGenericTake n $ 
               S.map S.tail x

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
upTo (n+1) f x = upTo' (n+1) f (toLinearStream x)
upTo m _ _ = []

upTo' 0 _ _ = []
upTo' (n+1) f ~(S.Cons x xs) = (f n x):(upTo' n f xs)

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
the time complexity is O(e + r*m) where n is r * 2^e and m elements of
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
toLinearStream :: Stream a -> S.Stream a
toLinearStream t = toLinearStream' [t]
toLinearStream' x = 
    let heads = L.map head x
        (ods,evs) = breakParity x in
    L.foldr S.Cons (toLinearStream' (ods `listAppend` evs)) heads

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
