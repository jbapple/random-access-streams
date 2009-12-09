data Tree a = Leaf a
            | Node a (Tree a) (Tree a) 
              deriving (Show)
type RAL a = [(Int,Tree a)]

cons :: a -> RAL a -> RAL a
cons x xs@((size1,t1) : (size2,t2) : rest) =
    if size1 == size2
    then (1 + size1 + size2, Node x t1 t2) : rest
    else (1,Leaf x) : xs
cons x xs = (1,Leaf x) : xs

bees :: RAL Char
bees = (1,Leaf 'b') : fmap (more 'b') bees
    where 
      more :: a -> (Int,Tree a) -> (Int,Tree a)
      more v (n,t) = (1 + 2*n, Node v t t)

badbees :: RAL Char
badbees = cons 'b' badbees

data B3 a = Nil
          | One a
          | B3 a a (B3 a) (B3 a) (B3 a)

b3cons :: a -> B3 a -> B3 a
b3cons x Nil = One x
b3cons x (One y) = B3 x y Nil Nil Nil
b3cons x (B3 y z zero one two) = B3 x y (b3cons z two) zero one