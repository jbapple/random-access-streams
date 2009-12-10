data BS a = BS a (BS a) (BS a)

bbcons x y =
  BS x
     (case y of
        BS h _ e -> bbcons h e)
     (case y of
        BS _ o _ -> o)

bscons x ~(BS h o e) = BS x (bscons h e) o

eyes :: BS Char
eyes = bscons 'i' eyes

smallEyes :: BS Char
smallEyes = 
  let ans = BS 'i' ans ans 
  in ans

data Node a = N2 a a
            | N3 a a a
data Digit a = D1 a
             | D2 a a
             | D3 a a a
             | D4 a a a a
data TTT a = TTT (Digit a) (TTT (Node a))

cons :: a -> TTT a -> TTT a
cons p (TTT (D1 q)       ds) = TTT (D2 p q) ds
cons p (TTT (D2 q r)     ds) = TTT (D3 p q r) ds
cons p (TTT (D3 q r s)   ds) = TTT (D4 p q r s) ds
cons p (TTT (D4 q r s t) ds) = TTT (D2 p q) (cons (N3 r s t) ds)

dangerousBees :: TTT Char
dangerousBees = cons 'b' dangerousBees

stream :: a -> TTT a
stream x = TTT (D2 x x) (stream (N2 x x))

bees :: TTT Char
bees = stream 'b'

data Tree a = Leaf a
            | Node a (Tree a) (Tree a) 
              deriving (Show)
type RAL a = [(Int,Tree a)]

scons :: a -> RAL a -> RAL a
scons x xs@((size1,t1) : (size2,t2) : rest) =
    if size1 == size2
    then (1 + size1 + size2, Node x t1 t2) : rest
    else (1,Leaf x) : xs
scons x xs = (1,Leaf x) : xs

sbees :: RAL Char
sbees = (1,Leaf 'b') : fmap (more 'b') sbees
    where 
      more :: a -> (Int,Tree a) -> (Int,Tree a)
      more v (n,t) = (1 + 2*n, Node v t t)

badbees :: RAL Char
badbees = scons 'b' badbees

data B3 a = Nil
          | One a
          | B3 a a (B3 a) (B3 a) (B3 a)

b3cons :: a -> B3 a -> B3 a
b3cons x Nil = One x
b3cons x (One y) = B3 x y Nil Nil Nil
b3cons x (B3 y z zero one two) = B3 x y (b3cons z two) zero one

data Braun a = Braun a (Braun a) (Braun a)

bcons x ~(Braun h o e) =
    Braun x (bcons h e) o

bhead  (Braun h _ _) = h
bodds  (Braun _ o _) = o
bevens (Braun _ _ e) = e