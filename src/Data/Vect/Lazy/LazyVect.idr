module Data.Vect.Lazy.LazyVect

import Data.Vect
import Data.Zippable


%default total


data LazyVect : (n : Nat) -> a -> Type where
  Nil : LazyVect 0 a
  (::) : (x : a) -> (Lazy (LazyVect n a)) -> LazyVect (S n) a

%name LazyVect xs


(++) : LazyVect n a -> Lazy (LazyVect m a) -> LazyVect (n + m) a
(++) [] y = y
(++) (x :: z) y = x :: Delay (z ++ y)


Functor (LazyVect n) where
  map f [] = []
  map f (x :: y) = f x :: Delay (map f y)

{-
Applicative (LazyVect n) where
  pure = replicate n
  (<*>) fs xs = ?hole -}


Foldable (LazyVect n) where
  foldr f a [] = a
  foldr f a (x :: xs) = f x (foldr f a xs)

  foldl f a [] = a
  foldl f a (x :: xs) = foldl f (f a x) xs

  null [] = True
  null (x :: xs) = False

  toList [] = []
  toList (x :: xs) = x :: toList xs

zipWith : {c : Type} -> (LazyVect n a -> LazyVect n b -> LazyVect n c) -> LazyVect n a -> LazyVect n b -> LazyVect n c
zipWith _ [] [] = []
zipWith f (x :: xs) (y :: ys) = the (LazyVect n c) ((f x y) :: zipWith f ?hole ?hole2) -- (f x y) :: ?hole-- (Delay $ zipWith f xs ys)

-- TODO: issue for let with Delay (cannot write let = Delay () in ...)

{-
Zippable (LazyVect n) where
  zipWith : (LazyVect n a -> LazyVect n b -> LazyVect n c) -> LazyVect n a -> LazyVect n b -> LazyVect n c
  zipWith _ [] [] = []
  zipWith f (x :: xs) (y :: ys) = (f x y) :: zipWith f xs ys

  zip : LazyVect n a -> LazyVect n b -> LazyVect n (a, b)
  zipWith3 : (a -> b -> c -> d) -> LazyVect n a -> LazyVect n b -> LazyVect n c -> LazyVect n d
  zipWith3 _ [] [] [] = []
  zipWith3 f (x :: xs) (y :: ys) (z :: zs) = (f x y z) :: zipWith3 f xs ys zs

  zip3 : LazyVect n a -> LazyVect n b -> LazyVect n c -> LazyVect n (a, b, c)

  unzipWith : (a -> (b, c)) -> LazyVect n a -> (LazyVect n b, LazyVect n c)
  unzipWith _ [] = ([], [])
  unzipWith f (x :: xs) = let (y, z) = f x; (ys, zs) = unzipWith f xs in (y :: ys, z :: zs)

  unzip3 : LazyVect n (a, b, c) -> (LazyVect n a, LazyVect n b, LazyVect n c)

  unzipWith3 : (a -> (b, c, d)) -> LazyVect n a -> (LazyVect n b, LazyVect n c, LazyVect n d)
  unzipWith3 _ [] = ([], [], [])
  unzipWith3 f (x :: xs) = let (y, z, w) = f x; (ys, zs, ws) = unzipWith3 f xs in (y :: ys, z :: zs, w :: ws)
  {-
  zipWith _ [] [] = []
  zipWith f (x :: xs) (y :: ys) = (f x y) :: zipWith f xs ys

  zip = zipWith (\x, y => (x, y))

  zipWith3 _ [] [] [] = []
  zipWith3 f (x :: xs) (y :: ys) (z :: zs) = (f x y z) :: zipWith3 f xs ys zs

  zip3 = zipWith3 $ \x, y, z => (x, y, z)

  unzipWith _ [] = ([], [])
  unzipWith f (x :: xs) = let (y, z) = f x
                              (ys, zs) = unzipWith f xs in (y :: ys, z :: zs)

  unzip = unzipWith $ \(x, y) => (x, y)

  unzipWith3 _ [] = ([], [], [])
  unzipWith3 f (x :: xs) = let (y, z, w) = f x
                               (ys, zs, ws) = unzipWith3 f xs in (y :: ys, z :: zs, w :: ws)

  unzip3 = unzipWith3 $ \(x, y, z) => (x, y, z) -}

fromVect : Vect n a -> LazyVect n a
fromVect [] = []
fromVect (x :: xs) = x :: Delay (fromVect xs)

fromList : (xs : List a) -> LazyVect (length xs) a
fromList [] = []
fromList (x :: xs) = x :: Delay (fromList xs)

