{-# LANGUAGE DataKinds #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeFamilies #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE UndecidableInstances #-}

module Exercises where

import Data.Kind (Constraint, Type)

-- | Before we get started, let's talk about the @TypeOperators@ extension. All
-- this does is allow us to write types whose names are operators, and write
-- regular names as infix names with the backticks, as we would at the value
-- level.

{- ONE -}

data Nat = Z | S Nat

-- | a. Use the @TypeOperators@ extension to rewrite the 'Add' family with the
-- name '+':
type family (x :: Nat) + (y :: Nat) :: Nat where
  'Z + y = y
  ('S n) + y = 'S (n + y)

-- | b. Write a type family '**' that multiplies two naturals using '(+)'. Which
-- extension are you being told to enable? Why?
type family (x :: Nat) ** (y :: Nat) :: Nat where
  'Z ** _ = 'Z
  ('S n) ** y = y + (n ** y)

data SNat (value :: Nat) where
  SZ :: SNat 'Z
  SS :: SNat n -> SNat ('S n)

-- | c. Write a function to add two 'SNat' values.
addSNat :: SNat a -> SNat b -> SNat (a + b)
addSNat SZ x = x
addSNat (SS x) y = SS (addSNat x y)

{- TWO -}

data Vector (count :: Nat) (a :: Type) where
  VNil :: Vector 'Z a
  VCons :: a -> Vector n a -> Vector ('S n) a

-- | a. Write a function that appends two vectors together. What would the size
-- of the result be?
appendVs :: Vector x a -> Vector y a -> Vector (x + y) a
appendVs VNil x = x
appendVs (VCons h t) xs = VCons h (appendVs t xs)

-- | b. Write a 'flatMap' function that takes a @Vector n a@, and a function
-- @a -> Vector m b@, and produces a list that is the concatenation of these
-- results. This could end up being a deceptively big job.
flatMap :: Vector n a -> (a -> Vector m b) -> Vector (n ** m) b
flatMap VNil _ = VNil
flatMap (VCons h t) k = appendVs (k h) (flatMap t k)

{- THREE -}

-- | a. More boolean fun! Write the type-level @&&@ function for booleans.
type family (x :: Bool) && (y :: Bool) :: Bool where
  'False && _ = 'False
  'True && y = y

-- | b. Write the type-level @||@ function for booleans.
type family (x :: Bool) || (y :: Bool) :: Bool where
  'True || _ = 'True
  'False || y = y

-- | c. Write an 'All' function that returns @'True@ if all the values in a
-- type-level list of boleans are @'True@.
type family All (xs :: [Bool]) :: Bool where
  All '[] = 'True
  All (x ': xs) = x && All xs

{- FOUR -}

-- | a. Nat fun! Write a type-level 'compare' function using the promoted
-- 'Ordering' type.
type family Compare (x :: Nat) (y :: Nat) :: Ordering where
  Compare 'Z 'Z = 'EQ
  Compare 'Z ('S y) = 'LT
  Compare ('S x) 'Z = 'GT
  Compare ('S x) ('S y) = Compare x y

-- | b. Write a 'Max' family to get the maximum of two natural numbers.
type family Max (x :: Nat) (y :: Nat) :: Nat where
  Max x y = Max' (Compare x y) x y

type family Max' (o :: Ordering) (x :: Nat) (y :: Nat) :: Nat where
  Max' 'GT x _ = x
  Max' _ _ y = y

-- | c. Write a family to get the maximum natural in a list.
type family Maximum (xs :: [Nat]) :: Nat where
  Maximum '[] = 'Z
  Maximum (x ': xs) = Max x (Maximum xs)

{- FIVE -}

data Tree = Empty | Node Tree Nat Tree

-- | Write a type family to insert a promoted 'Nat' into a promoted 'Tree'.
type family Insert (x :: Nat) (t :: Tree) :: Tree where
  Insert x 'Empty = 'Node 'Empty x 'Empty
  Insert x ('Node l c r) = Insert' (Compare x c) x (Node l c r)

type family Insert' (o :: Ordering) (x :: Nat) (t :: Tree) :: Tree where
  Insert' 'LT x ('Node l c r) = 'Node (Insert x l) c r
  Insert' 'GT x ('Node l c r) = 'Node l c (Insert x r)
  Insert' 'EQ _ t = t

{- SIX -}

-- | Write a type family to /delete/ a promoted 'Nat' from a promoted 'Tree'.
type family Delete (x :: Nat) (t :: Tree) :: Tree where
  Delete _ 'Empty = 'Empty
  Delete x ('Node l c r) = Delete' (Compare x c) x ('Node l c r)

type family Delete' (o :: Ordering) (x :: Nat) (t :: Tree) :: Tree where
  Delete' 'EQ _ ('Node l c r) = 'Node Empty c r
  Delete' 'LT x ('Node l c r) = 'Node (Delete x l) c r
  Delete' 'GT x ('Node l c r) = 'Node l c (Delete x r)

{- SEVEN -}

-- | With @TypeOperators@, we can use regular Haskell list syntax on the
-- type-level, which I think is /much/ tidier than anything we could define.
data HList (xs :: [Type]) where
  HNil :: HList '[]
  HCons :: x -> HList xs -> HList (x ': xs)

-- | Write a function that appends two 'HList's.
type family (xs :: [Type]) ++ (ys :: [Type]) :: [Type] where
  '[] ++ ys = ys
  (x ': xs) ++ ys = x ': (xs ++ ys)

appendHList :: HList a -> HList b -> HList (a ++ b)
appendHList HNil ys = ys
appendHList (HCons x xs) ys = HCons x (appendHList xs ys)

{- EIGHT -}

-- | Type families can also be used to build up constraints. There are, at this
-- point, a couple things that are worth mentioning about constraints:
--
-- - As we saw before, '()' is the empty constraint, which simply has "no
--   effect", and is trivially solved.
--
-- - Unlike tuples, constraints are "auto-flattened": ((a, b), (c, (d, ())) is
--   exactly equivalent to (a, b, c, d). Thanks to this property, we can build
--   up constraints using type families!
type family CAppend (x :: Constraint) (y :: Constraint) :: Constraint where
  CAppend x y = (x, y)

-- | a. Write a family that takes a constraint constructor, and a type-level
-- list of types, and builds a constraint on all the types.
type family Every (c :: Type -> Constraint) (x :: [Type]) :: Constraint where
  Every _ '[] = ()
  Every c (x ': xs) = (c x, Every c xs)

-- | b. Write a 'Show' instance for 'HList' that requires a 'Show' instance for
-- every type in the list.
instance Every Show xs => Show (HList xs) where
  show HNil = "[]"
  show (HCons h t) = show h <> ":" <> show t

-- | c. Write an 'Eq' instance for 'HList'. Then, write an 'Ord' instance.
-- Was this expected behaviour? Why did we need the constraints?
instance Every Eq xs => Eq (HList xs) where
  HNil == HNil = True
  HCons x xs == HCons y ys = x == y && xs == ys

instance (Every Eq xs, Every Ord xs) => Ord (HList xs) where
  compare (HCons x xs) (HCons y ys) = compare x y <> compare xs ys
  compare _ _ = EQ

{- NINE -}

-- | a. Write a type family to calculate all natural numbers up to a given
-- input natural.
type family Uncons (x :: Nat) (xs :: [Nat]) :: [Nat] where
  Uncons x '[] = '[x]
  Uncons x (y ': ys) = y ': Uncons x ys

type family UpTo (x :: Nat) :: [Nat] where
  UpTo 'Z = '[ 'Z]
  UpTo ('S n) = Uncons n (UpTo n)

-- | b. Write a type-level prime number sieve.
-- I'm not clever enough.

-- | c. Why is this such hard work?
-- We don't have same features for value-level programming, like binding,
-- pattern matching, higher-order functions...
