module TypeTrans.Array 

-- Module to represent Vector types, we use
-- Array as it's not already a taken construct
-- in the Idris prelude

import Data.Vect


-- A Shape is a Vector which represents the structure
-- of an Array e.g. the shape of [[1,2,3],[1,2,3]] would be [2,3]
Shape : Nat -> Type
Shape n = Vect n Nat

-- Rank represents the number of dimensions in an
-- Array, e.g. the rank of [[]] would be 2
Rank : Type
Rank = Nat

-- Vector with description of its dimensions in the Type
Array : Shape n -> Type -> Type
Array Nil t = t
Array (v::vs) t = Vect v (Array vs t) 


-- Give number of dimensions in the given Array
dim : Array xs t -> Nat
dim arr {xs} = length xs

-- Given a Vector returns the number of items
-- in the vector
length' : Vect n t -> Nat
length' v {n} = n 

-- Give the shape of a given array
shape : Array xs t -> Shape (length' xs) 
shape arr {xs} = xs


-- Gives a count of the total amount of elements in 
-- a vector based on its dimensions
size : Array xs t -> Nat
size arr {xs} = foldl (*) 1 xs


-- | Lift a 0 dimensional Vector  into a 1 dimensional 
--  Vector 
singleton : Array [] t -> Array [1] t
singleton t = [t]

-- | Inverse operation from singletonV, reduce dimension
-- of a 1 dimensional Vector with a single value into
-- a 0 dimensional Vector
invSingleton : Array [1] t -> Array [] t
invSingleton [t] = t


-- | Map operation on an Array, maps
--   all base elements
mapA : (a -> b) -> Array xs a -> Array xs b
mapA f arr {xs=[]}  = f arr
mapA f arr {xs = (y::ys)} = 
  case arr of
    [] => []
    (a::as) => (mapA f a) :: (map (mapA f) as)


-- | Reduce the dimensions of a 2+ dimensional vector
redDim : Array (x1::x2::xs) t -> Array (x1*x2::xs) t
redDim [] = []
redDim (v::vs) = v ++ redDim vs


-- | Transpose a 2+ dimensional Vector, switches first and second dimensions
transposeA : Array (x1::x2::xs) t -> Array (x2::x1::xs) t
transposeA [] = replicate _ []
transposeA (x::xs) = zipWith (::) x (transposeA xs)



-- Given a 1+ dimensional Vector in which the size of the highest dimension
-- sz_d0 = m * n, increases the Vector by 1 dimension by taking m lots
-- of n values
incDim : Array (m * n::xs) t -> Array (m::n::xs) t
incDim v {m} {n} = incDim' m n (toList v)
  -- We convert the given Vector into a list and use "unsafe" list
  -- functions to take m lots of n values from the list and then
  -- repackage these back into a Vector. Using the properties
  -- of the initial vector it should always be possible to do
  -- this without causing any runtime errors
  where 
    getN : (n : Nat) -> List t -> Vect n t
    getN Z l = []
    getN (S n) (x::xs) = x::(getN n xs)

    incDim' : (m : Nat) -> (n : Nat) -> List t -> Vect m (Vect n t)
    incDim' Z _ _ = []
    incDim' (S m) n xs = (getN n xs)::(incDim' m n (drop n xs))



-- Given a Vector of size n and a natural number m, and the conditions that m | n and m != 0
-- transforms the Vector of size n into a  Vector of size (m * (n `div` m)) which is equivalent
reshapeByFactor : (m : Nat) -> Array (n::ns) t -> {default SIsNotZ 
                                            nz : Not (m = Z)} -> 
                                            Array ((m * (divNatNZ n m nz))::ns) t
reshapeByFactor m v {n} {nz} = getN (m * (divNatNZ n m nz)) $ toList v
  where    
    getN : (n : Nat) -> List t -> Vect n t
    getN Z l = []
    getN (S n) (x::xs) = x::(getN n xs)



--{ok : n `mod` m = Z} ->
