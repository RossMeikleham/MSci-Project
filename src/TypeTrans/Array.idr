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
Array : (n : Rank) -> Shape n -> Type -> Type
Array Z Nil t = t
Array (S m) vs t = Vect (head vs) (Array m (tail vs) t)
Array (S m) (v::vs) t = Vect v (Array m vs t) 


-- Give number of dimensions in the given Array
dim : Array n xs t -> Nat
dim arr {n} = n

-- Give the shape of a given array
shape : Array n xs t -> Shape n
shape arr {xs} = xs


-- | Lift a 0 dimensional Vector  into a 1 dimensional 
--  Vector 
singleton : Array 0 [] t -> Array 1 [1] t
singleton t = [t]

-- | Inverse operation from singletonV, reduce dimension
-- of a 1 dimensional Vector with a single value into
-- a 0 dimensional Vector
invSingleton : Array 1 [1] t -> Array 0 [] t
invSingleton [t] = t


-- | Map operation on an Array, maps
--   all base elements
mapA : (a -> b) -> Array r xs a -> Array r xs b
mapA f arr {r=Z} {xs=[]}  = f arr
mapA f arr {r=(S n)} {xs = (y::ys)} = 
  case arr of
    [] => []
    (a::as) => (mapA f a) :: (map (mapA f) as)


-- | Reduce the dimensions of a 2+ dimensional vector
redDim : Array (S (S n)) (x1::x2::xs) t -> Array (S n) (x1*x2::xs) t
redDim [] = []
redDim (v::vs) = v ++ redDim vs


-- | Transpose a 2+ dimensional Vector, switches first and second dimensions
transposeA : Array (S (S n)) (x1::x2::xs) t -> Array (S (S n)) (x2::x1::xs) t
transposeA [] = replicate _ []
transposeA (x::xs) = zipWith (::) x (transposeA xs)



{- TODO, should be able to have Array as an instance of a Functor
   using mapA as the map function, Idris doesn't like the (Array r xs) parameter
   for not being "injective" 
instance Functor (Array r xs) where
 map = mapA 
-}



divProof : (m : Nat) -> (n : Nat) -> Not (m = z) -> n `mod` m = Z -> (m * (n `div` m)) = n 
divProof m n nzp mp = ?todo


expandV : (m : Nat) -> (n : Nat) -> Vect (m * n) t -> Vect m (Vect n t) 
expandV m n v = ?todo2


incVDim : (m : Nat) -> (n : Nat) -> Vect (m * (n `div` m)) t -> Not (m = z) -> Vect m (Vect (n `div` m) t)
incVDim m n v prf = expand m n v


getV : (m : Nat) -> Vect n t -> Not (m = z) -> {auto ok : n `mod` m = Z} -> Vect (n `div` m) t
getV m v nzp {n} {ok} = take (n `div` m) v'
  where v' : Vect (m * (n `div` m)) t
        v' = rewrite (divProof m n nzp ok) in v



--incVDim : (m : Nat) -> Vect n t -> Not (m = z) -> {auto ok : n `mod` m = Z} -> Vect m (Vect (n `div` m) t)
--incVDim m v nzp {n} = concat $ replicate m (take (n `div` m) v)




-- | Increase the dimension of a 1+ dimensional vector 
--   requires that m divides the highest dimension of the given
--   vector, and m != 0
--incDim : (m : Nat) -> Array (S r) (x::xs) t -> Not (m = Z)    
--                                       -> {auto ok : x `mod` m = Z} 
--                                       -> Array (S (S r)) (m::(x `div` m)::xs) t
--incDim m v nz p = ?todo
--  where dv = x `div` m
