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
total
dim : Array xs t -> Nat
dim arr {xs} = length xs

-- Given a Vector returns the number of items
-- in the vector
total
length' : Vect n t -> Nat
length' v {n} = n 

-- Give the shape of a given array
total
shape : Array xs t -> Shape (length' xs) 
shape arr {xs} = xs


-- Gives a count of the total amount of elements in 
-- a vector based on its dimensions
total
size : Array xs t -> Nat
size arr {xs} = foldl (*) 1 xs


-- | Lift a 0 dimensional Vector  into a 1 dimensional 
--  Vector 
total
singleton : Array [] t -> Array [1] t
singleton t = [t]

-- | Inverse operation from singletonV, reduce dimension
-- of a 1 dimensional Vector with a single value into
-- a 0 dimensional Vector
total
invSingleton : Array [1] t -> Array [] t
invSingleton [t] = t


-- | Map operation on an Array, maps
--   all base elements
total
mapA : (a -> b) -> Array xs a -> Array xs b
mapA f arr {xs=[]}  = f arr
mapA f arr {xs = (y::ys)} = 
  case arr of
    [] => []
    (a::as) => (mapA f a) :: (map (mapA f) as)


-- | Reduce the dimensions of a 2+ dimensional vector
total
redDim : Array (x1::x2::xs) t -> Array (x1*x2::xs) t
redDim [] = []
redDim (v::vs) = v ++ redDim vs


-- | Transpose a 2+ dimensional Vector, switches first and second dimensions
total
transposeA : Array (x1::x2::xs) t -> Array (x2::x1::xs) t
transposeA = transpose



-- Given a 1+ dimensional Vector in which the size of the highest dimension
-- sz_d0 = m * n, increases the Vector by 1 dimension by taking m lots
-- of n values
total
incDim : Array (m * n::xs) t -> Array (m::n::xs) t
incDim v {m = Z}  = []
incDim v {m = S r} {n} = 
    let (fstN, rest) = (take n v, drop n v) in 
        fstN :: (incDim rest)


-- Section for reshaping a vector keeping the dimensionality
-- the same except showing that the most outer dimension
-- is comprised of 2 factors multiplied together

-- Proof dividing 0 by a non zero number gives 0
total
divZProof : (m : Nat) -> (nz : Not (m = Z)) -> divNatNZ 0 m nz = 0
divZProof Z nz = void (nz Refl)
divZProof (S Z) _ = Refl
divZProof (S (S n)) _ = Refl  


-- Proof modulo 0 by a non zero number gives 0
total
modZProof : (m : Nat) -> (nz : Not (m = Z)) -> modNatNZ 0 m nz = 0
modZProof Z nz = void (nz Refl)
modZProof (S Z) _ = Refl
modZProof (S (S n)) _ = Refl 


-- Proof of the Quotient Remainder theorem for the specific
-- case of remainder = mod n m, and quotient = div n m
total
divModProof : (m : Nat) -> (n : Nat) -> 
                           (nz : Not (m = Z)) ->
                           (n = m * (divNatNZ n m nz) + (modNatNZ n m nz)) 
divModProof Z _ nz = void (nz Refl) -- Contraction m /= Z by supplied nz proof
divModProof m Z nz ?= Z -- Proof when n = 0 for all m
divModProof m n nz ?= n  


TypeTrans.Array.divModProof_lemma_1 = proof
  intros
  rewrite sym (divZProof m nz)
  rewrite sym (modZProof m nz)
  rewrite sym (plusZeroRightNeutral (mult m 0))
  rewrite sym (multZeroRightZero m)
  trivial


-- TODO Temporary "believe_me" proof, should be replaced
-- with the proof that n = m * (n `div` m) + (n `mod` m) if/when possible
TypeTrans.Array.divModProof_lemma_2 = proof 
  intro
  intro
  exact believe_me n


-- Proof that when m divides n that n = m * (n / m) in the case of
-- integer division
factorDivProof : (m : Nat) -> (n : Nat) -> 
                        (nz : Not (m = Z)) -> 
                        (mz : modNatNZ n m nz = Z) -> n = m * (divNatNZ n m nz)
 
factorDivProof Z _ nz _ = void (nz Refl) -- Contradiction, m /= Z by supplied nz proof
factorDivProof m Z nz _ ?= Z 
factorDivProof m n nz mz ?= n  

TypeTrans.Array.factorDivProof_lemma_1 = proof
  intros
  rewrite sym (divZProof m nz)
  rewrite sym (multZeroRightZero m)
  trivial

-- Considering this is a special case of the Quotient Remainder theorem
-- (remainder = 0) we show that this is contained within it, and use that 
-- proof to prove this proof
TypeTrans.Array.factorDivProof_lemma_2 = proof
  intros
  rewrite (plusZeroRightNeutral (m * divNatNZ n m nz))
  rewrite mz
  rewrite (divModProof m n nz)
  trivial


-- Given a Vector of size n and a natural number m, and the conditions that m | n and m != 0
-- transforms the Vector of size n into a  Vector of size (m * (n `div` m)) which is equivalent
total
reshapeByFactor : (m : Nat) -> Array (n::ns) t -> 
                               {default SIsNotZ nz : Not (m = Z)} -> 
                               {auto mz : modNatNZ n m nz = Z} ->
                               Array ((m * (divNatNZ n m nz))::ns) t

reshapeByFactor Z _ {nz} = void (nz Refl)
reshapeByFactor m xs {n} {nz} {mz} = rewrite sym (factorDivProof m n nz mz) in xs
