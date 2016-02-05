module TypeTrans.Array 

-- Module to represent Vector types, we use
-- Array as it's not already a taken construct
-- in the Idris prelude

import Data.Vect
import Data.List

%default total

-- A Shape is a Vector which represents the structure
-- of an Array e.g. the shape of [[1,2,3],[1,2,3]] would be [2,3]
Shape : Type
Shape = List Nat

-- Rank represents the number of dimensions in an
-- Array, e.g. the rank of [[]] would be 2
Rank : Type
Rank = Nat


Array : Shape -> Type -> Type
Array [] t  = t
Array (v::vs) t = Vect v (Array vs t)


-- Give number of dimensions in the given Array
dim : Array xs t -> Nat
dim arr {xs} = length xs

-- Given a Vector returns the number of items
-- in the vector
length' : Vect n t -> Nat
length' v {n} = n 

-- Give the shape of a given array
shape : Array xs t -> Shape 
shape arr {xs} = xs


-- Gives a count of the total amount of elements in 
-- a vector based on its dimensions
size : Array xs t -> Nat
size arr {xs} = foldr (*) 1 xs


-- Proof that a zero dimensional array cannot
-- contain more than zero dimensions
arrayCannotBeEmpty : Array (0::xs) t -> Void
arrayCannotBeEmpty (v::vs) impossible


-- | Lift a 0 dimensional Vector  into a 1 dimensional 
--  Vector 
singleton : Array (xs) t -> Array (1::xs) t
singleton t = [t]

-- | Inverse operation from singletonV, reduce dimension
-- of a 1 dimensional Vector with a single value into
-- a 0 dimensional Vector
invSingleton : Array (1::xs) t -> Array (xs) t
invSingleton [t] = t


-- | Map operation on an Array, maps
--   all base elements
mapA : (a -> b) -> Array xs a -> Array xs b
mapA f v {xs=[]}  = f v
mapA f v {xs = (y::ys)} = map (mapA f) v


mapM : Monad m => (a -> m b) -> Vect n a -> m (Vect n b)
mapM _ Nil = return Vect.Nil
mapM f (x::xs) = do
  x' <- f x
  xs' <- mapM f xs
  return (Vect.(::) x' xs')

mapM_ : Monad m => (a -> m b) -> Vect n a -> m ()
mapM_ _ Nil = return ()
mapM_ f (x::xs) = do
  f x
  mapM_ f xs

mapMA : Monad m => (a -> m b) -> Array xs a -> m (Array xs b)
mapMA f v {xs=[]} = f v
mapMA f v {xs = (y::ys)} = mapM (mapMA f) v

mapMA_ : Monad m => (a -> m b) -> Array xs a -> m ()
mapMA_ f v = do
  mapMA f v
  return ()

mapML : Monad m => (a -> m b) -> List a -> m (List b)
mapML _ [] = return []
mapML f (x::xs) = do
    x' <- f x
    xs' <- mapML f xs
    return (x'::xs')

mapML_ : Monad m => (a -> m b) -> List a -> m ()
mapML_ f v = do 
  mapML f v
  return ()

-- | Reduce the dimensions of a 2+ dimensional vector
redDim : Array (x1::x2::xs) t -> Array (x1*x2::xs) t
redDim [] = []
redDim (v::vs) = v ++ redDim vs 



-- | Flaten an Array down to 1 dimension
flattenA : Array (x::xs) t -> (n ** Array [S n] t) 
flattenA v {x = Z} = void (arrayCannotBeEmpty v)
flattenA v {x=S m} {xs=[]}  = (_ ** v)
flattenA v {xs = (y::ys)} = (flattenA (redDim v))



-- | FoldL operation on Array
foldlA : (a -> b -> a) -> a -> Array (x::xs) b -> a
foldlA f e v with (flattenA v)
  | (_ ** v') = foldlA' f e v'
  where foldlA' : (a -> b -> a) -> a -> Array [(S ys)] b -> a
        foldlA' f e v = foldl f e v



-- | Foldl1 operation on an Array
foldlA1 : (a -> a -> a) -> Array (x::xs) a -> a
foldlA1 f v with (flattenA v)
  | (_ ** v') = foldlA1' f v'
  where foldlA1' : (a -> a -> a) -> Array [(S ys)] a -> a 
        foldlA1' f v = foldl1 f v



-- | Transpose a 2+ dimensional Vector, switches first and second dimensions
transposeA : Array (x1::x2::xs) t -> Array (x2::x1::xs) t
transposeA = transpose



-- Given a 1+ dimensional Vector in which the size of the highest dimension
-- sz_d0 = m * n, increases the Vector by 1 dimension by taking m lots
-- of n values
incDim : Array (m * n::xs) t -> Array (m::n::xs) t
incDim v {m = Z}  = []
incDim v {m = S r} {n} = 
    let (fstN, rest) = (take n v, drop n v) in 
        fstN :: (incDim rest)


reshape' : Array (x1::(m * x2)::xs) t -> Array((x1 * m)::x2::xs) t
reshape' [] = []
reshape' (v::vs) = incDim v ++ reshape' vs

reshape : Array (x1::(m * x2)::xs) t -> Array ((m * x1)::x2::xs) t
reshape v {m} {x1} = rewrite (multCommutative m x1) in reshape' v


invReshape' : Array ((x1 * m)::x2::xs) t -> Array (x1::(m * x2)::xs) t
invReshape' v {x1 = Z} = [] 
invReshape' v {x1 =S r} = map redDim $ incDim v


invReshape : Array ((m * x1)::x2::xs) t -> Array (x1::(m * x2)::xs) t
invReshape v = invReshape' $ flip v
  where flip : Array ((m * x1)::x2::xs) t -> Array ((x1 * m)::x2::xs) t
        flip v {m} {x1} = rewrite multCommutative x1 m in v


-- Section for reshaping a vector keeping the dimensionality
-- the same except showing that the most outer dimension
-- is comprised of 2 factors multiplied together

-- Proof dividing 0 by a non zero number gives 0
divZProof : (m : Nat) -> (nz : Not (m = Z)) -> divNatNZ 0 m nz = 0
divZProof Z nz = void (nz Refl)
divZProof (S Z) _ = Refl
divZProof (S (S n)) _ = Refl  


-- Proof modulo 0 by a non zero number gives 0
modZProof : (m : Nat) -> (nz : Not (m = Z)) -> modNatNZ 0 m nz = 0
modZProof Z nz = void (nz Refl)
modZProof (S Z) _ = Refl
modZProof (S (S n)) _ = Refl 


-- Proof modNatNZ (m * n) n = 0
modMProof : (m : Nat) -> (n: Nat) -> {default SIsNotZ nz : Not (m = Z)} -> modNatNZ (mult m n) m nz = 0
modMProof Z _ {nz} = void (nz Refl)
modMProof _ Z ?= Z
modMProof m n ?= Z



-- TODO fill these out latee
TypeTrans.Array.modMProof_lemma_1 = proof
  intro
  intro
  exact believe_me Z

TypeTrans.Array.modMProof_lemma_2 = proof
  intro
  intro
  exact believe_me Z


-- Proof of the Quotient Remainder theorem for the specific
-- case of remainder = mod n m, and quotient = div n m
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
reshapeByFactor : (m : Nat) -> Array (n::ns) t -> 
                               {default SIsNotZ nz : Not (m = Z)} -> 
                               {auto mz : modNatNZ n m nz = Z} ->
                               Array ((m * (divNatNZ n m nz))::ns) t

reshapeByFactor Z _ {nz} = void (nz Refl)
reshapeByFactor m xs {n} {nz} {mz} = rewrite sym (factorDivProof m n nz mz) in xs


-- Split in one step
splitA : (m : Nat) -> Array (n::ns) t -> 
                               {default SIsNotZ nz : Not (m = Z)} -> 
                               {auto mz : modNatNZ n m nz = Z} ->
                               Array (m ::(divNatNZ n m nz)::ns) t
splitA m a {mz} {nz} = incDim $ reshapeByFactor m a {mz = mz} {nz = nz}



-- Helper functions for reshaping Vectors instead of Arrays,
-- as Unification behaviour is being a bit strange atm,


-- Flatten a 2d vector into a 1d vector
merge : Vect x1 (Vect x2 t) -> Vect (x1 * x2) t
merge [] = []
merge (v::vs) = v ++ merge vs

 
incDimV : Vect (m * n) t -> Vect m (Vect n t)
incDimV v {m = Z}  = []
incDimV v {m = S r} {n} = 
    let (fstN, rest) = (take n v, drop n v) in 
        fstN :: (incDimV rest)


reshapeByFV : (m : Nat) -> Vect n t -> 
                               {default SIsNotZ nz : Not (m = Z)} -> 
                               {auto mz : modNatNZ n m nz = Z} ->
                               Vect (m * divNatNZ n m nz) t

reshapeByFV Z _ {nz} = void (nz Refl)
reshapeByFV m xs {n} {nz} {mz} = rewrite sym (factorDivProof m n nz mz) in xs


splitV : (m : Nat) -> Vect n t -> 
                               {default SIsNotZ nz : Not (m = Z)} -> 
                               {auto mz : modNatNZ n m nz = Z} ->
                               Vect m (Vect (divNatNZ n m nz) t)
splitV m a {mz} {nz} = incDimV $ reshapeByFV m a {mz = mz} {nz = nz}



doubleToNat : Double -> Nat
doubleToNat d = fromIntegerNat $ cast d

-- Generate all factors for a given number
factors : Nat -> List Nat
factors (S Z) = [(S Z)]
factors n = assert_total $ lows ++ (reverse $ map (div n) lows)
    where lows = filter ((== 0) . modNat n) [1..doubleToNat .floor . sqrt $ cast n]


-- Get all factors of the largest dimension in
-- the given Vector
factorsV : Array (x::xs) t -> List Nat
factorsV {x} _ = factors x

-- Generate all factor pairs of a given natural number
factorPairs : Nat -> List (Nat, Nat)
factorPairs n = assert_total $ map (\f => (f, div n f)) fs 
  where fs = factors n


-- Sacrificing totality for functionality, split an Array into a higher
-- dimension
partial
splitA2 : (n : Nat) -> Array (x::xs) t -> Array (n :: div x n :: xs) t
splitA2 n xs {x} = split' n (div x n) (toList xs)
  where 
        partial
        getN : (n : Nat) -> List t -> Vect n t
        getN Z l = []
        getN (S n) (x::xs) = x::(getN n xs)
        
        partial 
        split' : (m : Nat) -> (n : Nat) -> List t -> Vect m (Vect n t)
        split' Z _ _ = []
        split' (S m) n xs = (getN n xs)::(split' m n (drop n xs))

infixr 5 !!;
partial
(!!) : {a : Type} -> List a -> Nat -> a
(x::xs) !! Z = x
(x::xs) !! (S n) = xs !! n

-- Split an array by the nth factor of its highest dimension, 
-- returns a Sigma Type containing the given factor with the split array
partial
splitNFactor: (n : Nat) -> Array (x::xs) t -> (f : Nat ** Array (f :: div x f :: xs) t)
splitNFactor n xs {x} = (f ** (splitA2 f xs))
  where f = factors x !! n

-- Generate all possible vector combinations using the factors of the highest
-- dimension of the given vector, returns a list of sigma values containing the
-- largest dimension of each split array along with the split array itself
partial
splitFactors : Array (x::xs) t -> List (f : Nat ** Array (f :: div x f :: xs) t)
splitFactors xs {x} = map (\f => (f ** splitA2 f xs)) (factors x)

partial
convertFactors : (f ** Array (f :: div x f :: xs) t) -> (ys ** Array ys t) 
convertFactors (f ** ys) {x} {xs} = assert_total $ ((f :: div x f :: xs) ** ys)

partial
splitFactorsGeneric : Array (x::xs) t -> List (ys ** Array ys t)
splitFactorsGeneric xs = map convertFactors $ splitFactors xs



toVect : Array (x::xs) t -> Vect x (Array xs t)
toVect = id

fromVect : Vect n t -> Array [n] t
fromVect = id

partial
printVect : (Show t) => Vect xs t -> IO()
printVect xs = do 
  print "[ "  
  mapM_ (\x => print x >>= \_ => print " ") xs
  print "]"


partial
printArr : (Show t) => Array xs t -> IO ()
printArr vs {t} = printArr' vs >>= \_ => putStrLn ""
  where 
    printArr' : (Show t) => Array xs t -> IO ()
    printArr' v {xs=[]} = print v >>= \_ => putStr ""
    printArr' v {xs = (y::ys)} = do
      putStr "["
      case v of
        [] => putStr ""
        (a::as) => do
          mapM_ (\x => printArr' x >>= \_ => putStr ",") $ init (a::as)
          printArr' (last (a::as))  
  
      putStr "]"

partial
printSigmaArr : (Show t) => (xs ** Array xs t) -> IO ()
printSigmaArr v {t} with (v) 
  | (xs ** vs) = printArr vs {t}


partial
printArrs : (Show t) => List (xs ** Array xs t) -> IO ()
printArrs vs {t} = mapML_ (\v => printSigmaArr v {t}) vs

