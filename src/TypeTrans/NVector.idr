module NVector

import Data.Vect

--iinfixr 7 ::

--data NVector : Vect n Nat -> Type -> Type where
--    Nil : NVector Nil a
--    (::) : 


data TypeD : Nat -> TypeD -> Type
     IntT : 

data TypeD : (d : Nat) -> Type where
Vec d TypeT | Tuple [TypeT] | IntT | ByteT | BitT | LongT | FloatT | DoubleT | BoolT | T1 | T2 | T3 



NVector : Vect n Nat -> Type -> Type
NVector Nil t = t
NVector (v::vs) t = Vect v (NVector vs t) 


-- | Reduce dimensions of type, given type must have dimension
--   of at least 1
redDim : TypeD (S d) -> TypeD d 
redDim v {S d} = ?todo1 --getDim (S d) v  * 
--        Vec (Vec tp sz2) sz1 -> Just (Vec tp (sz1*sz2) )
--        _ -> Nothing


-- | Increase dimension of a type, size of  
incDim : Nat -> TypeD (S d) -> TypeD (S (S d))
incDim  



--NNil : NVector Nil a
--NNil {a} = NVector Nil a

-- | Type transform a type into a 1 x 1 Vector containing that type
singleton : a -> Type
singleton _ {a} = NVector ([S Z]) a

-- | Inverse of singleton, type transforms type of  1 x 1 Vector 
--   into that type
invSingleton : NVector ([S Z]) a -> Type
invSingleton v {a} = a

-- | Get the atomic type of the given N Vector
getType : NVector n a -> Type
getType v {a} = a

