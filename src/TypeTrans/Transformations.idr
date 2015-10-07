module TypeTrans.Transformations

import TypeTrans.AST
import Data.Vect

{-
data TypeD : Nat -> TypeT -> Type where
  MkTypeD : (t : TypeT) -> TypeD n t

redDim : TypeD (S (S n)) t  -> TypeD (S n) t`
redDim (MkTypeD (Vec x (Vec y t))) = MkTypeD (Vec (x * y) t)
-}

--TODO place vector stuff in own module

-- Vector with description of its dimensions in the type
NVec : Vect n Nat -> Type -> Type
NVec Nil t = t
NVec (v::vs) t = Vect v (NVec vs t) 


--mapV : (t1 -> t2) -> NVec (x1::x2::xs) t1 -> NVec xs t2
--mapV f [] = []

--mapV : (t1 -> t2) -> NVec (x::xs) t1 -> NVec (x::xs) t2
--mapV f [] = []
--mapV f (v::vs) = (f v)

--mapV 

-- | Lift a 0 dimensional Vector  into a 1 dimensional 
--  Vector 
singletonV : NVec [] t -> NVec [1] t
singletonV t = [t]

-- | Inverse operation from singletonV, reduce dimension
-- of a 1 dimensional Vector with a single value into
-- a 0 dimensional Vector
invSingletonV : NVec [1] t -> NVec [] t
invSingletonV [t] = t


-- | Reduce the dimensions of a 2+ dimensional vector
redDimV : NVec (x1::x2::xs) t -> NVec (x1*x2::xs) t
redDimV [] = []
redDimV (v::vs) =  v ++ redDimV vs

-- | Increase the dimension of a 1+ dimensional vector 
--   requires that m divides the highest dimension of the given
--   vector, and m != 0
incrDimV : (m : Nat) -> NVec (x::xs) t -> Not (m = Z)    
                                       -> {auto ok : x `mod` m = Z} 
                                       -> NVec (m::(x `div` m)::xs) t
incrDimV m v nz {x} = ?todo
  where dv = x `div` m


incrDim : Nat -> TypeT -> Maybe TypeT
incrDim Z __ = Nothing
incrDim m (Vec sz tp) =
  if nsz * m == sz 
    then Just (Vec m (Vec nsz tp)) 
    else Nothing
  where 
    nsz = sz `div` m
incrDim _ _ = Nothing 

 

redDim : TypeT -> Maybe TypeT
redDim  (Vec sz1 (Vec sz2 tp)) = Just (Vec (sz1 * sz2) tp)
redDim _ = Nothing


splitMap : Int -> Action -> Action
splitMap m (Map v a) = Compose [Merge m, Map v (Map v a), Split m]


splitFold : Int -> Action -> Action
splitFold m (Fold v fa acc) =  Compose [Fold v (Fold v fa acc) acc, Split m]

splitAssocFoldByMap : Int -> Action -> Action
splitAssocFoldByMap m (Fold v afa acc) = Compose [Fold v afa acc, Map v (Fold v afa acc), Split m]

liftMapCompose : Action -> Action 
liftMapCompose (Map v (Compose as)) = Compose (map (Map v) as)   

-- Check
liftComposeMap : Action -> Action
liftComposeMap (Compose ((Map v a)::xs)) = Map v (Compose as) 
    where 
        as = map (\(Map _ a) => a) ((Map v a)::xs)



splitCompose : Action -> Action
splitCompose (Compose (a::as)) = Compose [a,Compose as]

mergeCompose : Action -> Action
mergeCompose (Compose (a::Compose as::[])) = Compose (a::as) 
-- -----------------------------
--


combineSplitMerge : Action -> Action -> Action                            
combineSplitMerge s m =
    let
        Split n1 = s
        Merge n2 = m
    in
        Distr n1 n2


combineSplitDistr : Action -> Action -> Action
combineSplitDistr s m =
    let
        Split n1 = s
        Distr n2 n3 = m
    in
        Distr n1 n3 -- CHECK!!


combineDistrMerge : Action -> Action -> Action
combineDistrMerge s m =
    let
        Distr n1 n2= s
        Merge n3 = m
    in
        Distr n1 n3


joinSplitMerge_helper : ((Action -> Action -> Action) , (Action -> Bool) , (Action -> Bool), 
                          List Action, List Action)  -> List Action
joinSplitMerge_helper (comb, t1, t2, [], as') = as'
joinSplitMerge_helper (comb, t1, t2, s::m::ras, as') =
    if (t1 s && t2 m)  
      then
        joinSplitMerge_helper (comb, t1, t2,ras, (as'++[comb s m]))
      else
        joinSplitMerge_helper (comb, t1, t2,(m::ras), (as'++[s]))


isSplit : Action -> Bool 
isSplit (Split _) = True
isSplit _ = False
  
isMerge : Action -> Bool
isMerge (Merge _) = True
isMerge _ = False
  
isDistr : Action -> Bool
isDistr (Distr _ _) = True
isDistr _ = False


joinSplitMerge : Action -> Action
joinSplitMerge (Compose [a]) =  Compose [a]
joinSplitMerge (Compose []) =  Compose []
joinSplitMerge (Compose as) = Compose (joinSplitMerge_helper (combineSplitMerge, isSplit, isMerge, as, []))

joinSplitDistr : Action -> Action
joinSplitDistr (Compose [a]) =  Compose [a]
joinSplitDistr (Compose []) =  Compose []
joinSplitDistr (Compose as) = Compose (joinSplitMerge_helper (combineSplitDistr, isSplit, isDistr, as, []))


joinDistrMerge : Action -> Action
joinDistrMerge (Compose [a]) =  Compose [a]
joinDistrMerge (Compose []) =  Compose []
joinDistrMerge (Compose as) = Compose (joinSplitMerge_helper (combineDistrMerge, isDistr, isMerge, as, []))



-- -----------------------------
--TODO Check
letToNestedLet : Argument -> Argument 
letToNestedLet (Let exprs res) = case exprs of
  (x::xs) => (Let exprs res)
  -- Need verbosity of x1::x2::xs for automatic proof checker to 
  -- infer that exprs is non empty
  (x1::x2::xs) => letToNestedLet (Let (init (x1::x2::xs)) 
                    (Let [Prelude.List.last (x1::x2::xs)] res))



-- TODO check, doesn't make sense
-- Lambda [Argument] Argument -> Action
-- Let [(Argument, Argument)] Argument -> Argument
-- Res Action Argument -> Argument
--letToLambda : Argument -> Argument
--letToLambda (Let [(lhs, rhs)] res) = Res (Lambda lhs res) rhs 
