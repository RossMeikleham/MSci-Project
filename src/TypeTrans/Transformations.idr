module TypeTrans.Transformations

import TypeTrans.AST
import Data.Vect

--TypeD : Nat -> TypeT -> Type
--MkTypeD t : TypeD n t



-- Reduce the dimensions in given dimensional type
redDim : TypeD (S (S n)) t1  -> TypeD (S n) t2
redDim (MkType (Vec x (Vec y t))) = MkType (Vec (x * y) t)


splitMap : Int -> Action -> Action
splitMap m (Map v a) = Compose [Merge m, Map v (Map v a), Split m]


splitFold : Int -> Action -> Action
splitFold m (Fold v fa acc) =  Compose [Fold v (Fold v fa acc) acc, Split m]

splitAssocFoldByMap : Int -> Action -> Action
splitAssocFoldByMap m (Fold v afa acc) = Compose [Fold v afa acc, Map v (Fold v afa acc), Split m]

liftMapCompose : Action -> Action 
liftMapCompose (Map v (Compose as)) = Compose (map (Map v) as)   

{- ???????
liftComposeMap : Action -> Action
liftComposeMap (Compose mas) = Map v (Compose as) 
    where 
        as = map (\(Map _ a) => a) mas
        Map v _ = head mas
-}


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
{- ???
letToNestedLet : Argument -> Argument 
letToNestedLet (Let exprs res) with (toIntegerNat $ length exprs) 
 | 1 = (Let exprs res)
 | _ = 
  letToNestedLet (Let exprs' (Let [expr] res))
    where 
        expr : (Argument, Argument) 
        expr = Prelude.List.last' exprs

        exprs' : List (Argument, Argument)
        exprs' = Prelude.List.init exprs        
-}

-- ???????
{-
letToLambda : Argument -> Argument 
letToLambda (Let [lst] res) = Res (Lambda lhs res) rhs 
  where
       lhs = fst $ unzip lst
       rhs = snd $ unzip lst 
-}  
  
   
