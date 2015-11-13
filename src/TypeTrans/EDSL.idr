
module EDSL

--import TypeTrans.AST
import TypeTrans.Transformations
import TypeTrans.Array
import Control.Monad.State

import Data.Vect

data TypeT = TyInt | TyBool | TyFun TypeT TypeT | TyVect Nat TypeT

-- Difference between stream and seq?
data MapVariant = MSeq | MPar | MStream
data FoldVariant = FSeq | FStream | FTree

total
interpType : TypeT -> Type
interpType TyInt = Int
interpType TyBool = Bool
interpType (TyFun i o) = interpType i -> interpType o
interpType (TyVect i t) = Vect i (interpType t)



-- Locate "base"/primitive type e.g. int, bool
--total 
--baseType : TypeT -> TypeT
--baseType (TyFun i o) = 
--baseType TyVect Nat 


using (G : Vect xs TypeT) {

data HasType : Fin n -> Vect n TypeT -> TypeT -> Type where
  Stop : HasType FZ (t :: G) t
  Pop  : HasType k G t -> HasType (FS k) (u :: G) t 


data Expr : (Vect xs TypeT) -> TypeT -> Type where
  Var : HasType i G t -> Expr G t
  Val : (x : Int) -> Expr G TyInt 
  Map : MapVariant -> Expr G (TyFun a b) -> Expr G (TyVect n a) -> Expr G (TyVect n b)

  -- Treat Composition as Concatonation of multiple Applys in a row
  -- Apply f (Apply g o)  is a composition of f and g, can be used for
  -- map streaming optimisation
  Apply : Expr G (TyFun a b) -> Expr G a -> Expr G b
  --Let : Expr (a :: gam) (Val () :: gam’) (R t) -> Expr gam gam’ t
  
  FoldL : FoldVariant -> Expr G (TyFun a (TyFun b a)) -> 
                          Expr G a  -> Expr G (TyVect n b) -> Expr G a
  FoldR : FoldVariant -> Expr G (TyFun a (TyFun b b)) -> 
                          Expr G b  -> Expr G (TyVect n a) -> Expr G b
  
  -- For Assoc Fold, the function needs to be closed e.g. (a -> a -> a), possibly 
  -- ensure given type is a monoid and use the respective monoid function for that type,
  -- using implicit type class instances we can select which monoid we wish to use
  -- e.g. the natural numbers can create a monoid instance for both addition and multiplication 
  --FoldAssoc : (Monoid (interpType a)) => FoldVariant -> Expr G a -> Expr G (TyVect n a) -> Expr G a

  Lambda : Expr (a :: G) t -> Expr G (TyFun a t)
  --Compose : Expr G (TyFun a  -> Expr (head a

  Split : (m: Nat) -> Expr G (TyVect n t) -> 
                      {default SIsNotZ nz : Not (m = Z)} ->
                      {auto mz : modNatNZ n m nz = Z} -> 
                      Expr G (TyVect m (TyVect (divNatNZ n m nz) t))

  Merge : Expr G (TyVect x1 (TyVect x2 t)) -> Expr G (TyVect (x1 * x2) t)
  Op : (interpType a -> interpType b -> interpType c) -> Expr G a -> Expr G b -> Expr G c
  UnOp : (interpType a -> interpType b) -> Expr G a -> Expr G b


-- Idris Interpreter which executes the AST

-- When we produce an expression we need to know which variables are in scope,
-- as well as their types. Env is an environment indexed over the types in scope.
data Env : Vect n TypeT -> Type where
  Nil : Env Nil
  (::) : interpType a -> Env G -> Env (a :: G)


lookup : HasType i G t -> Env G -> interpType t
lookup Stop (x :: xs) = x
lookup (Pop k) (x :: xs) = lookup k xs

interp : Env G -> Expr G t -> interpType t
interp env (Var i) = lookup i env
interp env (Val x) = x
interp env (Apply f s) = (interp env f) (interp env s)
interp env (Lambda body) = \x => interp (x :: env) body
interp env (Map vt f xs) =  
  case (interp env xs) of
    [] => Nil
    (y::ys) => (interp env (Apply f (UnOp head xs))) :: (interp env (Map vt f (UnOp tail xs)))  


interp env (FoldL vt f x xs) = 
  case (interp env xs) of
    [] => interp env x 
    (y::ys) => interp env $ FoldL vt f (Apply (Apply f x) $ UnOp head xs) $ UnOp tail xs 

interp env (FoldR vt f x xs) =
  case (interp env xs) of
    [] => interp env x
    (y::ys) => interp env $ Apply (Apply f $ UnOp head xs) (FoldR vt f x $ UnOp tail xs)                             


interp env (Op op x y) = op (interp env x) (interp env y)
interp env (UnOp op x) = op (interp env x) 
interp env (Merge xs) = merge $ interp env xs 
interp env (Split m xs {nz} {mz}) = splitV m {nz} {mz} $ interp env xs

mkLam : TTName -> Expr (t::g) t' -> Expr g (TyFun t t')
mkLam _ body = Lambda body

-- Specify structures for DSL
dsl expr
  lambda = mkLam
  variable = Var
  index_first = Stop
  index_next = Pop
  variable = Var


pure : Expr G a -> Expr G a
pure = id

(<$>) : (f : Lazy (Expr G (TyFun a t))) -> Expr G a -> Expr G t
(<$>) f a = Apply f a

-- Examples:
syntax "map" [f] [xs] = Map MSeq f xs
syntax [x] "+" [y] = Op (+) x (Val y)


-- AST for lambda function which adds 3 to a given integer
add3 : Expr G (TyFun TyInt TyInt)
add3 = Lambda (Op (+) (Var Stop) (Val 3))

add3Pretty : Expr G (TyFun TyInt TyInt)
add3Pretty = expr (\x => Op (+) (Val 3) x)

add3Pretty2 : Expr G (TyFun TyInt TyInt)
add3Pretty2 = expr (\x => x + 3)

-- AST for lambda function which adds 2 integers
add : Expr G (TyFun TyInt (TyFun TyInt TyInt))
add = Lambda (Lambda (Op (+) (Var Stop) (Var (Pop Stop))))

addPretty : Expr G (TyFun TyInt (TyFun TyInt TyInt))
addPretty = expr (\x,y => (Op (+) x y))

-- AST for simple mapping over list
mapAdd3 : Expr G (TyFun (TyVect n TyInt) (TyVect n TyInt))
mapAdd3 = Lambda (Map MSeq (add3) (Var Stop)) 

mapAdd3Pretty : Expr G (TyFun (TyVect n TyInt) (TyVect n TyInt))
mapAdd3Pretty = expr (\xs => map add3 xs) 


-- AST for simple merge and mapping
map2dAdd3 : Expr G (TyFun (TyVect m (TyVect n TyInt)) (TyVect (m * n) TyInt)) 
map2dAdd3 = Lambda (Apply (mapAdd3) (Merge (Var Stop))) 

testAdd : Int ->  Expr G (TyFun TyInt TyInt)
testAdd i = Lambda (Op (+) (Var Stop) (Val i))

testAdd' : {n : Nat} -> Vect n t ->  Expr G (TyFun TyInt TyInt)
testAdd' v {n} = Lambda (Op (+) (Var Stop) (Val $ fromNat n))

--splitEx : Expr G (TyFun (TyVect (m * n) TyInt) (TyVect m (TyVect n TyInt)))
--splitEx {m = Z} = ?todo45 --Lambda (Var Stop)
--splitEx {m = S k} {n} = rewrite (modMProof m n) in (Lambda (Split m (Var Stop)))

--AST for merge, map, then split again
--mapAddSplit : Expr G (TyFun (TyVect m (TyVect n TyInt)) (TyVect m (TyVect n TyInt))) 
--mapAddSplit {m = Z} = Lambda (Var Stop)
--mapAddSplit {m = S k} = Lambda (Split m $ Apply (mapAdd3) (Merge (Var Stop)))

{-
print2dV : Vect m (Vect n Int) -> IO ()
print2dV xs = 
    do print "[" 
       print2dV' xs

  where print2dV' : Vect m (Vect n Int) -> IO ()
        print2dV' [] = print "]"
        print2dV' (x::[]) = do print x 
                               print "]"

        print2dV' (x::xs) = do print x 
                               print ", "
                               print2dV' xs 

-}

interpStuff : IO ()
interpStuff = do  
    print $ interp [] mapAdd3 [1,2,3,4]
    print v2d

    print v3


  where v2d : Vect 3 Int
        v2d = interp [] map2dAdd3 [[1,1,1]]

        v3 : Int
        v3 = interp [] add3 3
}





