
module EDSL

import TypeTrans.AST
import TypeTrans.Transformations
import TypeTrans.Array
import Control.Monad.State

import Data.Vect
import Effect.File


data Program : Type -> Type where 
  Map : (a -> b) -> Program (Array xs a) -> Program (Array xs b) --Deep Map
  Fold : (a -> b -> b)  -> Program (Array (x::xs) a) -> Program (Array xs b)
  DecDim : Program (Array (x1::x2::xs) a) -> Program (Array (x1*x2::xs) a)
  IncDim : (n : Nat) -> Program (Array (x::xs) a) -> Program (Array (n::(x `div` n)::xs) a)
  Singleton : Program (Array 0 [] a) -> Program (Array 1 [1] a)
  InvSingleton : Program (Array 1 [1] a) -> Program (Array 0 [] a) 
  Base : (Array r xs t) -> Program (Array r xs t)



-- | Interpreting the AST in Idris
eval : Program a -> Array r xs b
eval (Map f prg) = mapV f $ eval prg
eval (Base v) = v




instance Functor Program where
  map f (Map f2 p) = ?todo7


instance Applicative Program where
  pure = ?todo10
  a <*> b = ?todo11


instance Monad Program where
  a >>= b = ?todo12




{-
using (G: Vect Ty n) {
  data Expr : Vect Ty n -> Ty -> Type where
    Var : (i: Fin n) -> Expr G (vlookup i G)
  | Val : (x: Int) -> Expr G TyInt
  | Lam : Expr (A::G) T -> Expr G (TyFun A T)
  | App : Expr G (TyFun A T) -> Expr G A -> Expr G T
  | Op : (interpTy A -> interpTy B -> interpTy C) ->

  Expr G A -> Expr G B -> Expr G C;

}
-}

{-
data Expr
  BinPlus A B
  BinMinus A B
  BinIdent A
-}

{-
NVec : Vect n Nat -> Type -> Type
NVec Nil t = t
NVec (v::vs) t = Vect v (NVec vs t) 


-- Define base types
data BaseType = IntT | BoolT

 
data Program : (dim : Vect n Nat) -> (t : BaseType) -> Type where
   Map : (t -> t2) -> Program dim t2  
   
    
  

data Action =
  Map    


eval : Vect (x::xs) BaseType -> Program ->  a
eval (Prog act arg) = 


exampleProgram : Program 
exampleProgram = do
  

add : Program 
add = do
  v <- get
  nv <- mapV (+1) v
  return nv


-}
