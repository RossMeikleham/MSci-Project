module TypeTrans.AST

import Data.Vect

-- Define Type Aliases
Rule : Type
Rule = String

Name : Type
Name = String

Value : Type
Value = String

Assoc : Type
Assoc = Bool

Performance : Type
Performance = Float

Cost : Type
Cost = Float

data Variant = Par | Seq | Stream | Tree 

instance Show Variant where
  show Par = "Par"
  show Seq = "Seq"
  show Stream = "Stream"
  show Tree = "Tree"


data TypeT = 
    Vec Nat TypeT |
    Tuple (List TypeT) | 
    IntT | 
    ByteT | 
    BitT | 
    LongT | 
    FloatT | 
    DoubleT | 
    BoolT | 
    T1 | 
    T2 | 
    T3 

instance Show TypeT where 
  show (Vec i t) = "Vec " ++ show i ++ " (" ++ show t ++ ")" 
  show (Tuple xs) = "Tuple " ++ show xs 
  show IntT = "Int"
  show ByteT = "Byte"
  show BitT = "Bit"
  show LongT = "Long"
  show FloatT = "Float"
  show DoubleT = "Double"
  show BoolT = "Bool"
  show T1 = "T1"
  show T2 = "T2"
  show T3 = "T3"


-- Vector with description of its dimensions in the type
--NVec : Vect n Nat -> TypeT -> TypeT
--NVec Nil t = t
--NVec (v::vs) t = Vec v (NVec vs t) 


-- Calculate the dimension of the given type
getDimension : TypeT -> Nat
getDimension (Vec i t) = (S Z) + getDimension t 
getDimension _ = Z -- Non vector types have dimension 0



mutual
-- Argument is not a very good name. I mean something of type a as opposed to a -> b for the actions
  data Argument = 
       Arg Name TypeT | 
       Val Value TypeT | 
       Res Action Argument |
       Let (List (Argument,Argument)) Argument --  let like this is not an action, it's only an action if I do  \x -> let ... x ... in ... i.e. Lambda x (let ...)

  instance Show Argument where
    show (Arg n t) = "Arg " ++ n ++ " " ++ show t
    show (Val v t) = "Val " ++ v ++ " " ++ show t
    show (Res act arg) = "Res " ++ show act ++ " " ++ show arg
    show (Let xs arg) = "Let " ++ show xs ++ " " ++ show arg

  data Action = 
      Opaque Name (List Argument) Argument TypeT (Performance,Cost) | -- [Type] is for constant args to map or fold, the first Type is the input arg, the last Type the return type
      OpaqueBin Assoc Name (List Argument) Argument Argument (Performance,Cost) |
      Map Variant Action | 
      Fold Variant Action Argument | -- Argument here is the accumulator, and action must be a binary operation, not unary
      Compose (List Action) | 
      -- Lambda (List Argument) (Action) ? 
      Lambda (List Argument) Argument | -- (\(x,y) -> map (g x) y) becomes Lambda [x,y] (Map g x) y so the last Argument is usually a Res
      Loop Action Action |
      Split Int | 
      Merge Int | 
      Distr Int Int |
      Group (List (Argument, List Rule)) | 
      Ungroup (List (Argument, List Rule)) |
      Zip (List TypeT) | -- this should really only work on a set of vectors and return a Vec (Tuple [Type]) Int
      Unzip TypeT  -- This should really only work on a Tuple [Vec Type Int]
    
  instance Show Action where 
    show (Opaque n xs arg t pc) = "Opaque " ++ n ++ " " ++ show xs ++ " " ++ 
                                  show arg ++ " "++ show t ++ " " ++ show pc
    show (OpaqueBin a n xs arg1 arg2 pc) = "Opaque " ++ show a ++ " " ++ n ++ " " ++
                                         show arg1 ++ " " ++ show arg2 ++ " " ++ show pc
    show (Map v act) = "Map " ++ show v ++ " " ++ show act
    show (Fold v act arg) = "Fold " ++ show v ++ " " ++ show act ++ " " ++ show arg
    show (Compose xs) = "Compose " ++ show xs
    show (Lambda xs act) = "Lambda " ++ show xs ++ " " ++ show act
    show (Loop act1 act2) = "Loop " ++  show act1 ++ " " ++ show act2
    show (Split i) = "Split " ++ show i
    show (Merge i) = "Merge " ++ show i
    show (Distr i1 i2) = "Distr " ++ show i1 ++ " " ++ show i2
    show (Group xs) = "Group " ++ show xs
    show (Ungroup xs) = "Ungroup " ++ show xs
    show (Zip xs) = "Zip " ++ show xs
    show (Unzip t) = "Unzip " ++ show t


-- We also need Zip, Unzip and Let
--data FoldAction =  deriving Show-- No need for return type as it's b -> a  -> b


data Program = Prog Action Argument  -- So actually Prog is identical to Res

instance Show Program where
  show (Prog act arg) = "Prog " ++ show act ++ " " ++ show arg

-- I also need to represent a while-loop 
-- We assume we have a loop primitive in the language
-- let loop cond action v  = (let res = action v in if (cond res) then res else loop cond action res) 
-- This becomes Loop (Opaque "cond" [] (Arg "res" T2) BoolT) (Opaque "action" [] (Arg "v" T1))
-- and a way to extract values from a tuple, maybe a let?
{-

let
    (err, p', p_avg) = fold (0, [], 0) sor p
in
    map (stage3 p_avg) p'
    rather than simply (map stage3) $ (fold acc stage2) $ (map stage1) p
 this would be
 (\(v_in,stage1,stage2) -> let  (err, p', p_avg) = fold (0, [], 0) stage1 v_in in map (stage2 p_avg) p') $ map stage1 p
 The best way is to add a Lambda action


(\(x,y) -> map (g x) y) . (foldl f acc ) $ v -- [4,5,6]
-}

-- (Tuple [IntT,Vec IntT 3]) 
{-
p : Program 
p = Prog  (Compose [
            Lambda [Arg "x" IntT, Arg "y" (Vec 3 IntT)] 
                   (Map Seq (Opaque "g" [Arg "x" IntT] (Arg "a1" IntT) IntT (0,0)))
                   ]
          ) {- (Arg "y" (Vec IntT 3)), 
        Fold Seq (OpaqueBin True "f" [] (Arg "acc" (Tuple [IntT,Vec IntT 3])) (Arg "a2" IntT) (0,0)) (Arg "acc" (Tuple [IntT,Vec IntT 3]))
        ])  -} 
    (Arg "v" (Vec 3 IntT)) 

-}
