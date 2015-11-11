Shape : Nat -> Type
Shape n = Vect n Nat

Vector : Shape n -> Type -> Type
Vector Nil t = t
Vector (v::vs) t = Vect v (Array vs t) 
