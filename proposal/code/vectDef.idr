Data Vect : Nat -> Type -> Type
  Nil : Vect 0 a
  (::) : a -> Vect n a -> Vect (n + 1) a
