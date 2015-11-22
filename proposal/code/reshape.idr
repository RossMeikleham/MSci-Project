reshape : Vector (x1::(m * x2)::xs) t -> 
          Vector((x1 * m)::x2::xs) t
reshape [] = []
reshape (v::vs) = incDim v ++ reshape' vs
