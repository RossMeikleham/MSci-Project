redDim : Vector (x1::x2::xs) t -> Vector (x1*x2::xs) t
redDim [] = []
redDim (v::vs) = v ++ redDim vs

