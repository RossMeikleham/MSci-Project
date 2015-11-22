invReshape : 
    Vector ((x1 * m)::x2::xs) t ->
    Vector (x1::(m * x2)::xs) t

invReshape v {x1 = Z} = [] 
invReshape v {x1 =S r} = 
    map redDim $ incDim v
