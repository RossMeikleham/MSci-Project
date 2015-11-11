incDim : Array (m * n::xs) t -> Array (m::n::xs) t
incDim v {m = Z}  = []
incDim v {m = S r} {n} = 
    let (fstN, rest) = (take n v, drop n v) in 
        fstN :: (incDim rest)
