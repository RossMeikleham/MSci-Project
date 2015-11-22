mapV : (a -> b) -> Vector xs a -> 
                   Vector xs b
mapV f v {xs=[]}  = f v
mapV f v {xs = (y::ys)} = map (mapV f) v
