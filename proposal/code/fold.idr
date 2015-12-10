foldlA : (a -> b -> a) -> a -> Vector (x::xs) b -> a
foldlA f e v with (flattenA v)
   | (_ ** v') = foldlA' f e v'
     where foldlA' : (a -> b -> a) -> a -> Vector [(S ys)] b -> a
           foldlA' f e v = foldl f e v

