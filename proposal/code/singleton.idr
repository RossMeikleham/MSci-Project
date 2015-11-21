singleton : Vector xs t -> 
            Vector (1::xs) t
singleton t = [t]

invSingleton : Vector (1::xs) t -> 
               Vector xs t
invSingleton [t] = t

