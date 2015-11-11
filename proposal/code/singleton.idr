singleton : Vector [] t -> Vector [1] t
singleton t = [t]

invSingleton : Vector [1] t -> Vector [] t
invSingleton [t] = t

