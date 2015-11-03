# MSci-Project
Exploring type transformations on vectors for generating code which can be run on FPGAs


[![Build Status](https://travis-ci.org/RossMeikleham/MSci-Project.svg?branch=master)](https://travis-ci.org/RossMeikleham/MSci-Project)

#Overview
This project explores using properties of vector types along with operations such as map, fold, and zip
on vectors to generate code to be run on a FPGA. We also aim to utilize the parallelism of operations
such as map and fold (when a fold operation is applied with an associative function) on these vectors.

We aim to implement an EDSL which generates multiple equivalent by construction programs that are run through
a cost model, the program with the best cost model is then to be selected to be streamed to a FPGA.

Even though better performance is likely to come from parallelizing operations as much as possible; the
circuits that need to be generated to support the specified parallelization may be too large to 
fit onto the specified FPGA. This is one of the main reasons we use a cost model to select the
program to use.

#Dependent Types
Dependent types allow for powerful compile time guarantees and proof checking, this project is implemented 
in a purely functional programming language with depdent types called [Idris](http://www.idris-lang.org/).

For example in a dependently typed functional language a list with length (called a Vect) in Idris, a function
taking a Vect as one of its arguments can look like the following:

```{Idris}
fn : Vect 5 Int -> Int
```
The length of the Vect is defined at the type level as the value 5. Idris enforces that Vects passed to this function 
must have exactly 5 elements, otherwise a compile time error is generated.  


```{Idris}
append : a -> Vect n a -> Vect (n + 1) a
```

This append function can take a Vect of any length, but it guarantees that the Vect returned has exactly
1 more element than the Vect passed in. If the implementation of this append function doesn't do this
then a compile time error is thrown. 

For vector transformations we use dependent types to guarantee our transformations are correct at compile time, rather
than waiting for a runtime error.

For example if we wanted to merge a 2 dimensional Vector into a single dimensional Vector; in a purely 
functional language such as Haskell we could express this in terms of lists as the following:

```{Haskell}
merge :: [[a]] -> Maybe [a]
merge [] = Just []
merge v@(x:xs) = 
  let fstLen = length x in
    -- Check if all inner lists are of the same length
    if all (\y -> fstLen == length y) xs
      then Just $ concat v 
      else Nothing
```
There is one major problem with this implementation in that lists within lists don't all have to be
the same size. (e.g. [[1],[1,2,4]] is a valid list of lists) and for a merge operation we require that the dimensionality of the lists
passed in is "rectangular" (sized m * n). This property needs to be checked at runtime before we can apply
the operation. On top of this in the case that the dimensionality property fails this needs to be taken care of in the 
program implementation itself either by throwing an error directly from the function or returning a value of 
`Maybe` or `Either` type which then needs to be unwrapped by the calling function. 


We can use Vects in Idris to solve this problem:

```{Idris}
merge : Vect m (Vect n a) -> Vect (n * m) a
merge [] = []
merge (x::xs) = x ++ merge xs
```

From Idris we can guarantee at compile time that the merge function is supplied by a "rectangular" list of m * n elements.
We can also guarantee that the size of the list that is returned is the dimensionality of the outer list
multiplied by the dimensionality of the inner list.


#Code

##Required
- Idris 0.9.19 Can be installed from [Hackage](https://hackage.haskell.org/package/idris-0.9.19) using cabal or
  on OSX through the Homebrew package manager.

##Building
- Building the code can be achieved by entering the command `idris --build project.ipkg` in the root directory
  of this repository
  
##Running Unit Tests
- Running unit tests can be achieved by entering the command `idris --testpkg project.ipkg` in the root directory
  of this repository
