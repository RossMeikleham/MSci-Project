module Tests.Array

import TypeTrans.Array
import Data.Vect

assertEq : Eq a => (given : a) -> (expected : a) -> IO ()
assertEq g e = if g == e
    then putStrLn "Test Passed"
    else putStrLn "Test Failed"

assertNotEq : Eq a => (given : a) -> (expected : a) -> IO ()
assertNotEq g e = if not (g == e)
    then putStrLn "Test Passed"
    else putStrLn "Test Failed"

assertTrue : Bool -> IO ()
assertTrue b = if b
                then putStrLn "Test Passed"
                else putStrLn "Test Failed"

assertFalse : Bool -> IO ()
assertFalse b = assertTrue (not b)


testRedDim : IO ()
testRedDim = assertEq (redDim arr) reducedArr

  where arr : Array [3, 3] Int
        arr = [[2,3,7], [4,2,6], [5,7,9]]

        reducedArr : Array [9] Int
        reducedArr = [2,3,7,4,2,6,5,7,9]

        

testIncDim : IO ()
testIncDim = assertEq (incDim arr) incArr

  where arr : Array [2 * 2] Int
        arr = [2, 3, 4, 5]

        incArr : Array [2,2] Int
        incArr = [[2, 3], [4, 5]]


testIncDimFactor : IO ()
testIncDimFactor = assertEq (incDim $ reshapeByFactor 3 arr) incArr
    
    where arr : Array [3] Int
          arr = [27, 10, 2]

          incArr : Array [3, 1] Int
          incArr = [[27], [10], [2]]


-- Test reducing dimensions, and then increasing
-- results in the same initial Array
testRedInc : IO ()
testRedInc = assertEq (incDim $ redDim arr') arr'
 
  where arr' : Array [3, 3] Int
        arr' = [[1,3,7], [4,2,6], [5,7,9]]


-- Test increasing dimensions and then reducing
-- results in the same initial Array
testIncRed : IO ()
testIncRed = assertEq (redDim $ incDim $ reshapeByFactor 3 arr) arr
             
 where 
       arr : Array [3] Int
       arr = [27, 10, 2]

{-
testIncFactors : IO ()
testIncFactors = do
    assertTrue res0

  where arr : Array [8] Int
        arr = [1, 2, 3, 4, 5, 6, 7, 8]
        
        arr0 : Array [1, 8] Int
        arr0 = [[1, 2, 3, 4, 5, 6, 7, 8]]

        res0 : Bool
        res0  with (splitNFactor 0 arr) 
                | (_ ** xs) = xs == arr0  
-}



testSplitting : IO ()
testSplitting = do 
                  printSplitArr
  where

    arr : Array [20] Int
    arr = [1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20];

    arr2 : (xs ** Array (1::xs) Int)
    arr2 = ([1,1] ** [[[1]]])

    liftArr : Array [S x] Int -> (xs ** Array ((S x)::xs) Int)
    liftArr vs = ([] ** vs)

    printSplitArr : IO()
    printSplitArr with  (liftArr arr)
      | (vs ** xs) = printArrs (splitFactorsGeneric xs) {t=Int} 

    test20 : Array (x::xs) t -> IO ()
    test20 a = print "todo"

    test10 : IO ()
    test10 with (arr2) 
      | (_ ** xs) = test20 xs
