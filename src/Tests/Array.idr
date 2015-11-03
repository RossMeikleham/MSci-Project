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
             
 where arr : Array [3] Int
       arr = [27, 10, 2]



