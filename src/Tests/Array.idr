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

  where arr : Vect 3 (Vect 3 Int)
        arr = [[2,3,7], [4,2,6], [5,7,9]]

        reducedArr : Array [9] Int
        reducedArr = [2,3,7,4,2,6,5,7,9]

        

testIncDim : IO ()
testIncDim = assertEq (incDim arr) incArr

  where arr : Vect (2 * 2) Int
        arr = [2, 3, 4, 5]

        incArr : Array [2,2] Int
        incArr = [[2, 3], [4, 5]]


testIncDimFactor : IO ()
testIncDimFactor = assertEq (incDim $ reshapeByFactor 3 arr) incArr
    
    where arr : Array [3] Int
          arr = [27, 10, 2]

          incArr : Array [3, 1] Int
          incArr = [[27], [10], [2]]

          --test : Array [3 * 1] Int
          --test = reshapeByFactor 3 arr      

          --test2' : Array [3, 1] Int
          --test2' = incDim $ reshapeByFactor 3 arr


testIncRed : IO ()
testIncRed = assertEq 2 2 -- (redDim $ incDim arr) arr

 where arr : Array [3 * 1] Int
       arr = [27, 10, 2]

