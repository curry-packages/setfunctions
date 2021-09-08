{-# OPTIONS_FRONTEND -Wno-overlapping #-}

import Control.SetFunctions

-- Place n queens on a chessboard so that no queen can capture another queen:
-- (this solution is due to Sergio Antoy)

queens :: [Int] -> [Int]
queens xs | isEmpty (set2 capture xs ys) = ys where ys = permute xs

permute :: [a] -> [a]
permute []     = []
permute (x:xs) = insX (permute xs)
 where insX ys     = x : ys
       insX (y:ys) = y : insX ys

capture :: [Int] -> [Int] -> Bool
capture xs ys
  | _ ++ [(x1,y1)] ++ _ ++ [(x2,y2)] ++ _ =:= zip xs ys &&
    (x1-y1 == x2-y2 || x1+y1 == x2+y2)
  = True
 where x1,x2,y1,y2 free


queens4 :: [Int]
queens4 = queens [1,2,3,4]

queens5 :: [Int]
queens5 = queens [1,2,3,4,5]
