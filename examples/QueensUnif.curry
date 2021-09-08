import Control.SetFunctions

-- Place n queens on a chessboard so that no queen can capture another queen:
-- (this solution is due to Sergio Antoy)

queens :: [Int] -> [Int]
queens xs | ys =:= permute xs && isEmpty (set2 capture xs ys) = ys where ys free

permute :: (Data a, Eq a) => [a] -> [a]
permute []     = []
permute (x:xs) | u ++ v =:= permute xs  = u ++ [x] ++ v
 where u,v free

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
