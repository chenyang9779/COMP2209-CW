{-# LANGUAGE DeriveGeneric #-}
-- comp2209 Functional Programming Challenges
-- (c) University of Southampton 2022
-- Skeleton code to be updated with your solutions
-- The dummy functions here simply return an arbitrary value that is usually wrong 

-- DO NOT MODIFY THE FOLLOWING LINES OF CODE
module Challenges (Atoms,Interactions,Pos,EdgePos,Side(..),Marking(..),
                   LamExpr(..),ArithExpr(..),
                   calcBBInteractions,solveBB,prettyPrint,
                   parseArith,churchEnc,innerRedn1,innerArithRedn1,compareArithLam) where


-- Import standard library and parsing definitions from Hutton 2016, Chapter 13
import Data.Char
import Parsing
import Control.Monad
import Data.List
import GHC.Generics (Generic,Generic1)
import Control.DeepSeq
import Data.Function
import Data.Ord


-- Challenge 1
-- Calculate Interactions in the Black Box

type ListAtoms = [Atoms]
type Atoms = [ Pos ]
type Interactions = [  ( EdgePos , Marking )  ] 
type Pos = (Int, Int)   -- top left is (1,1) , bottom right is (N,N) where N is size of grid
type EdgePos = ( Side , Int ) -- int range is 1 to N where N is size of grid

data Side = North | East | South | West
            deriving (Show, Eq, Ord, Generic)

data Marking =  Absorb | Reflect | Path EdgePos
                deriving (Show, Eq)

northPath,southPath,eastPath,westPath :: Int -> Int -> Int -> Atoms
northPath a size start 
    |start == 0 = replicate size a `zip` [1 ..size]
    |otherwise = replicate size a `zip` [start..size]
southPath a size start 
    |start == 0 = replicate size a `zip` reverse [1..size]
    |otherwise = drop (size - start ) (replicate size a `zip` reverse [1..size])
eastPath a size start 
    |start == 0 = reverse [1 ..size] `zip` replicate size a
    |otherwise = drop (size - start) (reverse [1..size] `zip` replicate size a)
westPath a size start
    |start == 0 = [1..size] `zip` replicate size a
    |otherwise = [start ..size] `zip` replicate size a

testPath :: Pos -> Atoms -> Atoms -> Int
testPath (x,y) path allPoints
    |(x,y) `elem` path = 0
    |(x-1,y) `elem` path && (x-1,y) `elem` allPoints = 0
    |(x-1,y) `elem` path = 1--left 
    |(x+1,y) `elem` path && (x+1,y) `elem` allPoints = 0
    |(x+1,y) `elem` path = 2--right 
    |(x,y-1) `elem` path && (x,y-1) `elem` allPoints = 0
    |(x,y-1) `elem` path = 3--top 
    |(x,y+1) `elem` path && (x,y+1) `elem` allPoints = 0
    |(x,y+1) `elem` path = 4--down
    |otherwise = 5
    
testOneByOne' :: Int-> Atoms -> EdgePos -> Int-> EdgePos -> Atoms-> Interactions
testOneByOne' a [] (North,point) start startDir allPoints = [(startDir,Path (South,point))]
testOneByOne' a [] (South,point) start startDir allPoints = [(startDir,Path (North,point))]
testOneByOne' a [] (East,point) start startDir allPoints = [(startDir,Path (West,point))]
testOneByOne' a [] (West,point) start startDir allPoints = [(startDir,Path (East,point))]

testOneByOne :: Int-> Atoms-> EdgePos -> Int -> EdgePos -> Atoms -> Interactions
testOneByOne _ [] _ _ _ _ = []
testOneByOne size ((x,y):xs) (North,point) start startDir allPoints
    |result1 == 0 = [(startDir,Absorb)]
    |result1 == 1 && y == 1 = [(startDir,Reflect)]
    |result1 == 1 && (point-2) >= 1 = testOneByOne size (sortByDir allPoints East) (East,y-1) (point-1) startDir allPoints
    |result1 == 1 && (point-2) < 1 = [(startDir,Path (West,y-1))]
    |result1 == 2 && y == 1 = [(startDir,Reflect)]
    |result1 == 2 && (point+2) <= size = testOneByOne size (sortByDir allPoints West) (West,y-1) (point+1) startDir allPoints
    |result1 == 2 && (point+2) > size = [(startDir,Path (East,y-1))]
    |result1 == 5 && null xs = [(startDir,Path (South,point))]
    |otherwise = testOneByOne size xs (North,point) start startDir allPoints
        where result1 = testPath (x,y) (northPath point size start) allPoints
testOneByOne size ((x,y):xs) (South,point) start startDir allPoints
    |result2 == 0 = [(startDir,Absorb)]
    |result2 == 1 && y == size = [(startDir,Reflect)]
    |result2 == 1 && (x-2) >= 1 = testOneByOne size (sortByDir allPoints East) (East,y+1) (point-1) startDir allPoints
    |result2 == 1 && (x-2) < 1 = [(startDir,Path (West,y+1))]
    |result2 == 2 && y == size = [(startDir,Reflect)]
    |result2 == 2 && (x+2) <= size = testOneByOne size (sortByDir allPoints West) (West,y+1) (point+1) startDir allPoints
    |result2 == 2 && (x+2) > size = [(startDir,Path (East,y+1))]
    |result2 == 5 && null xs = [(startDir,Path (North,point))]
    |otherwise = testOneByOne size xs (South,point) start startDir allPoints
        where result2 = testPath (x,y) (southPath point size start) allPoints
testOneByOne size ((x,y):xs) (East,point) start startDir allPoints
    |result3 == 0 = [(startDir,Absorb)]
    |result3 == 3 && x == size = [(startDir,Reflect)]
    |result3 == 3 && (y-2) >= 1 = testOneByOne size (sortByDir allPoints South) (South,x+1) (point-1) startDir allPoints
    |result3 == 3 && (y-2) < 1 = [(startDir,Path (North,x+1))]
    |result3 == 4 && x == size = [(startDir,Reflect)]
    |result3 == 4 && (y+2) <= size = testOneByOne size (sortByDir allPoints North) (North,x+1) (point+1) startDir allPoints
    |result3 == 4 && (y+2) > size = [(startDir,Path (South,x+1))]
    |result3 == 5 && null xs = [(startDir,Path (West,point))]
    |otherwise = testOneByOne size xs (East,point) start startDir allPoints
        where result3 = testPath (x,y) (eastPath point size start) allPoints
testOneByOne size ((x,y):xs) (West,point) start startDir allPoints
    |result4 == 0 = [(startDir,Absorb)]
    |result4 == 3 && x == 1 = [(startDir,Reflect)]
    |result4 == 3 && (y-2) >= 1 = testOneByOne size (sortByDir allPoints South) (South,x-1) (point-1) startDir allPoints
    |result4 == 3 && (y-2) < 1 = [(startDir,Path (North,x-1))]
    |result4 == 4 && x == 1 = [(startDir,Reflect)]
    |result4 == 4 && (y+2) <= size = testOneByOne size (sortByDir allPoints North) (North,x-1) (point+1) startDir allPoints
    |result4 == 4 && (y+2) > size= [(startDir,Path (South,x-1))]
    |result4 == 5 && null xs = [(startDir,Path (East,point))]
    |otherwise = testOneByOne size xs (West,point) start startDir allPoints
        where result4 = testPath (x,y) (westPath point size start) allPoints

sortByDir :: Atoms -> Side -> Atoms 
sortByDir xs dir 
    |dir == North = sortBy (compare `on` snd) xs
    |dir == South = sortBy (flip compare `on` snd) xs
    |dir == East = sortBy (flip compare `on` fst) xs
    |dir == West = sortBy (compare `on` fst) xs

calcBBInteractions :: Int -> Atoms -> [EdgePos] -> Interactions
calcBBInteractions _ _ [] = []
calcBBInteractions size [] ((dir,point):xs) = testOneByOne' size (sortByDir [] dir) (dir,point) 0 (dir,point) [] ++ calcBBInteractions size [] xs
calcBBInteractions size points ((dir,point):xs) = testOneByOne size (sortByDir points dir) (dir,point) 0 (dir,point) points ++ calcBBInteractions size points xs

-- Challenge 2
-- Find atoms in a Black Box

createBoxPts :: Int ->  Atoms 
createBoxPts a = [(x,y)|x <- [1..a],y<- [1..a]]

createNoUsePts :: Int -> Interactions -> Atoms 
createNoUsePts a = concatMap (createNoUsePts' a)

createNoUsePts' :: Int -> ( EdgePos , Marking ) -> Atoms 
--createNoUsePts' _ _ = []
createNoUsePts' a ((North,x),Path (West,y)) 
    | x /= 1 && y /= 1 = replicate 2 (x-1) `zip` [1..2]
                      ++ replicate 3 x `zip` [1..3]
                      ++ replicate 2 (x+1) `zip` [1..2]
                      ++ [1..2] `zip` replicate 2 (y-1)     
                      ++ [1..2] `zip` replicate 2 (y+1)  
                      ++ [1..3] `zip` replicate 3 y 
    | x == 1 = replicate a 1 `zip` [1..(y+1)] ++  replicate a 2 `zip`  [1..y]
    | y == 1 = [1..(x+1)] `zip` replicate a 1 ++ [1..x] `zip` replicate a 2 
createNoUsePts' a ((North,x),Path (East,y)) 
    | x /= a && y /= 1 = replicate 2 (x-1) `zip` [1..2]
                      ++ replicate 3 x `zip` [1..3]
                      ++ replicate 2 (x+1) `zip` [1..2]   
                      ++ [a,a-1] `zip` replicate 2 (y-1)     
                      ++ [a,a-1] `zip` replicate 2 (y+1)  
                      ++ [a,a-1,a-2] `zip` replicate 3 y
    | x == a = replicate a a `zip` [1..(y+1)] ++  replicate a (a-1) `zip`  [1..y]
    | y == 1 = [(x-1)..a] `zip` replicate a 1 ++ [x..a] `zip` replicate a 2 
createNoUsePts' a ((South,x),Path (West,y)) 
    | x /= 1 && y /= a = replicate 2 (x-1) `zip` [a,a-1]
                      ++ replicate 3 x `zip` [a,a-1,a-2]
                      ++ replicate 2 (x+1) `zip` [a,a-1]  
                      ++ [1..2] `zip` replicate 2 (y-1)     
                      ++ [1..2] `zip` replicate 2 (y+1)  
                      ++ [1..3] `zip` replicate 3 y
    | x == 1 = replicate a 1 `zip` [(y-1)..a] ++ replicate a 2 `zip` [y..a]
    | y == a = [1..(x+1)] `zip` replicate a a ++ [1..x] `zip` replicate a (a-1)
createNoUsePts' a ((South,x),Path (East,y)) 
    | x /= a && y /= a = replicate 2 (x-1) `zip` [a,a-1]
                      ++ replicate 3 x `zip` [a,a-1,a-2]
                      ++ replicate 2 (x+1) `zip` [a,a-1]  
                      ++ [a,a-1] `zip` replicate 2 (y-1)     
                      ++ [a,a-1] `zip` replicate 2 (y+1)  
                      ++ [a,a-1,a-2] `zip` replicate 3 y 
    | x == a = replicate a a `zip` [(y-1)..a] ++ replicate a (a-1) `zip` [y..a]
    | y == a = [(x-1)..a] `zip` replicate a a ++ [x..a] `zip` replicate a (a-1)
createNoUsePts' a ((West,y),Path (North,x)) 
    | y /= 1 && x /= 1 = [1..2] `zip` replicate 2 (y-1)     
                      ++ [1..2] `zip` replicate 2 (y+1)  
                      ++ [1..3] `zip` replicate 3 y
                      ++ replicate 2 (x-1) `zip` [1..2]
                      ++ replicate 3 x `zip` [1..3]
                      ++ replicate 2 (x+1) `zip` [1..2]   
    | y == 1 = [1..(x+1)] `zip` replicate a 1 ++ [1..x] `zip` replicate a 2
    | x == 1 = replicate a 1 `zip` [1..(y+1)] ++ replicate a 1 `zip` [1..y]
createNoUsePts' a ((West,y),Path (South,x)) 
    | y /= a && x /= 1 = [1..2] `zip` replicate 2 (y-1)     
                      ++ [1..2] `zip` replicate 2 (y+1)  
                      ++ [1..3] `zip` replicate 3 y
                      ++ replicate 2 (x-1) `zip` [a,a-1]
                      ++ replicate 3 x `zip` [a,a-1,a-2]
                      ++ replicate 2 (x+1) `zip` [a,a-1]   
    | y == a = [1..(x+1)] `zip` replicate a a ++ [1..x] `zip` replicate a (a-1)
    | x == 1 = replicate a 1 `zip` [(y-1)..a] ++ replicate a 2 `zip` [y..a]
createNoUsePts' a ((East,y),Path (North,x)) 
    | y /= 1 && x /= a = [a,a-1] `zip` replicate 2 (y-1)     
                      ++ [a,a-1] `zip` replicate 2 (y+1)  
                      ++ [a,a-1,a-2] `zip` replicate 3 y
                      ++ replicate 2 (x-1) `zip` [1..2]
                      ++ replicate 3 x `zip` [1..3]
                      ++ replicate 2 (x+1) `zip` [1..2]  
    | y == 1 = [(x-1)..a] `zip` replicate a 1 ++ [x..a] `zip` replicate a 2
    | x == a = replicate a a `zip` [1..(y+1)] ++ replicate a (a-1) `zip` [1..y]
createNoUsePts' a ((East,y),Path (South,x)) 
    | y /= a && x /= a = [a,a-1] `zip` replicate 2 (y-1)     
                      ++ [a,a-1,a-2] `zip` replicate 2 (y+1)  
                      ++ [1..3] `zip` replicate 3 y
                      ++ replicate 2 (x-1) `zip` [a,a-1]
                      ++ replicate 3 x `zip` [a,a-1,a-2]
                      ++ replicate 2 (x+1) `zip` [a,a-1]  
    | y == a = [(x-1)..a] `zip` replicate a a ++ [x..a] `zip` replicate a (a-1)
    | x == a = replicate a a `zip` [(y-1)..a] ++ replicate a a `zip` [y..a]  
createNoUsePts' a ((North,x1),Path (South,x2)) 
    | x1 == x2 && x1 == 1 = replicate a 1 `zip` [1..a] ++ replicate a 2 `zip` [1..a]
    | x1 == x2 && x1 == a = replicate a a `zip` [1..a] ++ replicate a (a-1) `zip` [1..a]
    | otherwise = replicate 2 (x1-1) `zip` [1..2]
               ++ replicate 3 x1 `zip` [1..3]
               ++ replicate 2 (x1+1) `zip` [1..2]
               ++ replicate 2 (x2-1) `zip` [a,a-1]
               ++ replicate 3 x2 `zip` [a,a-1,a-2]
               ++ replicate 2 (x2+1) `zip` [a,a-1]     
createNoUsePts' a ((South,x1),Path (North,x2)) 
    | x1 == x2 && x1 == 1 = replicate a 1 `zip` [1..a] ++ replicate a 2 `zip` [1..a]
    | x1 == x2 && x1 == a = replicate a a `zip` [1..a] ++ replicate a (a-1) `zip` [1..a]
    | otherwise = replicate 2 (x1-1) `zip` [a,a-1]
              ++ replicate 3 x1 `zip` [a,a-1,a-2]
              ++ replicate 2 (x1+1) `zip` [a,a-1]
              ++ replicate 2 (x2-1) `zip` [1..2]
              ++ replicate 3 x2 `zip` [1..3]
              ++ replicate 2 (x2+1) `zip` [1..2]
createNoUsePts' a ((West,y1),Path (East,y2))
    | y1 == y2 && y1 == 1 = [1..a] `zip` replicate a 1 ++ [1..a] `zip` replicate a 2
    | y1 == y2 && y1 == 1 = [1..a] `zip` replicate a a ++ [1..a] `zip` replicate a (a-1)
    | otherwise = [1..2] `zip` replicate 2 (y1-1)
               ++ [1..2] `zip` replicate 2 (y1+1)
               ++ [1..3] `zip` replicate 3 y1 
               ++ [a,a-1] `zip` replicate 2 (y2-1)
               ++ [a,a-1] `zip` replicate 2 (y2+1)
               ++ [a,a-1,a-2] `zip` replicate 3 y2
createNoUsePts' a ((East,y1),Path (West,y2))
    | y1 == y2 && y1 == 1 = [1..a] `zip` replicate a 1 ++ [1..a] `zip` replicate a 2
    | y1 == y2 && y1 == 1 = [1..a] `zip` replicate a a ++ [1..a] `zip` replicate a (a-1)
    | otherwise = [a,a-1] `zip` replicate 2 (y1-1)
               ++ [a,a-1] `zip` replicate 2 (y1+1)
               ++ [a,a-1,a-2] `zip` replicate 3 y1
               ++ [1..2] `zip` replicate 2 (y2-1)
               ++ [1..2] `zip` replicate 2 (y2+1)
               ++ [1..3] `zip` replicate 3 y2
createNoUsePts' a ((North,x1),Path (North,x2))
    | x1 < x2 = [(x1-1,1),(x1+1,1),(x1,1),(x1,2),(x1+1,2)] ++ [(x2-1,1),(x2,1),(x2+1,1),(x2-1,2),(x2,2)]
    | x1 > x2 = [(x1-1,1),(x1+1,1),(x1,1),(x1-1,2),(x1,2)] ++ [(x2-1,1),(x2,1),(x2+1,1),(x2+1,2),(x2,2)]
createNoUsePts' a ((South,x1),Path (South,x2))
    | x1 < x2 = [(x1-1,a),(x1+1,a),(x1,a),(x1,a-1),(x1+1,a-1)] ++ [(x2-1,a),(x2+1,a),(x2,a),(x2-1,a-1),(x2,a-1)]
    | x1 > x2 = [(x1-1,a),(x1+1,a),(x1,a),(x1-1,a-1),(x1,a-1)] ++ [(x2-1,a),(x2+1,a),(x2,a),(x2+1,a-1),(x2,a-1)]
createNoUsePts' a ((East,y1),Path (East,y2))
    | y1 < y2 = [(a,y1+1),(a,y1-1),(a,y1),(a-1,y1),(a-1,y1+1)] ++ [(a,y2+1),(a,y2-1),(a,y2),(a-1,y2),(a-1,y2-1)]
    | y1 > y2 = [(a,y1+1),(a,y1-1),(a,y1),(a-1,y1),(a-1,y1-1)] ++ [(a,y2+1),(a,y2-1),(a,y2),(a-1,y2),(a-1,y2+1)]
createNoUsePts' a ((West,y1),Path (West,y2))
    | y1 < y2 = [(1,y1+1),(1,y1-1),(1,y1),(2,y1),(2,y1+1)] ++ [(1,y2+1),(1,y2-1),(1,y2),(2,y2),(2,y2-1)]
    | y1 > y2 = [(1,y1+1),(1,y1-1),(1,y1),(2,y1),(2,y1-1)] ++ [(1,y2+1),(1,y2-1),(1,y2),(2,y2),(2,y2+1)]
createNoUsePts' a ((North,x),Reflect) = [(x,1)]
createNoUsePts' a ((South,x),Reflect) = [(x,a)]
createNoUsePts' a ((West,y),Reflect) = [(1,y)]
createNoUsePts' a ((East,y),Reflect) = [(a,y)]
createNoUsePts' a (_,Absorb) = []

subsequencesOfSize :: Int -> Atoms -> ListAtoms
subsequencesOfSize n xs = let l = length xs
                          in if n>l then [] else subsequencesBySize xs !! (l-n)
 where
   subsequencesBySize [] = [[[]]]
   subsequencesBySize (x:xs) = let next = subsequencesBySize xs
                             in zipWith (++) ([]:next) (map (map (x:)) next ++ [[]])

getPoints :: Int -> Interactions -> Atoms
getPoints a interactions = createBoxPts a \\ createNoUsePts a interactions

getSet :: Int -> Int -> Interactions -> ListAtoms
getSet a num interactions = subsequencesOfSize num (getPoints a interactions)

testAtoms :: Int -> ListAtoms -> Int -> Interactions -> Atoms
testAtoms a [] num interactions = testAtoms a (getSet a (num+1) interactions) (num+1) interactions
testAtoms a (x:xs) num interactions 
    |testResults results interactions = x
    |otherwise = testAtoms a xs num interactions
        where results = calcBBInteractions a x (map fst interactions)

testResults :: Interactions -> Interactions -> Bool
testResults x y = null (x \\ y) 

--returnPt enterPt wholeRt points 
solveBB :: Int -> Interactions -> Atoms 
solveBB a interactions = testAtoms a (getSet a 1 interactions) 1 interactions
--    | null (calcBBInteractions a [] (map fst interactions)) = []
 --   | otherwise = testAtoms a (getSet a 1 interactions) 1 interactions

-- Challenge 3
-- Pretty Printing Lambda with Alpha-Normalisation 

data LamExpr =  LamApp LamExpr LamExpr  |  LamAbs Int LamExpr  |  LamVar Int 
                deriving (Eq, Show, Read)

prettyPrint :: LamExpr -> String
prettyPrint expr 
    | findFirstFalse list /= -1 = prettyPrint' (rePrettyPrint alphaNorm list [])
    | otherwise = prettyPrint' alphaNorm
    where alphaNorm = alphaNormalize expr (findFreeVar expr [])
          list = findBounded alphaNorm []

prettyPrint' :: LamExpr -> String
prettyPrint' (LamApp (LamVar e1) (LamApp e2 e3)) =  prettyPrint' (LamVar e1) ++ " " ++ "(" ++ prettyPrint' (LamApp e2 e3) ++ ")"
prettyPrint' (LamApp (LamVar e1) e2) =  prettyPrint' (LamVar e1) ++ " " ++ prettyPrint' e2 
prettyPrint' (LamApp (LamAbs e1 e2) (LamApp e3 e4)) = "(" ++ prettyPrint' (LamAbs e1 e2) ++ ")" ++ " " ++ "(" ++ prettyPrint' (LamApp e3 e4) ++ ")"
prettyPrint' (LamApp (LamAbs e1 e2) e3) = "(" ++ prettyPrint' (LamAbs e1 e2) ++ ")" ++ " " ++ prettyPrint' e3 
prettyPrint' (LamApp e1 (LamApp e2 e3)) =  prettyPrint' e1 ++ " " ++ "(" ++ prettyPrint' (LamApp e2 e3) ++ ")"
prettyPrint' (LamApp e1 e2) =  prettyPrint e1 ++ " " ++ prettyPrint e2 
prettyPrint' (LamAbs i e) = "\\x" ++ show i ++ " -> " ++ prettyPrint' e
prettyPrint' (LamVar i) = "x" ++ show i

alphaNormalize :: LamExpr -> [(Int, Int)] -> LamExpr
alphaNormalize t env = go t env
  where
    go :: LamExpr -> [(Int, Int)] -> LamExpr
    go (LamVar x) env =
      case lookup x env of
        Just y  -> LamVar y
        Nothing -> LamVar x
    go (LamAbs x t1) env 
        | search' x env = LamAbs (search x env) t3
        | otherwise = LamAbs y t2
            where
                y = freshVar env
                t2 = go t1 ((x, y) : env)
                t3 = go t1 env
    go (LamApp t1 t2) env = LamApp (go t1 env) (go t2 env)

    freshVar :: [(Int, Int)] -> Int
    freshVar env = head (filter (\y -> y `notElem` map snd env) [0..])

findFreeVar :: LamExpr -> [Int] -> [(Int, Int)]
findFreeVar (LamVar a) list
    | a `notElem` list = [(a,a)]
    | otherwise = []
findFreeVar (LamAbs a e1) list = findFreeVar e1 (a:list) 
findFreeVar (LamApp e1 e2) list = findFreeVar e1 list  ++ findFreeVar e2 list 

rePrettyPrint :: LamExpr -> [(Int, Bool)] -> [(Int,Int)] -> LamExpr
rePrettyPrint (LamVar a) list env = 
                case lookup a env of 
                Just y  -> LamVar y
                Nothing -> LamVar a
rePrettyPrint (LamAbs a e1) list env
    |testElem a list && a > findFirstFalse list = LamAbs (findFirstFalse list) (rePrettyPrint e1 (replaceList (findFirstFalse list) list) ((a,findFirstFalse list):env))
    |testElem a list && a < findFirstFalse list = LamAbs a (rePrettyPrint e1 list ((a,a):env))
    |not (testElem a list) = LamAbs (findFirstFalse list) (rePrettyPrint e1 list env)
rePrettyPrint (LamApp e1 e2) list env = LamApp (rePrettyPrint e1 list env) (rePrettyPrint e2 list env)

findBounded :: LamExpr -> [(Int, Bool)] -> [(Int, Bool)]
findBounded (LamVar a) list 
    | checkList a list = sortBy (comparing fst) (replaceList a list)
    | otherwise = sortBy (comparing fst) ((a,True):list)
findBounded (LamAbs a e1) list 
    |checkList a list = findBounded e1 list
    |otherwise = findBounded e1 ((a,False):list)
findBounded (LamApp e1 e2) list = findBounded e2 (findBounded e1 list)

findFirstFalse :: [(Int, Bool)] -> Int
findFirstFalse [] = -1
findFirstFalse (x:xs)
    | snd x = findFirstFalse xs
    | otherwise = fst x

testElem :: Eq t => t -> [(t, b)] -> b
testElem a (x:xs)
    | a == fst x = snd x
    | otherwise = testElem a xs

checkList :: Eq t => t -> [(t, b)] -> Bool
checkList _ [] = False
checkList a (x:xs) 
    | a == fst x = True
    | otherwise = checkList a xs

replaceList :: Eq t => t -> [(t, Bool)] -> [(t, Bool)]
replaceList a (x:xs) 
    | a == fst x = (a,True):xs
    | otherwise = x : replaceList a xs
 
search' :: Int -> [(Int, Int)] -> Bool
search' x [] = False
search' x (y:ys) 
    | x == fst y = True
    | otherwise = search' x ys

search :: Int -> [(Int, Int)] -> Int
search x (y:ys) 
    | x == fst y = snd y
    | otherwise = search x ys

-- Challenge 4 
-- Parsing Arithmetic Expressions

data ArithExpr = Add ArithExpr ArithExpr | Mul ArithExpr ArithExpr 
               | Section ArithExpr  | SecApp ArithExpr ArithExpr | ArithNum Int
    deriving (Show,Eq,Read) 

expr :: Parser ArithExpr
expr = do
    e1 <- expr1
    (do
        symbol "+"
        Add e1 <$> expr) <|> return e1

expr1 :: Parser ArithExpr
expr1 = do
    e2 <- expr2
    (do
        symbol "*"
        Mul e2 <$> expr1) <|> return e2

expr2 :: Parser ArithExpr
expr2 = do
    (do
        symbol "("
        e <- expr
        symbol ")"
        return e) <|> (do
            symbol "("
            symbol "+"
            e <- expr
            symbol ")"
            SecApp (Section e) <$> expr2) <|> (do
                ArithNum <$> natural)

parseArith :: String -> Maybe ArithExpr
parseArith s = case parse expr s of
    [(e, "")] -> Just e
    _ -> Nothing

-- Challenge 5
-- Church Encoding of arithmetic 

churchEnc :: ArithExpr -> LamExpr 
churchEnc _ = undefined

-- Challenge 6
-- Compare Innermost Reduction for Arithmetic and its Church Encoding

innerRedn1 :: LamExpr -> Maybe LamExpr
innerRedn1 _ = undefined

innerArithRedn1 :: ArithExpr -> Maybe ArithExpr
innerArithRedn1 _ = undefined

compareArithLam :: ArithExpr -> (Int,Int)
compareArithLam _ = undefined

