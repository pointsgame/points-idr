module Points.Field

import Data.DPair
import Data.List
import Data.List1
import Data.SortedSet
import Data.Vect
import Points.Pos
import Points.Player
import Points.Point

record Field (width, height: Nat) where
  constructor MkField
  scoreRed, scoreBlack : Nat
  moves : List (Pos width height, Player)
  points : Vect (width * height) Point

point : {height: Nat} -> Field width height -> Pos width height -> Point
point field pos = index (toFin pos) $ points field

isPuttingAllowed : {height: Nat} -> Field width height -> Pos width height -> Bool
isPuttingAllowed field pos = Point.isPuttingAllowed $ point field pos

isPlayer : {height: Nat} -> Field width height -> Pos width height -> Player -> Bool
isPlayer field pos = Point.isPlayer $ point field pos

isPlayersPoint : {height: Nat} -> Field width height -> Pos width height -> Player -> Bool
isPlayersPoint field pos = Point.isPlayersPoint $ point field pos

isCapturedPoint : {height: Nat} -> Field width height -> Pos width height -> Player -> Bool
isCapturedPoint field pos = Point.isCapturedPoint $ point field pos

isEmptyBase : {height: Nat} -> Field width height -> Pos width height -> Player -> Bool
isEmptyBase field pos = Point.isEmptyBase $ point field pos

emptyField : (width: Nat) -> (height: Nat) -> Field width height
emptyField width height = MkField 0 0 [] $ replicate (width * height) EmptyPoint

wave : Pos width height -> (Pos width height -> Bool) -> SortedSet $ Pos width height
wave startPos f = wave' empty (singleton startPos)
  where neighborhood : Pos width height -> List $ Pos width height
        neighborhood pos = mapMaybe (map fst) $ n' pos ::
                                                s' pos ::
                                                w' pos ::
                                                e' pos ::
                                                []
        nextFront : SortedSet (Pos width height) -> SortedSet (Pos width height) -> SortedSet (Pos width height)
        nextFront passed front = difference (SortedSet.fromList $ filter f $ concatMap neighborhood (SortedSet.toList front)) passed
        wave' : SortedSet (Pos width height) -> SortedSet (Pos width height) -> SortedSet (Pos width height)
        wave' passed front = if null (SortedSet.toList front)
                             then passed
                             else wave' (union passed front) (nextFront passed front)

getInputPoints : {height: Nat} -> Field width height -> (pos : Pos width height) -> Player -> List ((Subset (Pos width height) (Adjacent pos)), (Subset (Pos width height) (Adjacent pos)))
getInputPoints field pos player =
  let isDirectionPlayer : ((pos : Pos width height) -> Maybe (Subset (Pos width height) (Adjacent pos))) -> Bool
      isDirectionPlayer dir = maybe False (\dirPos => isPlayer field (fst dirPos) player) $ dir pos
      list1 = if not $ isDirectionPlayer w' then
                if isDirectionPlayer nw' then toList (zip (nw' pos) (w' pos))
                else if isDirectionPlayer n' then toList (zip (n' pos) (w' pos))
                else []
              else
                []
      list2 = if not $ isDirectionPlayer s' then
                if isDirectionPlayer sw' then toList (zip (sw' pos) (s' pos)) ++ list1
                else if isDirectionPlayer w' then toList (zip (w' pos) (s' pos)) ++ list1
                else list1
              else
                list1
      list3 = if not $ isDirectionPlayer e' then
                if isDirectionPlayer se' then toList (zip (se' pos) (e' pos)) ++ list2
                else if isDirectionPlayer s' then toList (zip (s' pos) (e' pos)) ++ list2
                else list2
              else
                list2
      list4 = if not $ isDirectionPlayer n' then
                if isDirectionPlayer ne' then toList (zip (ne' pos) (n' pos)) ++ list3
                else if isDirectionPlayer e' then toList (zip (e' pos) (n' pos)) ++ list3
                else list3
              else
                list3
  in list4

square : List1 (Pos width height) -> Integer
square (pos ::: tail) = square' $ pos :: tail
  where skewProduct : Pos width height -> Pos width height -> Integer
        skewProduct (x1, y1) (x2, y2) = cast x1 * cast y2 - cast y1 * cast x2
        square' : List (Pos width height) -> Integer
        square' [] = 0
        square' (pos1 :: []) = skewProduct pos1 pos
        square' (pos1 :: pos2 :: tail) = skewProduct pos1 pos2 + square' (pos2 :: tail)

buildChain : {height: Nat} -> Field width height -> (startPos, nextPos: Pos width height) -> (0 _: Adjacent startPos nextPos) -> Player -> Maybe $ List1 $ Pos width height
buildChain field startPos nextPos adj player = if square chain < 0 then Just chain else Nothing
  where getNextPlayerPos : (pos: Pos width height) -> Direction -> Subset (Pos width height) (Adjacent pos)
        getNextPlayerPos centerPos dir = case directionToPos dir centerPos of
                                           Nothing => getNextPlayerPos centerPos $ rotate dir
                                           Just (Element pos adj) => if pos == startPos || isPlayer field pos player
                                                                     then Element pos adj
                                                                     else getNextPlayerPos centerPos $ rotate dir
        getChain : (startPos', nextPos': Pos width height) -> (0 _: Adjacent startPos' nextPos') -> List1 (Pos width height) -> List1 (Pos width height)
        getChain _ nextPos adj chain =
          let Element nextPos' nextAdj = getNextPlayerPos nextPos (rotateNotAdjacent (inverse (direction adj)))
          in if nextPos' == startPos
             then chain
             else getChain nextPos nextPos' nextAdj $ fromMaybe (cons nextPos' chain) $ List1.fromList $ dropWhile (/= nextPos') $ toList chain
        chain = getChain startPos nextPos adj $ cons nextPos $ startPos ::: []
