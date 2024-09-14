module Points.Field

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
