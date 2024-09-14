module Points.Field

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
