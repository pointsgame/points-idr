module Points.Point

import Derive.Prelude
import Points.Player

%default total

%language ElabReflection

public export
data Point : Type where
  EmptyPoint : Point
  PlayerPoint : Player -> Point
  BasePoint : Player -> Bool -> Point
  EmptyBasePoint : Player -> Point

%runElab derive "Point" [Show, Eq]

isPuttingAllowed : Point -> Bool
isPuttingAllowed EmptyPoint = True
isPuttingAllowed (EmptyBasePoint _) = True
isPuttingAllowed _ = False

isPlayer : Point -> Player -> Bool
isPlayer (PlayerPoint p) player = p == player
isPlayer (BasePoint p _) player = p == player
isPlayer _ _ = False

isPlayersPoint : Point -> Player -> Bool
isPlayersPoint point player = point == PlayerPoint player

isCapturedPoint : Point -> Player -> Bool
isCapturedPoint point player = point == BasePoint (nextPlayer player) True
