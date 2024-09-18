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

export
isPuttingAllowed : Point -> Bool
isPuttingAllowed EmptyPoint = True
isPuttingAllowed (EmptyBasePoint _) = True
isPuttingAllowed _ = False

export
isPlayer : Point -> Player -> Bool
isPlayer (PlayerPoint p) player = p == player
isPlayer (BasePoint p _) player = p == player
isPlayer _ _ = False

export
isPlayersPoint : Point -> Player -> Bool
isPlayersPoint point player = point == PlayerPoint player

export
isCapturedPoint : Point -> Player -> Bool
isCapturedPoint point player = point == BasePoint (nextPlayer player) True

export
isEmptyBase : Point -> Player -> Bool
isEmptyBase point player = point == Point.EmptyBasePoint player

export
capture : Player -> Point -> Point
capture player EmptyPoint = BasePoint player False
capture player (PlayerPoint player') = if player' == player
                                       then PlayerPoint player'
                                       else BasePoint player True
capture player (BasePoint player' enemy) = if player' == player
                                           then BasePoint player' enemy
                                           else if enemy
                                           then PlayerPoint player
                                           else BasePoint player False
capture player (EmptyBasePoint _) = BasePoint player False
