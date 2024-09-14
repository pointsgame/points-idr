module Points.Player

import Derive.Prelude

%default total

%language ElabReflection

public export
data Player = Red | Black

%runElab derive "Player" [Show, Eq]

export
nextPlayer : Player -> Player
nextPlayer Red = Black
nextPlayer Black = Red
