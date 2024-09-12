module Points.Player

import Derive.Prelude

%language ElabReflection

data Player = Red | Black

%runElab derive "Player" [Show, Eq]
