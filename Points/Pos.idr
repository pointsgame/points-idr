module Points.Pos

import Data.Fin

Pos : Nat -> Nat -> Type
Pos width height = (Fin width, Fin height)
