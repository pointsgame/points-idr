module Points.Pos

import Data.Fin
import Data.Fin.Extra

%default total

public export
Pos : Nat -> Nat -> Type
Pos width height = (Fin width, Fin height)

export
toFin : {width, height: Nat} -> Pos width height -> Fin (width * height)
toFin (x, y) = indexProd x y

AdjacentRight : Pos width height -> Pos width height -> Type
AdjacentRight (x1, y1) (x2, y2) = (FS x1 = weaken x2, y1 = y2)

AdjacentBottom : Pos width height -> Pos width height -> Type
AdjacentBottom (x1, y1) (x2, y2) = (x1 = x2, FS y1 = weaken y2)

AdjacentBottomRight : Pos width height -> Pos width height -> Type
AdjacentBottomRight (x1, y1) (x2, y2) = (FS x1 = weaken x2, FS y1 = weaken y2)

AdjacentTopRight : Pos width height -> Pos width height -> Type
AdjacentTopRight (x1, y1) (x2, y2) = (FS x1 = weaken x2, weaken y1 = FS y2)

AdjacentLeft : Pos width height -> Pos width height -> Type
AdjacentLeft pos1 pos2 = AdjacentRight pos2 pos1

AdjacentTop : Pos width height -> Pos width height -> Type
AdjacentTop pos1 pos2 = AdjacentBottom pos2 pos1

AdjacentTopLeft : Pos width height -> Pos width height -> Type
AdjacentTopLeft pos1 pos2 = AdjacentBottomRight pos2 pos1

AdjacentBottomLeft : Pos width height -> Pos width height -> Type
AdjacentBottomLeft pos1 pos2 = AdjacentTopRight pos2 pos1

data Adjacent : Pos width height -> Pos width height -> Type where
  AdjRight : AdjacentRight pos1 pos2 -> Adjacent pos1 pos2
  AdjLeft : AdjacentLeft pos1 pos2 -> Adjacent pos1 pos2
  AdjBottom : AdjacentBottom pos1 pos2 -> Adjacent pos1 pos2
  AdjTop : AdjacentTop pos1 pos2 -> Adjacent pos1 pos2
  AdjBottomRight: AdjacentBottomRight pos1 pos2 -> Adjacent pos1 pos2
  AdjTopLeft : AdjacentTopLeft pos1 pos2 -> Adjacent pos1 pos2
  AdjTopRight : AdjacentTopRight pos1 pos2 -> Adjacent pos1 pos2
  AdjBottomLeft : AdjacentBottomLeft pos1 pos2 -> Adjacent pos1 pos2

adjacentSymm : Adjacent pos1 pos2 -> Adjacent pos2 pos1
adjacentSymm (AdjRight adj) = AdjLeft adj
adjacentSymm (AdjLeft adj) = AdjRight adj
adjacentSymm (AdjBottom adj) = AdjTop adj
adjacentSymm (AdjTop adj) = AdjBottom adj
adjacentSymm (AdjBottomRight adj) = AdjTopLeft adj
adjacentSymm (AdjTopLeft adj) = AdjBottomRight adj
adjacentSymm (AdjTopRight adj) = AdjBottomLeft adj
adjacentSymm (AdjBottomLeft adj) = AdjTopRight adj

adjacentToBottomRight : AdjacentRight pos1 pos2 -> AdjacentBottom pos2 pos3 -> AdjacentBottomRight pos1 pos3
adjacentToBottomRight {pos1 = (_, _), pos2 = (_, _), pos3 = (_, _)} adjR adjB = (rewrite sym $ fst adjB in fst adjR, rewrite snd adjR in snd adjB)

adjacentToTopRight : AdjacentRight pos1 pos2 -> AdjacentTop pos2 pos3 -> AdjacentTopRight pos1 pos3
adjacentToTopRight {pos1 = (_, _), pos2 = (_, _), pos3 = (_, _)} adjR adjT = (rewrite fst adjT in fst adjR, rewrite snd adjR in sym $ snd adjT)

export
n : (pos1: Pos width height) -> Maybe (pos2: Pos width height ** AdjacentTop pos1 pos2)
n (x, FZ) = Nothing
n (x, FS y) = Just ((x, weaken y) ** (Refl, Refl))

export
s : (pos1: Pos width height) -> Maybe (pos2 ** AdjacentBottom pos1 pos2)
s {height = S Z} (x, FZ) = Nothing
s {height = S (S _)} (x, FZ) = Just ((x, FS FZ) ** (Refl, Refl))
s (x, FS y) = map (\((x1, y1) ** adj) => ((x1, FS y1) ** (fst adj, cong FS (snd adj)))) $ s (x, y)

export
w : (pos1: Pos width height) -> Maybe (pos2: Pos width height ** AdjacentLeft pos1 pos2)
w (FZ, x) = Nothing
w (FS x, y) = Just ((weaken x, y) ** (Refl, Refl))

export
e : (pos1: Pos width height) -> Maybe (pos2 ** AdjacentRight pos1 pos2)
e {width = S Z} (FZ, y) = Nothing
e {width = S (S _)} (FZ, y) = Just ((FS FZ, y) ** (Refl, Refl))
e (FS x, y) = map (\((x1, y1) ** adj) => ((FS x1, y1) ** (cong FS (fst adj), snd adj))) $ e (x, y)

export
nw : (pos1 : Pos width height) -> Maybe (pos2 ** AdjacentTopLeft pos1 pos2)
nw pos = do
  (npos ** adj1) <- n pos
  (nwpos ** adj2) <- w npos
  pure (nwpos ** adjacentToBottomRight adj2 adj1)

export
ne : (pos1: Pos width height) -> Maybe (pos2 ** AdjacentTopRight pos1 pos2)
ne pos = do
  (epos ** adj1) <- e pos
  (nepos ** adj2) <- n epos
  pure (nepos ** adjacentToTopRight adj1 adj2)

export
sw : (pos1: Pos width height) -> Maybe (pos2 ** AdjacentBottomLeft pos1 pos2)
sw pos = do
  (spos ** adj1) <- s pos
  (swpos ** adj2) <- w spos
  pure (swpos ** adjacentToTopRight adj2 adj1)

export
se : (pos1: Pos width height) -> Maybe (pos2 ** AdjacentBottomRight pos1 pos2)
se pos = do
  (epos ** adj1) <- e pos
  (sepos ** adj2) <- s epos
  pure (sepos ** adjacentToBottomRight adj1 adj2)

export
n' : (pos1: Pos width height) -> Maybe (pos2: Pos width height ** Adjacent pos1 pos2)
n' pos1 = map (\(pos2 ** adj) => (pos2 ** AdjTop adj)) $ n pos1

export
s' : (pos1: Pos width height) -> Maybe (pos2: Pos width height ** Adjacent pos1 pos2)
s' pos1 = map (\(pos2 ** adj) => (pos2 ** AdjBottom adj)) $ s pos1

export
w' : (pos1: Pos width height) -> Maybe (pos2: Pos width height ** Adjacent pos1 pos2)
w' pos1 = map (\(pos2 ** adj) => (pos2 ** AdjLeft adj)) $ w pos1

export
e' : (pos1: Pos width height) -> Maybe (pos2: Pos width height ** Adjacent pos1 pos2)
e' pos1 = map (\(pos2 ** adj) => (pos2 ** AdjRight adj)) $ e pos1

export
nw' : (pos1: Pos width height) -> Maybe (pos2: Pos width height ** Adjacent pos1 pos2)
nw' pos1 = map (\(pos2 ** adj) => (pos2 ** AdjTopLeft adj)) $ nw pos1

export
ne' : (pos1: Pos width height) -> Maybe (pos2: Pos width height ** Adjacent pos1 pos2)
ne' pos1 = map (\(pos2 ** adj) => (pos2 ** AdjTopRight adj)) $ ne pos1

export
sw' : (pos1: Pos width height) -> Maybe (pos2: Pos width height ** Adjacent pos1 pos2)
sw' pos1 = map (\(pos2 ** adj) => (pos2 ** AdjBottomLeft adj)) $ sw pos1

export
se' : (pos1: Pos width height) -> Maybe (pos2: Pos width height ** Adjacent pos1 pos2)
se' pos1 = map (\(pos2 ** adj) => (pos2 ** AdjBottomRight adj)) $ se pos1
