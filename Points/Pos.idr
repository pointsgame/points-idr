module Points.Pos

import Data.DPair
import Data.Fin
import Data.Fin.Extra
import Decidable.Equality.Core

%default total

public export
Pos : Nat -> Nat -> Type
Pos width height = (Fin width, Fin height)

export
toFin : {height: Nat} -> Pos width height -> Fin (width * height)
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

decAdjacentRight : (pos1, pos2: Pos width height) -> Dec $ AdjacentRight pos1 pos2
decAdjacentRight {pos1 = (x1, y1)} {pos2 = (x2, y2)} with (decEq (FS x1) (weaken x2)) | (decEq y1 y2)
  _ | Yes p1 | Yes p2 = Yes (p1, p2)
  _ | No p1 | _ = No $ \(p2, _) => void $ p1 p2
  _ | _ | No p1 = No $ \(_, p2) => void $ p1 p2

decAdjacentBottom : (pos1, pos2: Pos width height) -> Dec $ AdjacentBottom pos1 pos2
decAdjacentBottom {pos1 = (x1, y1)} {pos2 = (x2, y2)} with (decEq x1 x2) | (decEq (FS y1) (weaken y2))
  _ | Yes p1 | Yes p2 = Yes (p1, p2)
  _ | No p1 | _ = No $ \(p2, _) => void $ p1 p2
  _ | _ | No p1 = No $ \(_, p2) => void $ p1 p2

decAdjacentBottomRight : (pos1, pos2: Pos width height) -> Dec $ AdjacentBottomRight pos1 pos2
decAdjacentBottomRight {pos1 = (x1, y1)} {pos2 = (x2, y2)} with (decEq (FS x1) (weaken x2)) | (decEq (FS y1) (weaken y2))
  _ | Yes p1 | Yes p2 = Yes (p1, p2)
  _ | No p1 | _ = No $ \(p2, _) => void $ p1 p2
  _ | _ | No p1 = No $ \(_, p2) => void $ p1 p2

decAdjacentTopRight : (pos1, pos2: Pos width height) -> Dec $ AdjacentTopRight pos1 pos2
decAdjacentTopRight {pos1 = (x1, y1)} {pos2 = (x2, y2)} with (decEq (FS x1) (weaken x2)) | (decEq (weaken y1) (FS y2))
  _ | Yes p1 | Yes p2 = Yes (p1, p2)
  _ | No p1 | _ = No $ \(p2, _) => void $ p1 p2
  _ | _ | No p1 = No $ \(_, p2) => void $ p1 p2

decAdjacentLeft : (pos1, pos2: Pos width height) -> Dec $ AdjacentLeft pos1 pos2
decAdjacentLeft pos1 pos2 = decAdjacentRight pos2 pos1

decAdjacentTop : (pos1, pos2: Pos width height) -> Dec $ AdjacentTop pos1 pos2
decAdjacentTop pos1 pos2 = decAdjacentBottom pos2 pos1

decAdjacentTopLeft : (pos1, pos2: Pos width height) -> Dec $ AdjacentTopLeft pos1 pos2
decAdjacentTopLeft pos1 pos2 = decAdjacentBottomRight pos2 pos1

decAdjacentBottomLeft : (pos1, pos2: Pos width height) -> Dec $ AdjacentBottomLeft pos1 pos2
decAdjacentBottomLeft pos1 pos2 = decAdjacentTopRight pos2 pos1

export
data Adjacent : Pos width height -> Pos width height -> Type where
  AdjRight : AdjacentRight pos1 pos2 -> Adjacent pos1 pos2
  AdjLeft : AdjacentLeft pos1 pos2 -> Adjacent pos1 pos2
  AdjBottom : AdjacentBottom pos1 pos2 -> Adjacent pos1 pos2
  AdjTop : AdjacentTop pos1 pos2 -> Adjacent pos1 pos2
  AdjBottomRight: AdjacentBottomRight pos1 pos2 -> Adjacent pos1 pos2
  AdjTopLeft : AdjacentTopLeft pos1 pos2 -> Adjacent pos1 pos2
  AdjTopRight : AdjacentTopRight pos1 pos2 -> Adjacent pos1 pos2
  AdjBottomLeft : AdjacentBottomLeft pos1 pos2 -> Adjacent pos1 pos2

0 adjacentSymm : Adjacent pos1 pos2 -> Adjacent pos2 pos1
adjacentSymm (AdjRight adj) = AdjLeft adj
adjacentSymm (AdjLeft adj) = AdjRight adj
adjacentSymm (AdjBottom adj) = AdjTop adj
adjacentSymm (AdjTop adj) = AdjBottom adj
adjacentSymm (AdjBottomRight adj) = AdjTopLeft adj
adjacentSymm (AdjTopLeft adj) = AdjBottomRight adj
adjacentSymm (AdjTopRight adj) = AdjBottomLeft adj
adjacentSymm (AdjBottomLeft adj) = AdjTopRight adj

0 adjacentToBottomRight : AdjacentRight pos1 pos2 -> AdjacentBottom pos2 pos3 -> AdjacentBottomRight pos1 pos3
adjacentToBottomRight {pos1 = (_, _), pos2 = (_, _), pos3 = (_, _)} adjR adjB = (rewrite sym $ fst adjB in fst adjR, rewrite snd adjR in snd adjB)

0 adjacentToTopRight : AdjacentRight pos1 pos2 -> AdjacentTop pos2 pos3 -> AdjacentTopRight pos1 pos3
adjacentToTopRight {pos1 = (_, _), pos2 = (_, _), pos3 = (_, _)} adjR adjT = (rewrite fst adjT in fst adjR, rewrite snd adjR in sym $ snd adjT)

export
n : (pos: Pos width height) -> Maybe $ Subset (Pos width height) (AdjacentTop pos)
n (x, FZ) = Nothing
n (x, FS y) = Just $ Element (x, weaken y) (Refl, Refl)

export
s : (pos: Pos width height) -> Maybe $ Subset (Pos width height) (AdjacentBottom pos)
s {height = S Z} (x, FZ) = Nothing
s {height = S (S _)} (x, FZ) = Just $ Element (x, FS FZ) (Refl, Refl)
s (x, FS y) = map (\(Element (x1, y1) adj) => (Element (x1, FS y1) (fst adj, cong FS (snd adj)))) $ s (x, y)

export
w : (pos: Pos width height) -> Maybe $ Subset (Pos width height) (AdjacentLeft pos)
w (FZ, x) = Nothing
w (FS x, y) = Just $ Element (weaken x, y) (Refl, Refl)

export
e : (pos: Pos width height) -> Maybe $ Subset (Pos width height) (AdjacentRight pos)
e {width = S Z} (FZ, y) = Nothing
e {width = S (S _)} (FZ, y) = Just $ Element (FS FZ, y) (Refl, Refl)
e (FS x, y) = map (\(Element (x1, y1) adj) => (Element (FS x1, y1) (cong FS (fst adj), snd adj))) $ e (x, y)

export
nw : (pos: Pos width height) -> Maybe $ Subset (Pos width height) (AdjacentTopLeft pos)
nw pos = do
  Element npos adj1 <- n pos
  Element nwpos adj2 <- w npos
  pure $ Element nwpos $ adjacentToBottomRight adj2 adj1

export
ne : (pos: Pos width height) -> Maybe $ Subset (Pos width height) (AdjacentTopRight pos)
ne pos = do
  Element epos adj1 <- e pos
  Element nepos adj2 <- n epos
  pure $ Element nepos $ adjacentToTopRight adj1 adj2

export
sw : (pos: Pos width height) -> Maybe $ Subset (Pos width height) (AdjacentBottomLeft pos)
sw pos = do
  Element spos adj1 <- s pos
  Element swpos adj2 <- w spos
  pure $ Element swpos $ adjacentToTopRight adj2 adj1

export
se : (pos: Pos width height) -> Maybe $ Subset (Pos width height) (AdjacentBottomRight pos)
se pos = do
  Element epos adj1 <- e pos
  Element sepos adj2 <- s epos
  pure $ Element sepos $ adjacentToBottomRight adj1 adj2

export
n' : (pos: Pos width height) -> Maybe $ Subset (Pos width height) (Adjacent pos)
n' pos1 = map (\(Element pos2 adj) => Element pos2 (AdjTop adj)) $ n pos1

export
s' : (pos: Pos width height) -> Maybe $ Subset (Pos width height) (Adjacent pos)
s' pos1 = map (\(Element pos2 adj) => Element pos2 (AdjBottom adj)) $ s pos1

export
w' : (pos: Pos width height) -> Maybe $ Subset (Pos width height) (Adjacent pos)
w' pos1 = map (\(Element pos2 adj) => Element pos2 (AdjLeft adj)) $ w pos1

export
e' : (pos: Pos width height) -> Maybe $ Subset (Pos width height) (Adjacent pos)
e' pos1 = map (\(Element pos2 adj) => Element pos2 (AdjRight adj)) $ e pos1

export
nw' : (pos: Pos width height) -> Maybe $ Subset (Pos width height) (Adjacent pos)
nw' pos1 = map (\(Element pos2 adj) => Element pos2 (AdjTopLeft adj)) $ nw pos1

export
ne' : (pos: Pos width height) -> Maybe $ Subset (Pos width height) (Adjacent pos)
ne' pos1 = map (\(Element pos2 adj) => Element pos2 (AdjTopRight adj)) $ ne pos1

export
sw' : (pos: Pos width height) -> Maybe $ Subset (Pos width height) (Adjacent pos)
sw' pos1 = map (\(Element pos2 adj) => Element pos2 (AdjBottomLeft adj)) $ sw pos1

export
se' : (pos: Pos width height) -> Maybe $ Subset (Pos width height) (Adjacent pos)
se' pos1 = map (\(Element pos2 adj) => Element pos2 (AdjBottomRight adj)) $ se pos1

data Direction : Type where
  DirRight: Direction
  DirBottomRight: Direction
  DirBottom: Direction
  DirBottomLeft: Direction
  DirLeft: Direction
  DirTopLeft: Direction
  DirTop: Direction
  DirTopRight: Direction

inverse : Direction -> Direction
inverse DirRight = DirLeft
inverse DirBottomRight = DirTopLeft
inverse DirBottom = DirTop
inverse DirBottomLeft = DirTopRight
inverse DirLeft = DirRight
inverse DirTopLeft = DirBottomRight
inverse DirTop = DirBottom
inverse DirTopRight = DirBottomLeft

rotate : Direction -> Direction
rotate DirRight = DirBottomRight
rotate DirBottomRight = DirBottom
rotate DirBottom = DirBottomLeft
rotate DirBottomLeft = DirLeft
rotate DirLeft = DirTopLeft
rotate DirTopLeft = DirTop
rotate DirTop = DirTopRight
rotate DirTopRight = DirRight

rotateNotAdjacent : Direction -> Direction
rotateNotAdjacent DirRight = DirBottomLeft
rotateNotAdjacent DirBottomRight = DirBottomLeft
rotateNotAdjacent DirBottom = DirTopLeft
rotateNotAdjacent DirBottomLeft = DirTopLeft
rotateNotAdjacent DirLeft = DirTopRight
rotateNotAdjacent DirTopLeft = DirTopRight
rotateNotAdjacent DirTop = DirBottomRight
rotateNotAdjacent DirTopRight = DirBottomRight

0 adjacentAbsurd : Adjacent pos1 pos2
                -> Not (AdjacentRight pos1 pos2)
                -> Not (AdjacentLeft pos1 pos2)
                -> Not (AdjacentBottom pos1 pos2)
                -> Not (AdjacentTop pos1 pos2)
                -> Not (AdjacentBottomRight pos1 pos2)
                -> Not (AdjacentTopLeft pos1 pos2)
                -> Not (AdjacentTopRight pos1 pos2)
                -> Not (AdjacentBottomLeft pos1 pos2)
                -> Void
adjacentAbsurd (AdjRight adj) nadj _ _ _ _ _ _ _ = nadj adj
adjacentAbsurd (AdjLeft adj) _ nadj _ _ _ _ _ _ = nadj adj
adjacentAbsurd (AdjBottom adj) _ _ nadj _ _ _ _ _ = nadj adj
adjacentAbsurd (AdjTop adj) _ _ _ nadj _ _ _ _ = nadj adj
adjacentAbsurd (AdjBottomRight adj) _ _ _ _ nadj _ _ _ = nadj adj
adjacentAbsurd (AdjTopLeft adj) _ _ _ _ _ nadj _ _ = nadj adj
adjacentAbsurd (AdjTopRight adj) _ _ _ _ _ _ nadj _ = nadj adj
adjacentAbsurd (AdjBottomLeft adj) _ _ _ _ _ _ _ nadj = nadj adj

direction : {pos1, pos2: Pos width height} -> (0 _: Adjacent pos1 pos2) -> Direction
direction {pos1} {pos2} adj with (decAdjacentRight {pos1} {pos2})
  _ | Yes _ = DirRight
  _ | No p1 with (decAdjacentLeft {pos1} {pos2})
    _ | Yes _ = DirLeft
    _ | No p2 with (decAdjacentBottom {pos1} {pos2})
      _ | Yes _ = DirBottom
      _ | No p3 with (decAdjacentTop {pos1} {pos2})
        _ | Yes _ = DirTop
        _ | No p4 with (decAdjacentBottomRight {pos1} {pos2})
          _ | Yes _ = DirBottomRight
          _ | No p5 with (decAdjacentTopLeft {pos1} {pos2})
            _ | Yes _ = DirTopLeft
            _ | No p6 with (decAdjacentTopRight {pos1} {pos2})
              _ | Yes _ = DirTopRight
              _ | No p7 with (decAdjacentBottomLeft {pos1} {pos2})
                _ | Yes _ = DirBottomLeft
                _ | No p8 = void $ adjacentAbsurd adj p1 p2 p3 p4 p5 p6 p7 p8

directionToPos : Direction -> (pos: Pos width height) -> Maybe $ Subset (Pos width height) (Adjacent pos)
directionToPos DirRight = e'
directionToPos DirBottomRight = se'
directionToPos DirBottom = s'
directionToPos DirBottomLeft = sw'
directionToPos DirLeft = w'
directionToPos DirTopLeft = nw'
directionToPos DirTop = n'
directionToPos DirTopRight = ne'
