module Main

import Data.Fin
import Data.List1
import Data.String
import Decidable.Equality.Core
import Decidable.Equality
import Points.Pos
import Points.Player
import Points.Field

record GenField where
  constructor MkGenField
  width, height: Nat
  field: Field width height

constructField : String -> Maybe GenField
constructField image = case filter (/= "") $ toList $ split (== '\n') image of
  [] => Nothing
  lines @ (h :: _) =>
    let width = length h
        height = length lines
        moves = map (\(c, pos) => (if isLower c then Red else Black, pos)) $
                sortBy (\(c1, _) => \(c2, _) => compare (toLower c1, isLower c1) (toLower c2, isLower c2)) $
                List.filter (\(c, _) => toLower c /= toUpper c) $
                concatMap (\(line, y) => map (\(c, x) => (c, x, y)) $
                                         zip (unpack line) $
                                         allFins width) $
                zip lines $
                allFins height
        field = foldl (\field => \(player, pos) => field >>= \field => case decEq (isPuttingAllowed field pos) True of
                                                                         Yes p => Just $ putPoint pos player field p
                                                                         No _ => Nothing) (Just $ emptyField width height) moves
    in map (\field => MkGenField width height field) field

simpleSurroundImage = constructField """
.a.
cBa
.a.
"""

simpleSurround : Bool
simpleSurround = maybe False (\field =>
    scoreRed (GenField.field field) == 1 && scoreBlack (GenField.field field) == 0
  ) simpleSurroundImage

surroundEmptyTerritoryImage = constructField """
.a.
a.a
.a.
"""

surroundEmptyTerritory : Bool
surroundEmptyTerritory = maybe False (\field =>
    scoreRed (GenField.field field) == 0 && scoreBlack (GenField.field field) == 0
  ) surroundEmptyTerritoryImage

movePriorityImage = constructField """
.aB.
aCaB
.aB.
"""

movePriority : Bool
movePriority = maybe False (\field =>
    scoreRed (GenField.field field) == 0 && scoreBlack (GenField.field field) == 1
  ) movePriorityImage

movePriorityBigImage = constructField """
.B..
BaB.
aCaB
.aB.
"""

movePriorityBig : Bool
movePriorityBig = maybe False (\field =>
    scoreRed (GenField.field field) == 0 && scoreBlack (GenField.field field) == 2
  ) movePriorityBigImage

onionSurroundingsImage = constructField """
...c...
..cBc..
.cBaBc.
..cBc..
...c...
"""

onionSurroundings : Bool
onionSurroundings = maybe False (\field =>
    scoreRed (GenField.field field) == 4 && scoreBlack (GenField.field field) == 0
  ) onionSurroundingsImage

deepOnionSurroundingsImage = constructField """
...D...
..DcD..
.DcBcD.
DcBaBcD
.DcBcD.
..DcD..
...D...
"""

deepOnionSurroundings : Bool
deepOnionSurroundings = maybe False (\field =>
    scoreRed (GenField.field field) == 0 && scoreBlack (GenField.field field) == 9
  ) deepOnionSurroundingsImage

applyControlSurroundingInSameTurnImage = constructField """
.a.
aBa
.a.
"""

applyControlSurroundingInSameTurn : Bool
applyControlSurroundingInSameTurn = maybe False (\field =>
    scoreRed (GenField.field field) == 1 && scoreBlack (GenField.field field) == 0
  ) applyControlSurroundingInSameTurnImage

doubleSurroundImage = constructField """
.a.a.
aAbAa
.a.a.
"""

doubleSurround : Bool
doubleSurround = maybe False (\field =>
    scoreRed (GenField.field field) == 2 && scoreBlack (GenField.field field) == 0
  ) doubleSurroundImage

doubleSurroundWithEmptyPartImage = constructField """
.b.b..
b.zAb.
.b.b..
"""

doubleSurroundWithEmptyPart : Bool
doubleSurroundWithEmptyPart = maybe False (\field =>
    scoreRed (GenField.field field) == 1 && scoreBlack (GenField.field field) == 0
  ) doubleSurroundWithEmptyPartImage

shouldNotLeaveEmptyInsideImage = constructField """
.aaaa..
a....a.
a.b...a
.z.bC.a
a.b...a
a....a.
.aaaa..
"""

shouldNotLeaveEmptyInside : Bool
shouldNotLeaveEmptyInside = maybe False (\field =>
    scoreRed (GenField.field field) == 1 && scoreBlack (GenField.field field) == 0
  ) shouldNotLeaveEmptyInsideImage

surroundInOppositeTurnImage = constructField """
.a.
aBa
.a.
"""

surroundInOppositeTurn : Bool
surroundInOppositeTurn = maybe False (\field =>
    scoreRed (GenField.field field) == 1 && scoreBlack (GenField.field field) == 0
  ) surroundInOppositeTurnImage

partlySurroundInOppositeTurnImage = constructField """
.a..
aBa.
.a.a
..a.
"""

partlySurroundInOppositeTurn : Bool
partlySurroundInOppositeTurn = maybe False (\field =>
    scoreRed (GenField.field field) == 1 && scoreBlack (GenField.field field) == 0
  ) partlySurroundInOppositeTurnImage

holeInsideSurroundingImage = constructField """
....c....
...c.c...
..c...c..
.c..a..c.
c..a.a..c
.c..a..c.
..c...c..
...cBc...
....d....
"""

holeInsideSurrounding : Bool
holeInsideSurrounding = maybe False (\field =>
    scoreRed (GenField.field field) == 1 && scoreBlack (GenField.field field) == 0
  ) holeInsideSurroundingImage

holeInsideSurroundingAfterOppositeTurnSurroundingImage = constructField """
....b....
...b.b...
..b...b..
.b..a..b.
b..a.a..b
.b..a..b.
..b...b..
...bCb...
....b....
"""

holeInsideSurroundingAfterOppositeTurnSurrounding : Bool
holeInsideSurroundingAfterOppositeTurnSurrounding = maybe False (\field =>
    scoreRed (GenField.field field) == 1 && scoreBlack (GenField.field field) == 0
  ) holeInsideSurroundingAfterOppositeTurnSurroundingImage

surroundingDoesNotExpandImage = constructField """
....a....
...a.a...
..a.a.a..
.a.a.a.a.
a.a.aBa.a
.a.a.a.a.
..a.a.a..
...a.a...
....a....
"""

surroundingDoesNotExpand : Bool
surroundingDoesNotExpand = maybe False (\field =>
    scoreRed (GenField.field field) == 1 && scoreBlack (GenField.field field) == 0
  ) surroundingDoesNotExpandImage

twoSurroundingsWithCommonBorderImage = constructField """
.a..
aAa.
.bAa
..a.
"""

twoSurroundingsWithCommonBorder : Bool
twoSurroundingsWithCommonBorder = maybe False (\field =>
    scoreRed (GenField.field field) == 2 && scoreBlack (GenField.field field) == 0
  ) twoSurroundingsWithCommonBorderImage

twoSurroundingsWithCommonDotImage = constructField """
.a.a.
aBcBa
.a.a.
"""

twoSurroundingsWithCommonDot : Bool
twoSurroundingsWithCommonDot = maybe False (\field =>
    scoreRed (GenField.field field) == 2 && scoreBlack (GenField.field field) == 0
  ) twoSurroundingsWithCommonDotImage

threeSurroundingsWithCommonBordersImage = constructField """
..a..
.aAa.
..bAa
.aAa.
..a..
"""

threeSurroundingsWithCommonBorders : Bool
threeSurroundingsWithCommonBorders = maybe False (\field =>
    scoreRed (GenField.field field) == 3 && scoreBlack (GenField.field field) == 0
  ) threeSurroundingsWithCommonBordersImage

twoSurroundingsWithCommonDotOneBorderlineEmptyPlaceImage = constructField """
..a..
.aBa.
..c.a
.aBa.
..a..
"""

twoSurroundingsWithCommonDotOneBorderlineEmptyPlace : Bool
twoSurroundingsWithCommonDotOneBorderlineEmptyPlace = maybe False (\field =>
    scoreRed (GenField.field field) == 2 && scoreBlack (GenField.field field) == 0
  ) twoSurroundingsWithCommonDotOneBorderlineEmptyPlaceImage

main : IO ()
main = do
  putStrLn $ "simple surround \{show simpleSurround}"
  putStrLn $ "surround empty territory \{show surroundEmptyTerritory}"
  putStrLn $ "move priority \{show movePriority}"
  putStrLn $ "move priority, big \{show movePriorityBig}"
  putStrLn $ "onion surroundings \{show onionSurroundings}"
  putStrLn $ "deep onion surroundings \{show deepOnionSurroundings}"
  putStrLn $ "apply 'control' surrounding in same turn \{show applyControlSurroundingInSameTurn}"
  putStrLn $ "double surround \{show doubleSurround}"
  putStrLn $ "double surround with empty part \{show doubleSurroundWithEmptyPart}"
  putStrLn $ "should not leave empty inside \{show shouldNotLeaveEmptyInside}"
  putStrLn $ "surround in opposite turn \{show surroundInOppositeTurn}"
  putStrLn $ "partly surround in opposite turn \{show partlySurroundInOppositeTurn}"
  putStrLn $ "a hole inside a surrounding \{show holeInsideSurrounding}"
  putStrLn $ "a hole inside a surrounding, after opposite turn surrounding \{show holeInsideSurroundingAfterOppositeTurnSurrounding}"
  putStrLn $ "surrounding does not expand \{show surroundingDoesNotExpand}"
  putStrLn $ "2 surroundings with common border \{show twoSurroundingsWithCommonBorder}"
  putStrLn $ "2 surroundings with common dot \{show twoSurroundingsWithCommonDot}"
  putStrLn $ "3 surroundings with common borders \{show threeSurroundingsWithCommonBorders}"
  putStrLn $ "2 surroundings with common dot, one borderline empty place \{show twoSurroundingsWithCommonDotOneBorderlineEmptyPlace}"
