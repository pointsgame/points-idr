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

main : IO ()
main = do
  putStrLn $ "simple surround \{show simpleSurround}"
  putStrLn $ "surround empty territory \{show surroundEmptyTerritory}"
  putStrLn $ "move priority \{show movePriority}"
  putStrLn $ "move priority, big \{show movePriorityBig}"
  putStrLn $ "onion surroundings \{show onionSurroundings}"
  putStrLn $ "deep onion surroundings \{show deepOnionSurroundings}"
