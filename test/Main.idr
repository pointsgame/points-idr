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

main : IO ()
main = do
  putStrLn $ "simple surround \{show simpleSurround}"
  pure ()
