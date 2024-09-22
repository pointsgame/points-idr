module Main

import Data.Vect
import Data.Iterable
import Data.String
import Decidable.Equality.Core
import Decidable.Equality
import System
import System.Random
import Points.Pos
import Points.Player
import Points.Field

swap : Fin (S i) -> Vect (S i) a -> (a, Vect i a)
swap FZ (x :: xs) = (x, xs)
swap (FS FZ) (x1 :: x2 :: xs) = (x2, x1 :: xs)
swap (FS (FS i)) (x1 :: x2 :: xs) with (swap (FS i) (x2 :: xs))
  _ | (x', xs') = (x', x1 :: xs')

shuffle : {i: Nat} -> Vect i a -> IO $ Vect i a
shuffle Nil = pure Nil
shuffle {i = S i} xs@(_ :: _) = do
  k <- rndFin _
  let (x', xs') = swap k xs
  xs'' <- shuffle xs'
  pure (x' :: xs'')

allMoves : (width, height: Nat) -> Vect (width * height) $ Pos width height
allMoves width height = do
  concat $ map (\x => map (\y => (x, y)) range) range

randomGame : (width, height: Nat) -> IO $ Field width height
randomGame width height = do
  moves <- shuffle $ allMoves width height
  pure $ foldl (\field => \pos => case decEq (isPuttingAllowed field pos) True of
                                    No _ => field
                                    Yes p => putNextPoint pos field p
               ) (emptyField _ _) $ moves

record Result where
  constructor MkResult
  redScore, blackScore: Nat

Semigroup Result where
  (<+>) l r = MkResult (redScore l + redScore r) (blackScore l + blackScore r)

Monoid Result where
  neutral = MkResult 0 0

gameResult : Field width height -> Result
gameResult field = case winner field of
  Just Red => MkResult 1 0
  Just Black => MkResult 0 1
  Nothing => MkResult 0 0

record Args where
  constructor MkArgs
  width, height, gamesNumber : Nat
  seed: Integer

parseArgs : List String -> Maybe Args
parseArgs (_ :: width :: height :: gamesNumber :: seed :: []) = do
  width <- parsePositive width
  height <- parsePositive height
  gamesNumber <- parsePositive gamesNumber
  seed <- parseInteger seed
  pure $ MkArgs width height gamesNumber seed
parseArgs _ = Nothing

main : IO ()
main = do
  let usage = putStrLn "Usage: Bench {width} {height} {games} {seed}" >> exitFailure {io = IO}
  args <- getArgs
  args <- maybe usage pure $ parseArgs args
  srand $ fromInteger $ seed args
  result <- foldM (const $ map gameResult $ randomGame (width args) (height args)) $ gamesNumber args
  putStrLn $ show (redScore result) ++ ":" ++ show (blackScore result)
