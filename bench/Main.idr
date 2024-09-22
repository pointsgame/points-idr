module Main

import Data.Vect
import Data.Stream
import Decidable.Equality.Core
import Decidable.Equality
import System.Random
import Points.Pos
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

main : IO ()
main = pure ()
