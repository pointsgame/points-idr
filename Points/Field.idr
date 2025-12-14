module Points.Field

import Data.DPair
import Data.Integral
import Data.List
import Data.List1
import Data.SortedSet
import Data.Vect
import Points.Pos
import Points.Player
import Points.Point

public export
record Field (width, height: Nat) where
  constructor MkField
  scoreRed, scoreBlack : Nat
  moves : List (Pos width height, Player)
  lastSurroundChains : List $ List1 $ Pos width height
  lastSurroundPlayer : Player
  points : Vect (width * height) Point

export
point : {height: Nat} -> Field width height -> Pos width height -> Point
point field pos = index (toFin pos) $ points field

export
isPuttingAllowed : {height: Nat} -> Field width height -> Pos width height -> Bool
isPuttingAllowed field pos = Point.isPuttingAllowed $ point field pos

export
isPlayer : {height: Nat} -> Field width height -> Pos width height -> Player -> Bool
isPlayer field pos = Point.isPlayer $ point field pos

export
isPlayersPoint : {height: Nat} -> Field width height -> Pos width height -> Player -> Bool
isPlayersPoint field pos = Point.isPlayersPoint $ point field pos

export
isCapturedPoint : {height: Nat} -> Field width height -> Pos width height -> Player -> Bool
isCapturedPoint field pos = Point.isCapturedPoint $ point field pos

export
isEmptyBase : {height: Nat} -> Field width height -> Pos width height -> Player -> Bool
isEmptyBase field pos = Point.isEmptyBase $ point field pos

export
emptyField : (width: Nat) -> (height: Nat) -> Field width height
emptyField width height = MkField 0 0 [] [] Red $ replicate (width * height) EmptyPoint

wave : {width, height: Nat} -> Pos width height -> (Pos width height -> Bool) -> SortedSet $ Pos width height
wave startPos f = wave' empty (singleton startPos)
  where neighborhood : Pos width height -> List $ Pos width height
        neighborhood pos = mapMaybe (map fst) $ n' pos ::
                                                s' pos ::
                                                w' pos ::
                                                e' pos ::
                                                []
        nextFront : SortedSet (Pos width height) -> SortedSet (Pos width height) -> SortedSet (Pos width height)
        nextFront passed front = difference (SortedSet.fromList $ filter f $ concatMap neighborhood (SortedSet.toList front)) passed
        wave' : SortedSet (Pos width height) -> SortedSet (Pos width height) -> SortedSet (Pos width height)
        wave' passed front = if null front
                             then passed
                             else wave' (union passed front) (nextFront passed front)

getInputPoints : {width, height: Nat} -> Field width height -> (pos : Pos width height) -> Player -> List ((Subset (Pos width height) (Adjacent pos)), (Subset (Pos width height) (Adjacent pos)))
getInputPoints field pos player =
  let isDirectionPlayer : ((pos : Pos width height) -> Maybe (Subset (Pos width height) (Adjacent pos))) -> Bool
      isDirectionPlayer dir = maybe False (\dirPos => isPlayer field (fst dirPos) player) $ dir pos
      list1 = if not $ isDirectionPlayer w' then
                if isDirectionPlayer nw' then toList (zip (nw' pos) (w' pos))
                else if isDirectionPlayer n' then toList (zip (n' pos) (w' pos))
                else []
              else
                []
      list2 = if not $ isDirectionPlayer s' then
                if isDirectionPlayer sw' then toList (zip (sw' pos) (s' pos)) ++ list1
                else if isDirectionPlayer w' then toList (zip (w' pos) (s' pos)) ++ list1
                else list1
              else
                list1
      list3 = if not $ isDirectionPlayer e' then
                if isDirectionPlayer se' then toList (zip (se' pos) (e' pos)) ++ list2
                else if isDirectionPlayer s' then toList (zip (s' pos) (e' pos)) ++ list2
                else list2
              else
                list2
      list4 = if not $ isDirectionPlayer n' then
                if isDirectionPlayer ne' then toList (zip (ne' pos) (n' pos)) ++ list3
                else if isDirectionPlayer e' then toList (zip (e' pos) (n' pos)) ++ list3
                else list3
              else
                list3
  in list4

square : List1 (Pos width height) -> Integer
square (pos ::: tail) = square' $ pos :: tail
  where skewProduct : Pos width height -> Pos width height -> Integer
        skewProduct (x1, y1) (x2, y2) = cast x1 * cast y2 - cast y1 * cast x2
        square' : List (Pos width height) -> Integer
        square' [] = 0
        square' (pos1 :: []) = skewProduct pos1 pos
        square' (pos1 :: pos2 :: tail) = skewProduct pos1 pos2 + square' (pos2 :: tail)

buildChain : {width, height: Nat} -> Field width height -> (startPos, nextPos: Pos width height) -> (0 _: Adjacent startPos nextPos) -> Player -> Maybe $ List1 $ Pos width height
buildChain field startPos nextPos adj player = if square chain > 0 then Just chain else Nothing
  where getNextPlayerPos : (pos: Pos width height) -> Direction -> Subset (Pos width height) (Adjacent pos)
        getNextPlayerPos centerPos dir = case directionToPos dir centerPos of
                                           Nothing => getNextPlayerPos centerPos $ rotate dir
                                           Just (Element pos adj) => if pos == startPos || isPlayer field pos player
                                                                     then Element pos adj
                                                                     else getNextPlayerPos centerPos $ rotate dir
        getChain : (startPos', nextPos': Pos width height) -> (0 _: Adjacent startPos' nextPos') -> List1 (Pos width height) -> List1 (Pos width height)
        getChain _ nextPos adj chain =
          let Element nextPos' nextAdj = getNextPlayerPos nextPos $ rotateNotAdjacent $ inverse $ direction adj
          in if nextPos' == startPos
             then chain
             else getChain nextPos nextPos' nextAdj $ fromMaybe (cons nextPos' chain) $ List1.fromList $ dropWhile (/= nextPos') $ toList chain
        chain = getChain startPos nextPos adj $ cons nextPos $ startPos ::: []

uniq : (Eq a) => List a -> List a
uniq = map head . group

posInsideRing : Pos width height -> List1 (Pos width height) -> Bool
posInsideRing (x, y) ring =
  case List1.fromList $ uniq $ map snd $ filter ((<= x) . fst) $ toList ring of
    Just coords =>
      let coords' = if List1.last coords == y
                    then appendl coords $ toList $ head' $ if head coords == y then tail coords else toList coords
                    else if head coords == y then cons (List1.last coords) coords
                    else coords
       in odd $ count (\(a, b, c) => b == y && ((a < b && c > b) || (a > b && c < b))) $ zip3 (toList coords') (tail coords') (drop 1 $ tail coords')
    Nothing => False

getInsideRing : {width, height: Nat} -> Pos width height -> List1 (Pos width height) -> SortedSet (Pos width height)
getInsideRing startPos ring =
  let ringSet = fromList $ toList ring
   in wave startPos $ not . flip contains ringSet

getEmptyBaseChain : {width, height: Nat} -> Field width height -> Pos width height -> Player -> Maybe $ List1 $ Pos width height
getEmptyBaseChain field startPos player =
  (w startPos) >>= (getEmptyBaseChain' . fst)
  where getEmptyBaseChain' : Pos width height -> Maybe $ List1 $ Pos width height
        getEmptyBaseChain' pos = if not $ isPlayer field pos player then (w pos) >>= (getEmptyBaseChain' . fst)
                                 else let inputPoints = getInputPoints field pos player
                                          chains = mapMaybe (\((Element chainPos adj), _) => buildChain field pos chainPos adj player) inputPoints
                                          result = head' $ List.filter (posInsideRing startPos) chains
                                      in result <|> ((w pos) >>= (getEmptyBaseChain' . fst))

capture : Player -> Point -> Point
capture player point = case point of
  EmptyPoint => BasePoint player False
  PlayerPoint p => if p == player then PlayerPoint p else BasePoint player True
  BasePoint p enemy => if p == player then BasePoint p enemy
                       else if enemy then PlayerPoint player
                       else BasePoint player False
  EmptyBasePoint _ => BasePoint player False

export
putPoint : {width, height: Nat} -> (pos : Pos width height) -> Player -> (field : Field width height) -> (0 _ :isPuttingAllowed field pos = true) -> Field width height
putPoint pos player field _ =
 let enemyPlayer = nextPlayer player
     point' = point field pos
     newMoves = (pos, player) :: moves field
  in if isEmptyBase point' player then
       { moves := newMoves
       , lastSurroundChains := []
       , lastSurroundPlayer := player
       , points := replaceAt (toFin pos) (PlayerPoint player) $ points field
       } field
     else
       let inputPoints = getInputPoints field pos player
           potentialChains = mapMaybe
             (\(Element chainPos chainAdj, Element capturedPos _) =>
               do chain <- buildChain field pos chainPos chainAdj player
                  pure (chain, capturedPos)
             ) inputPoints
           sortedChains = sortBy (\(c1, _), (c2, _) => compare (length c1) (length c2)) potentialChains
           initialField = { lastSurroundPlayer := player, lastSurroundChains := [] } field
           fieldWithCaptures = foldl
             (\field', (chain, capturedPos) =>
                let capturedSet = getInsideRing capturedPos chain
                    capturedList = SortedSet.toList capturedSet
                    capturedCount = count (\pos' => isPlayersPoint field' pos' enemyPlayer) capturedList
                    freedCount = count (\pos' => isCapturedPoint field' pos' player) capturedList
                in if capturedCount > 0
                   then { scoreRed := if player == Player.Red then scoreRed field' + capturedCount else minus (scoreRed field') freedCount
                        , scoreBlack := if player == Player.Black then scoreBlack field' + capturedCount else minus (scoreBlack field') freedCount
                        , lastSurroundChains := chain :: lastSurroundChains field'
                        , points := foldl (\points, p => replaceAt (toFin p) (Point.capture player (point field' p)) points) (points field') capturedList
                        } field'
                   else { points := foldl (\points, p =>
                                        if point field' p == EmptyPoint
                                        then replaceAt (toFin p) (EmptyBasePoint player) points
                                        else points
                                    ) (points field') capturedList
                        } field'
             ) initialField sortedChains
       in if point' == EmptyBasePoint enemyPlayer
          then
             if not $ null $ lastSurroundChains fieldWithCaptures
             then -- We broke the enemy base
                let enemyEmptyBase = wave pos (\pos' => isEmptyBase fieldWithCaptures pos' enemyPlayer)
                in { moves := newMoves
                   , points := let points1 = replaceAt (toFin pos) (PlayerPoint player) $ points fieldWithCaptures
                                   points2 = foldl (\points, p => replaceAt (toFin p) EmptyPoint points) points1 (SortedSet.toList enemyEmptyBase)
                               in points2
                   } fieldWithCaptures
             else -- Suicide move
                let enemyEmptyBaseChain = getEmptyBaseChain field pos enemyPlayer
                    enemyEmptyBase = filter (\pos => isEmptyBase field pos player) $ SortedSet.toList $ maybe SortedSet.empty (getInsideRing pos) $ enemyEmptyBaseChain
                in { scoreRed := if player == Player.Red then scoreRed field else scoreRed field + 1
                   , scoreBlack := if player == Player.Black then scoreBlack field else scoreBlack field + 1
                   , moves := newMoves
                   , lastSurroundChains := maybe [] (:: []) enemyEmptyBaseChain
                   , lastSurroundPlayer := enemyPlayer
                   , points := let points1 = foldl (\points, p => replaceAt (toFin p) (BasePoint enemyPlayer False) points) (points field) enemyEmptyBase
                                   points2 = replaceAt (toFin pos) (BasePoint enemyPlayer True) points1
                               in points2
                   } field
          else -- Normal placement
             { moves := newMoves
             , points := replaceAt (toFin pos) (PlayerPoint player) $ points fieldWithCaptures
             } fieldWithCaptures

export
lastPlayer : Field width height -> Maybe Player
lastPlayer = map snd . head' . moves

export
nextPlayer : Field width height -> Player
nextPlayer = fromMaybe Player.Red . map Player.nextPlayer . lastPlayer

export
putNextPoint : {width, height: Nat} -> (pos: Pos width height) -> (field: Field width height) -> (0 _: isPuttingAllowed field pos = True) -> Field width height
putNextPoint pos field = putPoint pos (nextPlayer field) field

export
winner : Field width height -> Maybe Player
winner field =
  if Field.scoreBlack field < Field.scoreRed field
  then Just Player.Red
  else if Field.scoreRed field < Field.scoreBlack field
  then Just Player.Black
  else Nothing
