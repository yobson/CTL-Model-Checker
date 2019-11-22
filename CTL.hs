import qualified Data.Set as S

data Formula = T | Atom String | And Formula Formula | Not Formula| ExistsNext Formula | ExistsUntil Formula Formula | ForallNext Formula | ForallUntil Formula Formula deriving (Eq, Show)

foldForm :: b -> (String -> b) -> (b -> b -> b) -> (b -> b) -> (b -> b) -> (b -> b -> b) -> (b -> b) -> (b -> b -> b) -> Formula -> b
foldForm p atom and not existsNext existsUntil forallNext forallUntil (T) = p
foldForm p atom and not existsNext existsUntil forallNext forallUntil (Atom s) = atom s
foldForm p atom and not existsNext existsUntil forallNext forallUntil (And f1 f2) = and (foldForm p atom and not existsNext existsUntil forallNext forallUntil f1) (foldForm p atom and not existsNext existsUntil forallNext forallUntil f2)
foldForm p atom and not existsNext existsUntil forallNext forallUntil (Not f) = not (foldForm p atom and not existsNext existsUntil forallNext forallUntil f)
foldForm p atom and not existsNext existsUntil forallNext forallUntil (ExistsNext f) = existsNext (foldForm p atom and not existsNext existsUntil forallNext forallUntil f)
foldForm p atom and not existsNext existsUntil forallNext forallUntil (ExistsUntil f1 f2) = existsUntil (foldForm p atom and not existsNext existsUntil forallNext forallUntil f1) (foldForm p atom and not existsNext existsUntil forallNext forallUntil f2)
foldForm p atom and not existsNext existsUntil forallNext forallUntil (ForallNext f) = forallNext (foldForm p atom and not existsNext existsUntil forallNext forallUntil f)
foldForm p atom and not existsNext existsUntil forallNext forallUntil (ForallUntil f1 f2) = forallUntil (foldForm p atom and not existsNext existsUntil forallNext forallUntil f1) (foldForm p atom and not existsNext existsUntil forallNext forallUntil f2)

type Name = String
type Label = String
type States = S.Set State

fix' :: (Eq a) => S.Set a -> (S.Set a -> S.Set a) -> S.Set a
fix' e f | res == e  = e
         | otherwise = fix' res f
  where res = f e

fix = fix' S.empty

data State = State Name Label [State]

instance Eq State where
  (State s1 _ _) == (State s2 _ _) = s1 == s2

instance Ord State where
  (State s1 _ _) <= (State s2 _ _) = s1 <= s2

instance Show State where
  show (State s l _) = show (s,l)

allStates = allStates' S.empty

allStates' :: States -> State -> States
allStates' cont x@(State s l []) = S.singleton x `S.union` cont
allStates' cont x@(State s l xs) = cont' `S.union` S.unions (map allStates filt)
  where filt = filter (\y -> not $ S.member y cont') xs
        cont' = cont `S.union` S.singleton x

post :: State -> States
post (State _ _ xs) = S.fromList xs

posts :: States -> States
posts s = S.unions (S.map (\(State _ _ xs) -> (S.fromList xs)) s)

sat :: State -> Formula -> States
sat init = foldForm ts (satPred' ts) satAnd (satNot' ts) (satExistsNext' ts) satExistsUntil (satForallNext' ts) satForallUntil
  where ts = allStates init

satPred' :: States -> String -> States
satPred' s l = S.filter (\(State _ lab _) -> filter (\a -> elem a l) lab == l) s

satAnd :: States -> States -> States
satAnd = S.intersection

satNot' :: States -> States -> States
satNot' = S.difference

satExistsNext' :: States -> States -> States
satExistsNext' all phi = S.unions (S.map postPred all)
  where postPred s | post(s) `S.intersection` phi /= S.empty = S.singleton s
                   | otherwise                               = S.empty

satExistsUntil :: States -> States -> States
satExistsUntil phi psi = fix f
  where f t = psi `S.union` satExistsNext' phi t

satForallNext' :: States -> States -> States
satForallNext' all phi = S.unions (S.map postPred all)
  where postPred s | post(s) `S.isSubsetOf` phi = S.singleton s
                   | otherwise              = S.empty

satForallUntil :: States -> States -> States
satForallUntil phi psi = fix f
  where f t = psi `S.union` satForallNext' phi t
