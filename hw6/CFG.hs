module CFG where

import Prelude hiding (Monoid(..), Semigroup(..))
import Data.Tree
import Algebra

-- CFGs in Chomsky Normal Form
-- ====================================================

data Rule nt
  = nt :- String    -- Lexical rule, e.g., N :- "dog"
  | nt :< (nt, nt)  -- Branching rule, e.g., S :< (NP, VP)
  deriving (Eq, Show, Ord)

type CFG nt = [Rule nt] -- a CFG is just a list of rules

type Phrase = [String] -- a "phrase" is any list of words

-- Labeled Binary Trees
-- ====================================================

data LBT nt
  = Leaf nt String
  | Branch nt (LBT nt) (LBT nt)
  deriving (Eq, Show, Ord)

root :: LBT nt -> nt
root (Leaf c _)     = c
root (Branch c _ _) = c


-- Pretty-printed trees
-- ====================================================

 -- convert LBT to Tree
toTree :: Show nt => LBT nt -> Tree String
toTree (Leaf   c x)   = Node (show c) [Node (show x) []]
toTree (Branch c l r) = Node (show c) [toTree l, toTree r]
                                                                                                                    
displayForest :: Show nt => [LBT nt] -> IO ()
displayForest = putStrLn . drawForest . map toTree


-- Some small English grammars
-- ====================================================

data Cats = S | D | DP | NP | VT | VP | P | PP | WP | W | RC | C
  deriving (Eq, Show, Ord) 


eng :: CFG Cats
eng =
  [ S  :< (DP, VP)
  , S  :< (WP, S )     -- preposed while-phrases
  , WP :< (W , S)      -- making a while-phrase
  , VP :< (VT, DP)
  , DP :< (D , NP)
  , NP :< (NP, PP)
  , NP :< (NP, RC)     -- relative clause modification of an NP
  , PP :< (P , DP)
  , VP :< (VP, PP)
  , RC :< (C , VP)     -- subject-gap rel clauses require "that"
  , RC :< (DP, VT)     -- object-gap rel clauses without "that"
  , DP :- "Sam"
  , DP :- "I"
  , VT :- "wrote"
  , VT :- "read"
  , VT :- "know"
  , VT :- "watched"    -- "watched" is transitive
  , VP :- "watched"    -- "watched" is also intransitive
  , VP :- "cried"
  , VP :- "awoke"
  , VP :- "stinks"
  , D  :- "this"
  , D  :- "the"
  , D  :- "every"
  , NP :- "book"
  , NP :- "baby"
  , NP :- "student"
  , P  :- "with"
  , C  :- "that"
  , W  :- "while"
  ]

cfg14 :: CFG Cats
cfg14 =
  [ S  :< (DP,VP)
  , VP :< (VT,NP)
  , NP :< (NP,PP)
  , PP :< (P ,NP)
  , VP :< (VP,PP)
  , DP :- "Mary"
  , DP :- "Sam"
  , NP :- "telescopes"
  , NP :- "spies"
  , NP :- "watches"  -- "watches" is a noun
  , VP :- "watches"  -- "watches" is also an intransitive verb
  , VP :- "spies"
  , VT :- "watches"  -- "watches" is also a transitive verb
  , P  :- "with"
  ]


type PCFG nt = [(Rule nt, Prob)]

-- A probabilistic version of cfg14
pcfg14 :: PCFG Cats
pcfg14 =
  [ (S  :< (DP,VP), 1.0)
  , (VP :< (VT,NP), 0.4)
  , (NP :< (NP,PP), 0.2)
  , (PP :< (P ,NP), 1.0)
  , (VP :< (VP,PP), 0.3)
  , (DP :- "Mary", 0.4)
  , (DP :- "Sam", 0.6)
  , (NP :- "telescopes", 0.1)
  , (NP :- "watches", 0.3)
  , (NP :- "spies", 0.2)
  , (VP :- "spies", 0.1)
  , (VP :- "watches", 0.2)
  , (VT :- "watches", 1.0)
  , (P  :- "with", 1.0)
  ]


-- PARSING
-- ====================================================

-- generate every split of a list
splits :: [a] -> [([a], [a])]
splits u = [splitAt i u | i <- [1..length u - 1]]

-- Naive parsing to categories
-- ====================================================

-- look up the possible categories for a given word
stepLex :: CFG nt -> String -> [nt]
stepLex cfg w =
  [ c | (c :- v) <- cfg, w==v ]

-- look up all the possible categories for a given
-- pair of daughter categories
stepBin :: Eq nt => CFG nt -> [nt] -> [nt] -> [nt]
stepBin cfg left right =
  [ c | lcat <- left, rcat <- right, (c :< (l, r)) <- cfg
      , l==lcat, r==rcat ]

-- find all the categories that can join two phrases
combine :: Eq nt => CFG nt -> (Phrase, Phrase) -> [nt]
combine cfg (left, right) = stepBin cfg lcats rcats
  where lcats = parse cfg left
        rcats = parse cfg right

-- split a phrase every way possible and combine each split
parse :: Eq nt => CFG nt -> Phrase -> [nt]
parse cfg [w] = stepLex cfg w -- if the phrase is a single word
parse cfg phr = concat [combine cfg (l,r) | (l,r) <- splits phr] -- if it's more


-- Naive parsing to trees
-- ====================================================

stepLexLBT :: CFG nt -> String -> [LBT nt]
stepLexLBT cfg w =
  [ Leaf c w | (c :- v) <- cfg, w==v ]

stepBinLBT :: Eq nt => CFG nt -> [LBT nt] -> [LBT nt] -> [LBT nt]
stepBinLBT cfg left right =
  [ Branch c ltree rtree | ltree <- left, rtree <- right
                         , (c :< (l,r)) <- cfg, l == root ltree, r == root rtree ]

combineLBT :: Eq nt => CFG nt -> (Phrase, Phrase) -> [LBT nt]
combineLBT cfg (left, right) = stepBinLBT cfg lts rts
  where lts = parseLBT cfg left  -- parse the left daughter
        rts = parseLBT cfg right -- parse the right daughter

parseLBT :: Eq nt => CFG nt -> Phrase -> [LBT nt]
parseLBT cfg [w] = stepLexLBT cfg w
parseLBT cfg phr = concat [combineLBT cfg (l,r) | (l,r) <- splits phr]


-- Naive parsing to monoid-weighted categories
-- ====================================================

-- a CFG where rules are tagged with values
type CFT nt v = [(Rule nt, v)]

stepLexM :: Monoid v => CFT nt v -> String -> [(nt, v)]
stepLexM cfg w =
  [ (c, m) | (c :- v, m) <- cfg, w==v ]

stepBinM :: (Eq nt, Monoid v) => CFT nt v -> [(nt, v)] -> [(nt, v)] -> [(nt, v)]
stepBinM cfg left right =
  [ (c, m<>n<>o) | (lcat, n) <- left, (rcat, o) <- right
                 , (c :< (l,r), m) <- cfg, l==lcat, r==rcat ]

combineM :: (Eq nt, Monoid v) => CFT nt v -> (Phrase, Phrase) -> [(nt, v)]
combineM cfg (left, right) = stepBinM cfg lts rts -- combine the results
  where lts = parseM cfg left  -- parse the left daughter
        rts = parseM cfg right -- parse the right daughter

parseM :: (Eq nt, Monoid v) => CFT nt v -> Phrase -> [(nt, v)]
parseM cfg [w] = stepLexM cfg w
parseM cfg phr  = concat [combineM cfg (l,r) | (l,r) <- splits phr]


-- CKY parsing to categories
-- ====================================================

-- an append operator, just for convenience
xs +: x = xs ++ [x]

-- a lookup function for keys that are known to be in a dictionary
lookup' :: Eq k => k -> [(k,v)] -> v
lookup' key ((k,v):tail) = if key == k then v else lookup' key tail

-- all the suffixes of a list
tails :: [a] -> [[a]]
tails []     = []
tails (x:xs) = tails xs +: (x:xs)

-- all the prefixes of a list
inits :: [a] -> [[a]]
inits = go [] [] where
  go cur res []     = res
  go cur res (x:xs) = let next = cur +: x in go next (res +: next) xs

-- all the suffixes of all the prefixes
spans :: [a] -> [[a]]
spans = inits >=> tails
  where f >=> g = \a -> [c | b <- f a, c <- g b] -- standard relation composition


-- parse every sub-span of the sentence exactly once, using the results of
-- previous parses instead of re-parsing
-- note that the chart is an "accumulating parameter" in the recursion, similar
-- to the `enumerate` and `merge` functions we've written in class, or
-- the `inits` function above

cky :: Eq nt => CFG nt -> Phrase -> [nt]
cky cfg xs = let ((_, cats):_) = go (spans xs) [] in cats
 where
  go []         chart = chart
  go ([w]:phrs) chart = go phrs (([w],r):chart)
    where
      r = [c | (c :- v) <- cfg, v==w]
  go (phr:phrs) chart = go phrs ((phr,r):chart)
    where
      r = [ c | (left,right) <- splits phr
              -- instead of parsing the left/right daughters, we just look them up
              -- in the chart because we know we've already parsed them
              , lcat <- lookup' left  chart
              , rcat <- lookup' right chart
              , (c :< (l,r)) <- cfg, l==lcat, r==rcat ]

ckyM :: (Eq nt, Monoid v) => CFT nt v -> Phrase -> [(nt, v)]
ckyM mcfg xs = let ((_, cats):_) = go (spans xs) [] in cats
 where
  go []         chart = chart
  go ([w]:phrs) chart = go phrs (([w], r):chart)
    where
      r = [(c, m) | (c :- v, m) <- mcfg, v==w]
  go (phr:phrs) chart = go phrs ((phr, r):chart)
    where
      r = [ (c, m<>n<>o) | (left,right) <- splits phr
                         , (lcat, n) <- lookup' left  chart
                         , (rcat, o) <- lookup' right chart
                         , (c :< (l,r), m) <- mcfg, l==lcat, r==rcat ]

cky' :: (Eq nt, Semiring v) => CFT nt v -> Phrase -> [(nt, v)]
cky' scfg xs = let ((_, cats):_) = go (spans xs) [] in cats
 where
  go []         chart = chart
  go ([w]:phrs) chart = go phrs (([w], r):chart)
    where
      r = [(c, m) | (c :- v, m) <- scfg, v==w]
  go (phr:phrs) chart = go phrs ((phr, compress r):chart)
    where
      r = [ (c, m<>n<>o) | (left,right) <- splits phr
                         , (lcat, n) <- lookup' left  chart
                         , (rcat, o) <- lookup' right chart
                         , (c :< (l,r), m) <- scfg, l==lcat, r==rcat ]
