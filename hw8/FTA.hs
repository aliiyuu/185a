module FTA where

import Prelude hiding (Monoid(..), Semigroup(..), traverse)

traverse :: (a -> [b]) -> [a] -> [[b]]
traverse f []     = [[]]
traverse f (a:as) = [b:bs | b <- f a, bs <- traverse f as]

------------------------------------------------------------------------
-- This defines the basic "Rose Tree" type for Trees with arbitrary
-- numbers of daughters
------------------------------------------------------------------------
data Tree s = Node s [Tree s] deriving (Eq,Show,Ord)

-- some little functions for writing trees more compactly

-- create a leaf node
lf :: s -> Tree s
lf w = Node w []

-- create an internal node
node :: s -> [Tree s] -> Tree s
node = Node

-- merge two daughter trees together with a root labeled "."
mrg :: Tree String -> Tree String -> Tree String
mrg t1 t2 = Node "." [t1,t2]

-- some example trees
t7 :: Tree String
t7 = node "b" [node "c" [lf "a"], node "a" [lf "b", lf "b"]]

t14 :: Tree String
t14 = Node "a" [Node "b" [Node "b" [Node "a" []], Node "a" [Node "b" [], Node "a" []]]]

t20 :: Tree String
t20 =
  mrg
  ( mrg
    ( lf "that" )
    ( mrg
      ( lf "nobody" )
      ( mrg
        ( lf "met" )
        ( lf "anybody" ))))
  ( mrg
    ( lf "surprised" )
    ( lf "John" ))

-- 'C John ate an apple yesterday'
tree_1a :: Tree String
tree_1a =
  mrg (lf "C") (mrg (lf "John") (mrg (mrg (lf "ate") (mrg (lf "an") (lf "apple"))) (lf "yesterday")))

-- 'Q John ate what yesterday'
tree_1b :: Tree String
tree_1b =
  mrg (lf "Q") (mrg (lf "John") (mrg (mrg (lf "ate") (lf "what")) (lf "yesterday")))

-- 'Q John ate an apple yesterday'
tree_3a :: Tree String
tree_3a =
  mrg (lf "Q") (mrg (lf "John") (mrg (mrg (lf "ate") (mrg (lf "an") (lf "apple"))) (lf "yesterday")))

-- 'C John ate what yesterday'
tree_3b :: Tree String
tree_3b =
  mrg (lf "C") (mrg (lf "John") (mrg (mrg (lf "ate") (lf "what")) (lf "yesterday")))

-- 'Q John laughed because Mary bought books why'
tree_13 :: Tree String
tree_13 =
  Node "." [
    Node "Q" [],
    Node "." [
      Node "John" [],
      Node "." [
        Node "laughed" [],
        Node "*" [
          Node "because" [],
          Node "." [
            Node "Mary" [],
            Node "." [
              Node "." [Node "bought" [], Node "books" []],
              Node "why" []
            ]
          ]
        ]
      ]
    ]
  ]


------------------------------------------------------------------------
-- Here we define a type for a top-down Finite Tree Automaton, specified
-- by a set of initial states and a top-down transition table
------------------------------------------------------------------------

type TDTransition q = (q, String, [q])
data FTA_td q = FTA_tdWith [q] [TDTransition q]
--                          I      Delta

-- a function to determine which categories a tree can have
-- according to a top-down machine
walkFTA_td :: Eq q => [TDTransition q] -> Tree String -> [q]
walkFTA_td delta (Node c cs) =
  [ s | (s, x, ts) <- delta, c==x
      , elem ts (traverse (walkFTA_td delta) cs) ]


-- an example top down FTA that generates only trees with an even
-- number of "a"s

data EO = E | O deriving (Eq, Ord, Show, Enum)

evenAsFTA_td :: FTA_td EO
evenAsFTA_td = FTA_tdWith i delta where
  i = [E]
  delta =
    [ (O, "a", [E,E]) , (E, "b", [E,E])
    , (E, "a", [E,O]) , (O, "b", [E,O])
    , (E, "a", [O,E]) , (O, "b", [O,E])
    , (O, "a", [O,O]) , (E, "b", [O,O])
    , (O, "a", [E]  ) , (E, "b", [E]  )
    , (E, "a", [O]  ) , (O, "b", [O]  )
    , (O, "a", [ ]  ) , (E, "b", [ ]  )
    ]

------------------------------------------------------------------------
-- Here we define a type for a bottom-up Finite Tree Automaton, specified
-- by a set of final states and a top-down transition table
------------------------------------------------------------------------

type Transition q = ([q], String, q)
data FTA q = FTAWith [q] [Transition q]
--                    F      Delta

getDelta :: FTA q -> [Transition q]
getDelta (FTAWith f delta) = delta

getFinals :: FTA q -> [q]
getFinals (FTAWith f delta) = f


-- an example bottom-up FTA that generates only trees with an
-- even number of "a"s

evenAsFTA :: FTA EO
evenAsFTA = FTAWith f delta where
  f = [E]
  delta =
    [ ([E,E], "a", O) , ([E,E], "b", E)
    , ([E,O], "a", E) , ([E,O], "b", O)
    , ([O,E], "a", E) , ([O,E], "b", O)
    , ([O,O], "a", O) , ([O,O], "b", E)
    , ([E]  , "a", O) , ([E]  , "b", E)
    , ([O]  , "a", E) , ([O]  , "b", O)
    , ([ ]  , "a", O) , ([ ]  , "b", E)
    ]




-- an example bottom-up FTA that generates only trees in which
-- each NPI is c-commaneded by a licenser

data Polarity = NPI | Neg | Neu deriving (Eq,Show,Ord)

polarityFTA :: FTA Polarity
polarityFTA = FTAWith f (delta ++ v) where
  f = [Neg, Neu]
  delta = [ ([NPI, NPI], ".", NPI) , ([], "anybody", NPI)
          , ([Neu, NPI], ".", NPI) , ([], "ever",    NPI)
          , ([NPI, Neu], ".", NPI) , ([], "not",     Neg)
          , ([Neu, Neu], ".", Neu) , ([], "nobody",  Neg)
          , ([Neg, NPI], ".", Neu)
          , ([Neg, Neu], ".", Neu)
          , ([Neu, Neg], ".", Neu)
          , ([Neg, Neg], ".", Neu)
          ]
  v = [ ([], w, Neu) | w <- ["that", "met", "surprised", "Mary", "John"]
                     , not (elem w ["anybody","ever","not","nobody"])    ]

------------------------------------------------------

------------------------------------------------------------------------
-- some categorized vocabularies for building FTAs for wh-dependencies
------------------------------------------------------------------------
plainWords = [ "John","Mary","ate","bought","an","apple","books",
               "yesterday", "C","laughed","because" ]
whWords = ["who","what","why"]
qWords = ["Q"]


------------------------------------------------------------------------
-- some convenience functions for displaying trees
-- (drawTree is probably what you want)
------------------------------------------------------------------------

drawTree :: Tree String -> String
drawTree  = unlines . draw

drawForest :: [Tree String] -> String
drawForest  = unlines . map drawTree

draw :: Tree String -> [String]
draw (Node x ts0) = lines x ++ drawSubTrees ts0
  where
    drawSubTrees st = case st of
      []     -> []
      [t]    -> "|" : shift "`- " "   " (draw t)
      (t:ts) -> "|" : shift "+- " "|  " (draw t) ++ drawSubTrees ts
    shift first other = zipWith (++) (first : repeat other)
