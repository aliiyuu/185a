{-# LANGUAGE NoImplicitPrelude #-}


module HW8 where 


-- The only bits of the standard Haskell library that will be available to you
-- are the things you see imported here:

import FTA
import Prelude
  ( -- the basic types that we've seen for integers, booleans, characters, and strings
    Int, Bool(True, False), Char, String
    -- the type constructor Maybe (and its data constructors, Just and Nothing)
  , Maybe(..)
    -- some basic arithmetic operations and relations:
  , (+), (-), (*), (<), (>), (==), (>=), (<=), maximum, minimum, max, min, sum, product
    -- some basic boolean operations:
  , (&&), (||), not
    -- some list inspection and processing functions
  , take, drop, or, and, any, all, map, filter, concat, elem, (++), (.), words
    -- and some classes for showing and comparing things (don't worry about these)
  , Show, Eq, undefined
  )


-- Your task is to fill in the definitions below according to the instructions
-- in the comments (which are also in the pdf version of the assignment). Note
-- that the word `undefined` is a placeholder for what you will write, so make
-- sure you have deleted (and replaced!) every occurrence you see. At any
-- point, you can load this file into ghci, where you should be able to
-- evaluate your expressions to see if they do what you want them to do.

-- To load this file into ghci on the command line, you will need to change to
-- whatever directory you've put this file in, and then make sure that the
-- accompanying FST and Algebra files are also in that directory. Then
-- you just type:
--   > ghci HW8.hs
-- and you should be able to go. You can check to see if one of the functions
-- is in scope by asking ghci for its type with `:type` (or `:t` for short)
--   ghci> :type traverse
--   traverse :: (a -> [b]) -> [a] -> [[b]]
-- Whenever you make a change to the file, you'll need to reload it in ghci
-- with `:reload` (or `:r` for short)
--   ghci> :reload

-- ::: {.tex-center}
-- **Ling 185A: Assignment 8**

-- Dylan Bumford, Winter 2024

-- due: Fri, Mar 15
-- :::

-- # Background and reminders

-- Have a look at `FTA.hs`{.tt}. Things to notice:

-- - Top-down tree automata and functions are designated with `_td`. These are
--   included for reference and as examples. All the exercises will work with
--   bottom-up tree automata, which are designated without a suffix. So `FTA q`,
--   for instance, is a bottom-up finite tree automaton.

-- - You can see some concrete examples of encoded trees in `t7`, `t14` and `t20`.

-- - Remember that _every node has a list of daughters_, though if it's a leaf node
--   that list will be empty. So every tree has the form `Node x ts`, for some
--   symbol `x` and some (possibly empty) list of trees `ts`. To compute, say, the
--   number of nodes in a tree, we could write this:
--   
--   ```
--   nodes :: Tree a -> Int
--   nodes (Node x ts) = 1 + sum (map nodes ts)
--   ```
--   
-- - There are some little convenience functions `lf` (leaf), and `mrg` (binary
--   merge when the root label doesn't matter) to make building trees slightly less
--   tedious. These should be self-evident.

-- ## Warm-ups: Working with trees

-- These don't have anything to do with tree automata yet, just trees.

-- @.  Write a function `count` which returns the number of occurrences of a string
--     in a tree.
--     
count :: String -> Tree String -> Int
count x (Node y ts) = if y == x then 1 + sum (map (count x) ts) else sum (map (count x) ts)
  

--     ```{.shell}
--     ghci> count "a" t7
--     2
--     ghci> count "b" t7
--     3
--     ghci> count "c" t7
--     1
--     ghci> count "a" (Node "a" [t7,t7,t7,t7])
--     9
--     ghci> count "that" t20
--     1
--     ghci> count "." t20
--     5
--     ```

-- @.  Write a function `leftEdge :: Tree a -> [a]` which returns the sequence of
--     symbols we find by following a root-to-leaf path downwards through given
--     tree, taking the leftmost branch at each point. 
--     
leftEdge :: Tree a -> [a]
leftEdge (Node y []) = [y]
leftEdge (Node y (t:ts)) = y : leftEdge t

--     ```{.shell}
--     ghci> leftEdge t7
--     ["b","c","a"]
--     ghci> leftEdge t14
--     ["a","b","b","a"]
--     ghci> leftEdge t20
--     [".",".","that"]
--     ghci> leftEdge (Node 3 [])
--     [3]
--     ```

-- ## Finite Tree Automata Parsing

-- @.  Write a function to parse a tree using a bottom-up tree automaton. This
--     should return the list of states that a machine could end up in after
--     consuming the tree from the leaves upward, using the transitions sanctioned
--     by the machine. You may wish to consider the top down parser `walkFTA_td`
--     defined in class (and in `FTA.hs`{.tt}) for comparison.

walkFTA :: Eq q => [Transition q] -> Tree String -> [q]
walkFTA delta (Node c cs) =  [ r | (ts, x, r) <- delta, c==x
      , elem ts (traverse (walkFTA delta) cs) ]
--     
--     ```{.shell}
--     ghci> walkFTA (getDelta evenAsFTA) t14
--     [E]
--     ghci> walkFTA (getDelta polarityFTA) t20
--     [Meh]
--     ```

-- @.  Write a function to check whether a given `FTA` can generate a given tree.
--     Remember that in order for the tree to be grammatical, there must be at
--     least one tree-shaped path through the machine that ends in an acceptable
--     final state.

generates :: Eq q => FTA q -> Tree String -> Bool
generates m t = any accepting (walkFTA (getDelta m) t)
  where accepting = \q -> elem q (getFinals m)

--     
--     ```{.shell}
--     ghci> generates polarityFTA t20
--     True
--     ghci> generates polarityFTA (Node "." [Node "anything" [], t20])
--     False
--     ghci> generates evenAsFTA t14
--     True
--     ghci> generates evenAsFTA (Node "a" [t14])
--     False
--     ```

-- # Wh-in-situ dependencies

-- ## The basic pattern

-- In syntax classes you've probably talked about "wh-in-situ" languages (such as
-- Japanese, Mandarin, Turkish, Hindi, and many others), where wh-words that move
-- to the front of a question in languages like English instead stay in their base
-- position. So in a language which is wh-in-situ but otherwise like English ---
-- let's call it Whenglish --- a question formed from eg:wh:no:wh by asking
-- about the object position would look almost the same as eg:wh:no:wh, as
-- shown in eg:wh:in:situ, rather than eg:wh:movement where we see
-- the effect of wh-movement.

-- ::: ex
-- a.  Mary ate an apple yesterday     eg:wh:no:wh
-- a.  Mary ate what yesterday         eg:wh:in:situ
-- a.  what Mary ate yesterday         eg:wh:movement
-- :::

-- Let's assume that declarative sentences begin with a declarative complementizer
-- C, and interrogative sentences with an interrogative complementizer Q. In
-- English, the Q complementizer attracts the embedded 'wh' word, but in Whenglish,
-- it does not, as depicted in the trees below.


-- Evidence for the idea that there's a distinguished Q complementizer comes from
-- the fact that it's pronounced overtly in many languages. For example, in
-- Japanese it's pronounced 'no'; see eg:japanese:cooccurrence:ok, corresponding
-- to eg:wh:no:wh and eg:wh:in:situ. The C complementizer in the
-- declarative is unpronounced, like in English.Or perhaps we should say
-- it's pronounced as $\varepsilon$. The Q complementizer must co-occur with a
-- wh-word, and vice-versa, as shown in eg:japanese:cooccurrence:bad.

-- ::: ex
-- a.
-- | 
-- | John-wa ringo-o tabeta
-- | John-TOP apple-ACC ate
-- | 'John ate an apple'

-- a. 
-- |
-- | John-wa nani-o tabeta no
-- | John-TOP what-ACC ate Q
-- | 'What did John eat?' 
--   eg:japanese:cooccurrence:ok:question
-- :::

-- ::: ex
-- a.
-- |
-- | ^* John-wa ringo-o tabeta no
-- | John-TOP apple-ACC ate Q
-- | 

-- a.
-- |
-- | ^* John-wa nani-o tabeta
-- | John-TOP what-ACC ate
-- |

-- From this point of view, the _dependency_ between a wh-word and a Q
-- complementizer is similar to the dependency between an NPI and its licensing
-- negative element, which we discussed in class. Specifically, here's a complete
-- set of rules for well-formed trees in Whenglish:

-- -   Every wh-word must be c-commanded by a Q complementizer.

-- -   A single Q can license multiple wh-words that it c-commands, just like a
--     single negation can license multiple NPIs. When this happens it produces
--     "multiple questions", like the English 'Who ate what?'.

-- -   Every Q must c-command at least one wh-word. This is different from the
--     pattern with NPIs; a negative element need not c-command an NPI.

-- -   Any leaf node with a string in the list `qWords` is a Q complementizer.

-- -   Any leaf node with a string in the list `whWords` is a wh-word.

-- -   Other leaf nodes are allowed to have any string in the list `plainWords`.

-- -   Branching nodes should have exactly two daughters and the label ".".


-- @.  Define a (bottom-up) Finite Tree Automaton `wh1FTA` that enforces these
--     rules. You can choose whatever you like as the state type of the machine.
--     You might like to define a custom type for this purpose, like we did for
--     `polarityFTA`. (If you do, make sure you include `deriving (Eq,Show)`.)
--     
-- choose a type for q and uncomment this type declaration:

wh1FTA :: FTA Wh
data Wh = Q | Wh | Plain deriving (Eq,Show)

wh1FTA = FTAWith f (delta ++ v ++ w ++ x) where
  f = [Plain]
  delta = [ ([Q, Wh], ".", Plain) , ([Plain, Wh], ".", Wh),
            ([Wh, Plain], ".", Wh), ([Plain, Plain], ".", Plain),
            ([Wh, Wh], ".", Wh), ([Wh, Q], ".", Plain)
          ]
  v = [ ([], w, Q) | w <- qWords ]
  w = [ ([], w, Wh) | w <- whWords ]
  x = [ ([], w, Plain) | w <- plainWords ]

--     ```{.shell}
--     ghci> generates wh1FTA tree_1a
--     True
--     ghci> generates wh1FTA tree_1b
--     True
--     ghci> generates wh1FTA tree_3a
--     False
--     ghci> generates wh1FTA tree_3b
--     False
--     ghci> generates wh1FTA (mrg (lf "Q") (lf "what"))
--     True
--     ghci> generates wh1FTA (mrg (lf "Q") (lf "Mary"))
--     False
--     ghci> generates wh1FTA (mrg (lf "C") (lf "what"))
--     False
--     ghci> generates wh1FTA (mrg (lf "Q") (mrg (lf "what") (lf "why")))
--     True
--     ghci> generates wh1FTA (mrg (lf "C") (mrg (lf "what") (lf "why")))
--     False
--     ghci> generates wh1FTA (mrg (lf "Q") (mrg (lf "John") (lf "what")))
--     True
--     ghci> generates wh1FTA (mrg (mrg (lf "Q") (lf "John")) (lf "what"))
--     False
--     ```

-- ## Island effects

-- You've probably also learned in syntax classes about the way wh-movement out of
-- certain kinds of structures, called **islands**, is disallowed. Here we'll
-- concentrate on **adjunct islands**.

-- - - -

-- Adjuncts include relative clauses, as bracketed eg:adjunct:rc, and
-- 'because'-clauses, as in eg:adjunct:bc.

-- ::: ex
-- a.  Mary likes the person [that bought books as a gift]
--     eg:adjunct:rc
-- a.  Mary laughed [because John bought books as a gift]
--     eg:adjunct:bc
-- :::

-- As a result, sentences that attempt to move a wh-word out of these constituents
-- are ungrammatical[^1]

-- ::: ex
-- a.  ^* What does Mary like the person that bought \gap as a gift for John?
-- a.  ^* Why does Mary like the person that bought books \gap?
--     eg:english:rc:island
-- :::

-- ::: ex
-- a.  ^* What did John laugh [because Mary bought \gap as a gift]?
-- a.  ^* Why did John laugh [because Mary bought books \gap]?
--     eg:english:bc:island
-- :::

-- [^1]: The interrogatives in eg:english:rc:island and
--     eg:english:bc:island are trying to get at questions that would be
--     answered by "as a gift", where the 'why' asks for the reason that the books
--     were bought, not the reason for the liking/laughing.

-- Interestingly, the configurations that block wh-movement in these English
-- examples can also disrupt the dependency between Q and in-situ wh-words. Here's
-- some relevant data from Mandarin Chinese, showing adjuncts in brackets.

-- ::: ex
-- |
-- | ^* ni zui xihuan [ weishenme mai shu de ] ren ?
-- | you most like why buy book de person
-- | 'Why do you like the person that bought books?'
-- :::

-- ::: ex
-- |
-- | ^* ta [ zai Lisi weishenme mai shu  yihou ] shengqi le ?
-- | he  at Lisi why buy book after angry le
-- | 'Why did he get angry after Lisi bought books?'
-- :::

-- And here's something along the same lines from Japanese.

-- ::: ex
-- |
-- | ^* Mary-ga [ John-ni naze hon-o ageta ] hito-ni atta no ? 
-- | Mary-nom John-dat why book-acc gave man-dat meet q
-- | Why did Mary meet the man that gave books to John?
-- :::

-- So we'll assume that Whenglish follows the same pattern. 

-- @.  Define a (bottom-up) Finite Tree Automaton `wh2FTA`that enforces the same
--     basic dependency pattern between Q and wh-words as in `wh1FTA`, and
--     additionally guarantees that the licensing Q for a wh-word is not separated
--     from it by an adjunct island boundary. You will probably find that you can
--     use the same states you used for `wh1FTA` here, though you don't have to. We
--     will use `"*"` as a non-leaf symbol to identify (the root nodes of)
--     adjuncts. Specifically:
--     
--     -   All of the rules from `wh1FTA` above still apply, _except that_
--         branching nodes can now be labeled either `"."` or `"*"`.
--     
--     -   A constituent whose root node has the label `"*"` is an adjunct.
--     
--     -   If a wh-word is contained within an adjunct, then it can only be
--         licensed by a Q complementizer that is also within that adjunct. And
--         still, every Q complementizer must license at least one wh-word in this
--         way.

--     Here's a tree that should **not** be generated by `wh2FTA`, for example. It
--     is defined for you in `FTA.hs`{.tt} as `tree_13`.

-- choose a type for q and uncomment this type declaration:

wh2FTA :: FTA Wh
wh2FTA = FTAWith f (delta ++ v ++ w ++ x) where
  f = [Plain, Q]
  delta = [ ([Q, Wh], ".", Plain),  ([Plain, Wh], ".", Wh),
            ([Wh, Plain], ".", Wh), ([Plain, Plain], ".", Plain),
            ([Wh, Wh], ".", Wh), ([Plain, Plain], "*", Plain),
            ([Q, Wh], "*", Plain), ([Wh, Q], "*", Plain)
          ]
  v = [ ([], w, Q) | w <- qWords ]
  w = [ ([], w, Wh) | w <- whWords ]
  x = [ ([], w, Plain) | w <- plainWords ]
 

{-

this version is if you assume that only complementizers and "because" can start adjuncts
(and assuming that complementizers on the right is okay)

data Wh = Q | Wh | Plain | Adj deriving (Eq,Show)
wh2FTA :: FTA Wh
wh2FTA = FTAWith f (delta ++ v ++ w ++ x) where
  f = [Plain, Q]
  delta = [ ([Q, Wh], ".", Plain),  ([Plain, Wh], ".", Wh),
            ([Wh, Plain], ".", Wh), ([Plain, Plain], ".", Plain),
            ([Wh, Wh], ".", Wh), ([], "because", Adj),
            ([], "C", Adj), ([Adj, Plain], "*", Plain),
            ([Plain, Adj], "*", Plain), ([Q, Wh], "*", Plain),
            ([Wh, Q], "*", Plain)
          ]
  v = [ ([], w, Q) | w <- qWords ]
  w = [ ([], w, Wh) | w <- whWords ]
  x = [ ([], w, Plain) | w <- plainWords ]

-}


--     ```{.shell}
--     ghci> generates wh2FTA tree_13
--     False
--     ghci> generates wh2FTA (Node "." [Node "Q" [], Node "*" [Node "C" [], Node "why" []]])
--     False
--     ghci> generates wh2FTA (Node "." [Node "Q" [], Node "." [Node "C" [], Node "why" []]])
--     True
--     ghci> generates wh2FTA (Node "." [Node "Q" [], Node "*" [Node "C" [], Node "why" []]])
--     False
--     ghci> generates wh2FTA (Node "." [Node "C" [], Node "*" [Node "Q" [], Node "why" []]])
--     True
--     ```
