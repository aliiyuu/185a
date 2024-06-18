{-# LANGUAGE NoImplicitPrelude #-}
{-# LANGUAGE FlexibleInstances #-}


module PROJ2 where 


-- The only bits of the standard Haskell library that will be available to you
-- are the things you see imported here:



import Regexp
import Prelude
  ( -- that basic types that we've seen for integers, booleans, characters, and strings
    Int, Bool(True, False), Char, String
    -- the type constructor Maybe (and its data constructors, Just and Nothing)
  , Maybe(..)
    -- some basic arithmetic operations and relations:
  , (+), (-), (*), (<), (>), (==), (>=), (<=)
  , maximum, minimum, max, min, sum, product, mod
    -- some basic boolean operations:
  , (&&), (||), not, otherwise
    -- some list and tuple inspection and processing functions
  , take, drop, or, and, any, all, map, filter, concat, splitAt, reverse
  , elem, (++), (.), words, length, head, tail, fst, snd, null, lookup
    -- and some classes for showing and comparing things (don't worry about these)
  , Show(..), Eq(..), ($), putStrLn, undefined
  )


-- Your task is to fill in the definitions below according to the instructions
-- in the comments (which are also in the pdf version of the assignment). Note
-- that the word `undefined` is a placeholder for what you will write, so make
-- sure you have deleted (and replaced!) every occurrence you see. At any
-- point, you can load this file into ghci, where you should be able to
-- evaluate your expressions to see if they do what you want them to do.

-- To load this file into ghci on the command line, you will need to change to
-- whatever directory you've put this file in, and then make sure that the
-- accompanying Regexp and FSA files are also in that directory. Then
-- you just type:
--   > ghci PROJ2.hs
-- and you should be able to go. You can check to see if one of the functions
-- is in scope by asking ghci for its type with `:type` (or `:t` for short)
--   ghci> :type remainder
--   remainder :: Char -> Regexp -> Regexp
-- Whenever you make a change to the file, you'll need to reload it in ghci
-- with `:reload` (or `:r` for short)
--   ghci> :reload


-- ::: {#center}
-- **Ling 185A: RE conversion project**

-- Dylan Bumford

-- due: Fri, Mar 22
-- :::

-- # Converting regular expressions to deterministic machines

-- In class, and in HW4, we wrote an algorithm to convert a regular expression to a
-- finite state machine. That machine, however, used "epsilon-transitions" to move
-- freely from some states to others without consuming any of the input. This
-- prevents us from using the normal FSA parsing functions like `walk` and
-- `accepts`, which only take steps when they consume characters. So to get a
-- usable machine from the regular expression, we had to subsequently convert the
-- `EpsFSA` to a real `FSA`.

-- This project invites you to consider an alternative method for converting
-- `Regexp` directly to an `FSA` without wasting time with epsilon-transitions. In
-- fact, we will convert the `Regexp` directly to a **deterministic** `FSA`: one in
-- which there is always exactly one choice of which state to transition to.

-- # Semiring equations

-- Recall that a type is a monoid if there is an operation `(<>)` on its values
-- that is associative and has an identity element.

-- ::: {#minisplit opts=[0.28][c]}

class Monoid a where
  idty :: a
  (<>) :: a -> a -> a

-- +split

-- -   `(x <> y) <> z == x <> (y <> z)`
-- -   `idty <> x == x`
-- -   `x <> idty == x`

-- :::

-- And a monoid is a semiring if there is an operation `summarize` that its monoid
-- operation distributes over. That is, for any value `k` and list `vals`, the
-- equations on the right hold.

-- ::: {#minisplit opts=[0.28][c]}

class Semiring a where
  summarize :: [a] -> a

-- +split

-- -   `summarize [k <> x | x <- vals] == k <> summarize [x | x <- vals]`
-- -   `summarize [x <> k | x <- vals] == summarize [x | x <- vals] <> k`

-- :::


-- Think of adding up a bunch of numbers each multiplied by `k`; you could simplify
-- your life by just adding the numbers straight up and then multiplying the total
-- by `k`.

-- The distributivity law tells you more than meets than eye. Let's call the result
-- of summarizing an empty list `empty`, so `empty = summarize []`. What happens
-- when you apply the monoid operation to `(<>)` to a value `k` by `empty`: `k <>
-- empty == ...` Well, a little reasoning shows that _for any semiring whatsoever_:

-- ```
--    k <> empty
-- == k <> summarize []            -- by definition of empty
-- == summarize [k <> x | x <- []] -- by distributivity
-- == summarize []                 -- by definition of list comprehension
-- == empty
-- ```

-- For instance, in the boolean semiring, `(<>) = (&&)` and `summarize = or`. So
-- `empty == or [] == False`. And indeed, `k && False == False` no matter what `k`
-- is.

-- Similarly,

-- ```
--    empty <> k
-- == summarize [] <> k            -- by definition of empty
-- == summarize [x <> k | x <- []] -- by distributivity
-- == summarize []                 -- by definition of list comprehension
-- == empty
-- ```

-- # Regular semirings

-- We saw that lists form a monoid under concatenation:

instance Monoid [a] where
  idty = []
  xs <> ys = xs ++ ys

-- For any list `xs`, concatenating `xs` with `[]` just returns the same list `xs`.
-- And for any lists `xs`, `ys`, and `zs`, it doesn't matter if you glue `xs` to
-- `ys` and then the result to `zs`, or glue `xs` to the result of gluing `ys` to
-- `zs`. You get the same big list either way.

-- Regular expressions also form a monoid under concatenation:

instance Monoid Regexp where
  idty = One
  r <> s = r <.> s

-- That is, any string that matches `(r <.> s) <.> t` also matches `r <.> (s <.>
-- t)`, and vice versa. Which regular expression is the identity element for
-- `(<.>)`? This expression `i` should have the property that `i <.> r` matches all
-- the same strings as `r` does (and likewise for `r <.> i`).

-- It turns out, regular expressions also form a semiring! Find a definition for
-- `summarize` that makes the semiring laws true:

instance Semiring Regexp where
  summarize [] = Zero
  summarize (re:res) = case res of {[] -> re; _ -> re <|> (summarize res)}

-- You should check your definition by constructing some simple `Regexp`s and
-- testing that `<.>` distributes over your definition of `summarize`. For instance:

-- ```{.shell}
-- ghci> (r, s) = (str "a", str "b" <|> str "c")
-- ghci> k = rep (str "d")
-- ghci> dist u = match (k <> summarize [r, s]) u == match (summarize [k <> r, k <> s]) u
-- ghci> all dist ["a", "b", "ddd", "ddc", "addb", "dddda"]
-- ```

-- Notice that the `(<.>)` defined in `Regexp.hs`{.tt} takes some shortcuts when
-- building complex expressions. Those shortcuts are just exactly the algebraic
-- facts discussed here. Which lines take advantage of the fact that `(<.>)` is the
-- monoid action for `Regexp`, and which take advantage of the fact that `Regexp`
-- is a semiring?

-- ```{.haskell minted="{texcomments=false}"}
 {- 
These lines take advantage of the fact that <.> is the monoid action for a Regexp:
One  <.> e    = e
e    <.> One  = e
This is basically using the fact that One is the identity for a regular expression. and that 
<.> is the associative binary operation. Anything <.>'d with One is still that value.
Zero <.> e    = Zero
e    <.> Zero = Zero
These lines may take advantage of the fact that the Alt function distributes over concatenation,
and that REs are semirings.
Since we are pulling values from an empty list (or a RE that matches nothing), the result of the
concatenation is nothing, or Zero based on semiring laws.
 -}
-- ```

-- # Warm up

-- Our encoding of FSAs is **nondeterministic**: a character `c` may lead to
-- several (or no) next states. For instance, in the simple FSA on the left, from
-- state 1, a `C`{.tt} can transition to state 1 or state 2.

-- :::::::::::::: {#minisplit opts=[0.5][c]}

-- $$tikzpicture
--   \node [state,initial] (1) {1};
--   \node [state,] at (2.5,0) (2) {2};
--   \node [state,accepting] at (5,0)  (3) {3};
--   \draw (1) edge[loop above] node{C} (1);
--   \draw (1) edge[loop below] node{V} (1);
--   \draw (1) edge node {C} (2);
--   \draw (2) edge node {V} (3);
-- tikzpicture$$

-- +split

-- $$tikzpicture[node distance=2cm]
--   \node [state,initial] (1) {1};
--   \node [state, right=of 1] (12) {2};
--   \node [state, above=1cm of 12,accepting] (13) {3};
--   \draw (1) edge node{C} (12);
--   \draw (1) edge[loop above] node{V} (1);
--   \draw (12) edge[loop right] node{C} (12);
--   \draw (12) edge[bend right] node[sloped=false]{V} (13);
--   \draw (13) edge[bend right] node[sloped=false]{C} (12);
--   \draw (13) edge node{V} (1);
-- tikzpicture$$

-- ::::::::::::::

-- In a **deterministic** automaton, things are simpler. For any character `c` and
-- state `q`, there is exactly one transition leaving `q` and consuming `c`, so you
-- always know exactly where to go next. For instance, the automaton above on the
-- right is equivalent to the one on the left, but at every state there's exactly
-- one transition per character. The transitions of such a machine may be encoded
-- as a _function_ rather than a _table_. And there can only be one start state.
-- Compare the data types of `FSA` and `DFA` below.

-- ::: {#minisplit opts=[0.5]}

-- ```
-- type State = Int
-- type TransL = [(State, Char, State)]
-- data FSA =
--  FSAWith [State] [Char] [State] [State] TransL
--  --        $Q$      $\Sigma$       $I$       $F$      $\Delta$
-- ```

-- +split

type State = Int
type TransF = (State, Char) -> State
data DFA =
 DFAWith [State] [Char] State [State] TransF
 --        $Q$      $\Sigma$      $I$      $F$      $\Delta$

-- :::

-- For instance, the deterministic machine above might be encoded as:

myDFA = DFAWith qs ss q0 fs tf where
  qs = [1,2,3]
  ss = "CV"
  q0 = 1
  fs = [3]
  tf = \(q,c) -> case (q,c) of
    (1, 'C') -> 2; (1, 'V') -> 1
    (2, 'C') -> 2; (2, 'V') -> 3
    (3, 'C') -> 2; (3, 'V') -> 1

-- To write a parser for a deterministic machine, we replace all of the
-- _nondeterinistic_ state transitions of the form `State -> [State]` with
-- _ordinary functions_ of the form `State -> State`. Test your definitions by
-- parsing a few strings with `myDFA` (or any other DFA you define).

-- ::: {#minisplit opts=[0.52]}

-- ```
-- -- FSA parsing functions designed to transit
-- -- from one state to a list of next states

-- return :: a -> [a]
-- return = \a -> [a]

-- (>=>) :: (a -> [b]) -> (b -> [c]) -> (a -> [c])
-- f >=> g = \a -> [c | b <- f a, c <- g b]

-- step :: TransL -> Char -> State -> [State]
-- step trs c =
--   \q -> [r | (s,x,r) <- trs, s == q, x == c]

-- walk :: TransL -> String -> State -> [State]
-- walk trs ""     = return
-- walk trs (c:cs) = step trs c >=> walk trf cs

-- accepts :: FSA -> String -> Bool
-- accepts (FSAWith _ _ is fs ds) u =
--  or [elem qf fs | qi <- is, qf <- walk ds u qi]
-- ```

-- +split

-- DFA parsing functions designed to transit
-- from one state to exactly one next state

quit :: a -> a
quit = \a -> a 

(>->) :: (a -> b) -> (b -> c) -> (a -> c)
f >-> g = \a -> g (f a)

dstep :: TransF -> Char -> State -> State
dstep tf c =
  \q -> tf (q, c)

dwalk :: TransF -> String -> State -> State
dwalk tf ""     = quit
dwalk tf (c:cs) = dstep tf c >-> dwalk tf cs

daccepts :: DFA -> String -> Bool
daccepts (DFAWith _ _ q0 fs tf) u = elem (dwalk tf u q0) fs

-- :::

-- Eventually, you'll need to be able to add new transitions to a partially
-- built-up `TransF` function. Might as well write that auxiliary function now.
-- Given a function `f`, a key `k` and a value `v`, return a new function that is
-- just like `f` except that when its argument is equal to `k` then it returns `v`
-- (otherwise it just returns whatever it would have returned before).

extend :: Eq k => (k -> v) -> k -> v -> (k -> v)
extend f k v = \k' -> if k' == k then v else (f k')


-- # The Idea

-- Here is the main idea for the conversion procedure we'll follow. We are going to
-- build an DFA whose states are regular expressions. The initial state will be the
-- regular expression we are aiming to convert, and each transition will take us from a
-- one regular expression to another. What should the transitions be? Well, imagine
-- we're at a regular expression `re`, and we then consume a character `c`. What
-- regular expression should we move to? Answer: one that is just like `re`, except
-- that it just matches the stuff that can come after `c`.

-- For example, say we know that

-- ```{.shell}
-- ghci> mset re
-- ["cat", "catt", "cattt", "dog", "dogg", "doggg"]
-- ```

-- Then after consuming `c`, we would want to transition to an expression `re'`
-- such that

-- ```{.shell}
-- ghci> mset re'
-- ["at", "att", "attt"]
-- ```

-- That is, it matches all of the `c`-suffixes of strings that `re` matched. Or put
-- another way, if `re` matches a string that starts with `c`, then `re'` should
-- match the tail of that string:
-- if `match re (c:u) == True`, then `match re' u == True`.
-- In an equation:

-- $$\mytt re' = x_1\cdots x_n \giv cx_1\cdots x_n \in \mytt re$$

-- To build out the machine, we'll just need to iterate this process, consecutively
-- reducing regular expressions one character at a time, so to speak. Here's a
-- picture:

-- $$tikzpicture
-- \node [state,initial,inner sep=0pt] at (0,0) (0) {$\mytt ab\ror ac$};
-- \node [state,right of=0] (1) {$\mytt b\ror c$};
-- \node [state,below of=1] (2) {$\emptyset$};
-- \node [state,right of=1,accepting] (3) {$\varepsilon$};
-- \draw (0) edge node[sloped] {a} (1);
-- \draw (0) edge[bend left =20] node {b} (2);
-- \draw (0) edge[bend right=20] node {c} (2);
-- \draw (1) edge node {a} (2);
-- \draw (1) edge[bend left =20] node {b} (3);
-- \draw (1) edge[bend right=20] node {c} (3);
-- tikzpicture$$

-- The original RE `(ab|ac)` matches `"ab"`{.tt} and `"ac"`{.tt}. After reading
-- `'a'`{.tt}, it transitions to the RE `(b|c)`, which matches `"b"`{.tt} and
-- `"c"`{.tt}, since these are the strings that can come after `'a'`{.tt}. However,
-- after consuming either `'b'`{.tt} or `'c'`{.tt}, it transitions to
-- `?$\emptyset$?`, which doesn't match anything because there are no matches to
-- `(ab|ac)` that begin with either `'b'`{.tt} or `'c'`{.tt}. Then the process
-- repeats at `(b|c)`. This RE matches `"b"`{.tt} and `"c"`{.tt}. So after reading
-- either `'b'`{.tt} or `'c'`{.tt}, it transitions to `?$\varepsilon$?`, which
-- matches the empty string. This makes sense, since there are no more characters
-- left to consume (the empty string is what follows `'b'`{.tt} and `'c'`{.tt} in
-- `"b"`{.tt} and `"c"`{.tt}).

-- More generally, we should be able to stop at any regular expression that accepts
-- the empty string. So write a function `emptyOK` that returns `True` if its
-- argument matches the empty string, and `False` if it does not.

emptyOK :: Regexp -> Bool
emptyOK re = case re of
  Zero    -> False
  One     -> True
  Lit _   -> False
  Alt r s -> emptyOK r || emptyOK s
  Cat r s -> emptyOK r && emptyOK s
  Star r  -> True

-- ```{.shell}
-- ghci> emptyOK (One <|> str "ab")
-- True
-- ghci> emptyOK (str "ab" <|> str "ac")
-- False
-- ghci> emptyOK (str "a" <|> rep (str "b"))
-- True
-- ```

-- Remember you can check your results for an arbitrary regular expression `re` by
-- comparing `emptyOK re` to `match re ""`.

-- # Remainders

-- The most important component of this procedure is the function that reduces a
-- regular expression by a single initial character. We'll call this the
-- `remainder` of `re` after `c`. Given a regular expression `re` and a character
-- `c`, it should return a new regular expression that matches exactly the strings
-- that follow `c`, according to `re`.

-- Start with the base cases. Let's say `re` is `Zero`. This matches nothing, so
-- there are no strings that come after `c`, i.e., no `c`-remainders. So the result
-- is still `Zero`. Moving on, `One` matches only the empty string. Since this does
-- not start with `c`, there are again no `c`-remainders, so the result is also
-- `Zero`. How about `Lit ?$a$?`? This matches only the string whose only character
-- is `?$a$?`. If `?$a$?` is `c`, then there is exactly one `c`-remainder: the
-- empty string (since `"c" = 'c':""`). But if `?$a$?` is not `c`, then there are
-- again no `c`-remainders.

remainder :: Regexp -> Char -> Regexp
remainder re c = case re of
  Zero    -> Zero
  One     -> Zero
  Lit a   -> if a == c then One else Zero

-- Now things get interesting. Every string that matches `Alt r s` is either an
-- `r`-type string or an `s`-type string. So the `c`-suffixes of this set are all
-- either a `c`-suffix of an `r`-string or a `c`-suffix of an `s`-string.

  Alt r s -> (remainder r c) <|> (remainder s c)

-- Next up, `Cat r s` matches an `r`-type string followed by an `s`-type string.
-- How would you characterize the `c`-remainders of such `r ++ s`-strings? Make
-- sure you think about the case where `r` can match the empty string. Write a
-- regular expression to characterize these `c`-remainders.

  Cat r s -> if emptyOK r then ((remainder r c) <.> s) <|> (remainder s c) else (remainder r c) <.> s
-- Finally, `Star r` matches any number of consecutive `r`-type strings. How would
-- you characterize the set of strings that you get by lopping off the initial `c`s
-- from this set (and eliminating those strings that don't start with `c`)?

  Star r -> remainder r c <.> rep r
 
-- Test your function on a number of examples:

-- ```{.shell}
-- ghci> re = ...
-- ghci> and [ match (remainder re c) u | (c:u) <- take 100 (mset re) ] 
-- ```

-- Actually, while we're here, might as well write a new match function, since the
-- `remainder` notion opens up a new very simple recursive definition.

matchRem re ""     = emptyOK re
matchRem re (c:cs) = matchRem (remainder re c) cs

-- # Building the machine recursively

-- As described above, we will convert a regular expression to an automaton by
-- calculating successive remainders. To do this recursively, we'll build the
-- machine up as we whittle down the expression.

-- ## Preliminaries

-- First, let's fix some alphabet here that will be shared across your regular
-- expressions and your machines. (Feel free to change this.)

type Alphabet = [Char] -- $\Sigma$
sigma :: Alphabet
sigma = "abcd"

-- We'll be associating states in the machine we build with regular expressions.
-- So, as with the `compress` function in our transducers, we'll want to keep a
-- dictionary around mapping `Regexp`s to `State`s. And at any given point, we'll
-- have built part of the total eventual machine, so a dictionary of the states
-- and transitions assembled so far.

type REDict = [(Regexp, State)]
type PartialMachine = (REDict, TransF)

-- Here's the idea. Say we're standing at a state `q` associated with an expression
-- `re`. For each character `c` in the alphabet, we need to build a state
-- representing the remainder of `re` after `c`. Then we need to move to those new
-- states and repeat the process. But we have to be a little bit clever about how
-- we do this or else it would just go on forever. We might be at a state
-- representing `Zero`, find out its `c`-remainder is `Zero`, add a new state also
-- representing `Zero`, and then repeat. To make sure this terminates, instead of
-- adding a _new_ state also representing `Zero`, we should just add a loop from
-- the state we already have back to itself. More generally, whenever we find out
-- that we already have a state associated with `remainder re c`, we should add an
-- arc back to that existing state, rather than creating a new one.

-- We'll do this with a pair of mutually recursive functions `along` and `across`
-- (quite similar to the `combine` and `parse` functions for CFGs, or even more
-- similar to the simple `even` and `odd` functions). The first one, `along`,
-- calculates a single remainder for a single character, adds a single transition
-- to that remainder, and then hands control over to `across`. That latter
-- function, `across`, calls `along` for each character in the alphabet to add the
-- relevant next transitions. The result is a ratcheting action:

-- Importantly, you want to define `across` so that it calls `along c1`, `along
-- c2`, ..., in sequence, passing the updated machine after each `along` in as
-- input to the next `along`. This is because you might need to connect states you
-- build in later steps to states you build in earlier ones (remember, the goal
-- here is to avoid adding duplicate states). You might think of `along` as taking
-- a single step in the machine-building process, and `across` as taking repeated
-- steps until you run out of symbols in the alphabet, at which point the machine
-- can be returned as is.

across :: (Regexp, State) -> (PartialMachine -> PartialMachine)
across qi = go qi sigma
  where -- recurse over the alphabet, building a big machine update pipeline
        -- that updates by running along the first symbol, then updating
        -- the resulting machine by running along the second, and so on
        go :: (Regexp, State) -> Alphabet -> (PartialMachine -> PartialMachine)
        go qi []     = \m -> m
        go qi (c:cs) = \m -> along qi c (go qi cs m)

-- Now, onto the dirty work. `along` builds out the machine from the current
-- RE/state by transitioning along a given character to its remainder. If that
-- remainder is already in the machine, then it will just need to add the new arc
-- to it. But if it's not already in the machine, then it will need to add it
-- together with the arc to it, and then start the whole `across/along` building
-- operation at the new state.

along :: (Regexp, State) -> Char -> (PartialMachine -> PartialMachine)
along (q0, i0) c = \(dict, arcs) -> 
  -- calculate the re corresponding to the strings you can accept after c
  let qc = remainder q0 c

  -- check to see if there is already a state
  -- in the machine corresponding to that remainder
  in case lookup qc dict of
                             
    -- if so, leave the states as they are (nothing to add)
    -- and add a new arc from the current state to the remainder state
    Just ic -> (dict, extend arcs (i0, c) ic)


    -- if not, then you'll need to add it to the machine's dictionary
    -- in addition to adding the new edge
    Nothing ->
      let -- allocate a new state not yet assigned to any RE in the dictionary
          ic    = maximum ([snd x | x <- dict]) + 1
          -- add the new (remainder, state) pair to the dictionary
          dict' = dict ++ [(qc, ic)]
          -- add an edge from the current state to the new one
          arcs' = extend arcs (i0, c) ic
      in
      -- now build up the rest of the machine starting from the new state
      across (qc, ic) (dict', arcs')

-- ## Putting it together

-- Define the initial configuration of the machine, with a single state for the
-- RE you're aiming to convert.

initialState :: Regexp -> (Regexp, State)
initialState re = (re, 0) -- the first state of the partial machine

-- Note that you don't need to (and shouldn't!) change this instance of 'undefined',
-- since there are no transitions yet, so the function is in fact undefined
initialMachine :: Regexp -> PartialMachine
initialMachine re = ([initialState re], undefined) 

-- All that's left is to write the function. Remember, an RE/state is final if it
-- matches the empty string (at which point you've consumed all the characters you
-- need, so you should stop).

reToDFA :: Regexp -> DFA
reToDFA re = DFAWith qs sigma q0 fs arcs
  where
    -- build the machine out from the initial configuration
    (dict, arcs) = across (initialState re) (initialMachine re)

    -- start with the state you assigned to the initial RE
    q0 = snd (initialState re)
    -- extract the states from the dictionary
    qs = [snd x | x <- dict] 
    -- decide which of those states are final
    fs = [snd x | x <- dict, emptyOK (fst x)]

-- not sure if I am supposed to define sigma and arcs - maybe this is why these tests are failing but I doubt it

-- Test your results on a few REs. Make sure you test both that the DFA resulting
-- from conversion accepts the strings that the RE matches and that it rejects the
-- strings that the RE doesn't match.

-- ```{.shell}
-- ghci> re = ...
-- ghci> and [ daccepts (reToDFA re) u | u <- take 100 (mset re) ]
-- ghci> and [ not (daccepts (reToDFA re) u) | u <- [.. some strings re doesn't match ...]]
-- ```



------------------------------------------------------------------------
-- a convenience function print the FSA out in a slightly more readable
-- format in ghci
------------------------------------------------------------------------

showDFA (DFAWith states sigma initials finals delta) = do
  putStrLn $ "states:      " ++ show states
  putStrLn $ "alphabet:    " ++ show sigma
  putStrLn $ "initial:     " ++ show initials
  putStrLn $ "final:       " ++ show finals
  putStrLn $ "transitions: " ++ show [(s, c, delta (s,c)) | s <- states, c <- sigma]
