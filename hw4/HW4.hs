{-# LANGUAGE NoImplicitPrelude #-}


module HW4 where 


-- The only bits of Haskell that will be available to you in this assignment
-- are the things you see imported here at the top. In particular, the only
-- pre-defined Haskell functions and types that you'll be able to use are the
-- ones you see in `import Prelude` block. Do not change anything in this
-- import block.

import FSA    -- all the functions exported by our FSA.hs file
import Regexp
  ( -- the type and constructors for Regexp
    Regexp(..)
    -- functions to build up Regexps
  , zero, one, char, (<|>), (<.>), rep
    -- functions to generate strings from a Regexp and/or see if
    -- a String matches a Regexp
  , mset, match
  )
import Prelude
  ( -- that basic types that we've seen for integers, booleans, characters, and strings
    Int, Bool(True, False), Char, String
    -- the type constructor Maybe (and its data constructors, Just and Nothing)
  , Maybe(..)
    -- some basic arithmetic operations and relations:
  , (+), (-), (*), (<), (>), (==), maximum, minimum
    -- some basic boolean operations:
  , (&&), (||), not
    -- some list inspection and processing functions
  , take, drop, or, and, any, all, map, filter, concat, elem, (++)
    -- and some classes for showing and comparing things (don't worry about these)
  , Show, Eq, undefined
  )
import Data.Char (ord)


-- Your task is to fill in the definitions below according to the instructions
-- in the comments (which are also in the pdf version of the assignment). Note
-- that the word `undefined` is a placeholder for what you will write, so make
-- sure you have deleted (and replaced!) every occurrence you see. At any
-- point, you can load this file into ghci, where you should be able to
-- evaluate your expressions to see if they do what you want them to do.

-- To load this file into ghci on the command line, you will need to change to
-- whatever directory you've put this file in, and then make sure that the
-- accompanying FSA.hs and Regexp.hs files from BruinLearn are also in that
-- directory. Then you just type:
--   > ghci HW3.hs
-- and you should be able to go. You can check to see if one of the functions
-- is in scope by asking ghci for its type with `:type` (or `:t` for short)
--   ghci> :type accepts
--   accepts :: FSA -> String -> Bool
-- Whenever you make a change to the file, you'll need to reload it in ghci
-- with `:reload` (or `:r` for short)
--   ghci> :reload

-- ::: {.tex-center}
-- **Ling 185A: Assignment 4**

-- Dylan Bumford, Winter 2023 

-- due: Wed, Feb 7
-- :::

-- # Preambles

-- In any given FSA, the ambit of a string `u` is the set of states you could _end
-- in after_ reading `u` if you _start in an initial state_. We might just as well
-- be interested in the converse notion: the set of states you could _start in
-- before_ reading `u` if you _end in a final state_. Let's call this set the
-- **preamble** of the string. It's the states you can be in before walking along
-- `u` if you want to make it to the end of the machine. If you think of the string
-- as the tank of gas that you burn through while `walk`ing, then the ambit is how
-- far away you can get from the initial states on that tank, and the preamble is
-- how far away you can be from the final states in order to get there when you run
-- out of gas.

-- Anyway, in code:

preambleDef :: FSA -> String -> [State]
preambleDef fsa u = [ q | q <- states fsa, any accepting (walk fsa u q) ]
  where accepting = \q -> elem q (finals fsa)      

-- That is, the preamble of `u` is the set of states `q` such that there's a way to
-- `walk` via `u` from `q` to some accepting state.

-- (@) This code is fine as a definition, but it's not very constructive. It
--     calculates the preamble by simply trying every single state in the machine
--     and checking for each one if there is some path via `u` that lands on a
--     final state. There is a smarter way to generate this set: we just need to
--     walk through the machine backwards! So for this problem you're going to
--     define a parser that takes as input the state you want to end at, and then
--     reverses through the automaton a step at a time. You will certainly want to
--     consult the `step`, `walk`, and `ambit` functions in the `FSA.hs`{.tt}
--     library for inspiration, but don't use these functions in your code. (It is
--     possible to solve this problem by inverting all the arrows of the FSA,
--     swapping the initial and final states, reversing the input string, and then
--     just taking the reversed string's `ambit` in the inverted machine. I am not
--     interested in that solution.)
--     
--     #.  Define a function `stepBack` that, when given an FSA and a character `c`,
--         returns a function that maps any state `q` to the set of source states that
--         transition along `c` to reach `q`.

stepBack :: FSA -> Char -> State -> [State]
stepBack fsa c = \q -> [ s | (s,x,r) <- ttable fsa, r == q, x == c ]

--     
--     #.  Define a function `backPedal` that, when given an FSA and a string `u`,
--         returns a function that maps any state `q` to the set of states from
--         which there is a path ending at `q` that consumes `u`. This is the
--         interesting, recursive bit. As always, think about the recursive case by
--         assuming that you have already solved the problem for the underlying layer
--         of the input, and figuring out what you need to do with the last little
--         bit to finish the problem off. Here, that means assuming that when you
--         call `backPedal` on the tail of the string `cs`, you get back a function
--         that maps states to the list of states you could start at before walking
--         forward to `q` consuming `cs`. It will definitely help to draw some
--         pictures. 
--     
backPedal :: FSA -> String -> State -> [State]
backPedal fsa     "" = return
backPedal fsa (c:cs) = backPedal fsa cs >=> stepBack fsa c
--         
--     #.  Now define a function `preamble` that `backPedal`s from the final
--         states of a machine in order to find the preamble of a string.
--     

preamble :: FSA -> String -> [State]
preamble fsa u = run()
  where 
    run = enterBackward fsa >=> backPedal fsa u
      where
        enterBackward fsa = \() -> finals fsa

--     #.  Finally, define an alternative acceptance function using your `preamble`
--         instead of `ambit`.

acceptsAgain :: FSA -> String -> Bool
acceptsAgain fsa u = any accepting (preamble fsa u)
  where accepting = \q -> elem q (starts fsa)

--         
--     You can test your code on any of the FSAs from the slides or from the
--     previous assignment, or any FSA you design. You can either figure out the
--     correct preambles for your test strings by eyeballing the states, or
--     comparing the results with `preambleDef` above.


-- # Strictly-local grammars

-- A **strictly-local grammar** (SLG) is a machine, much like an FSA, but simpler.
-- Instead of defining transitions as relations between states that consume a
-- symbol, we just define transitions as relations between symbols directly. No
-- states! To define an SLG, you need to specify four things:

-- -   $\Sigma$, the alphabet of symbols
-- -   $I$, the set of symbols that a sentence can start with
-- -   $F$, the set of symbols that a sentence can end with
-- -   $\Delta$, a set of pairs of symbols, indicating which symbols can come
--     after which other ones
--     
-- An SLG accepts a string $x_1x_2\dots x_n$ iff:

-- -   $x_1 \in I$
-- -   $(x_i, x_{i+1}) \in \Delta$, for all $1 \leq i < n$
-- -   $x_n \in F$

-- (@) Here is a Haskell data type encoding this simple kind of automaton:

type SLGTransition = (Char, Char)
data SLG = SLGWith [Char] [Char] [Char] [SLGTransition]
--                   $\Sigma$      $I$      $F$          $\Delta$

-- convenience functions
alphasSLG (SLGWith a i f d) = a 
startsSLG (SLGWith a i f d) = i
finalsSLG (SLGWith a i f d) = f
ttableSLG (SLGWith a i f d) = d

--     And here are a couple examples of such machines:

slg1, slg2 :: SLG
slg1 = SLGWith "CV" "C" "V" [('C','C'), ('C', 'V'), ('V', 'V')]
slg2 = SLGWith "abc" "abc" "abc"
            [('a','a'),('b','b'),('c','c'),('a','b'),('b','a'),('a','c'),('c','a')]

--     #.  Your first task is to write a function `acceptsSLG` that determines
--         whether a given `SLG` accepts a particular `String`. For instance, it
--         should give these results in `ghci`{.tt}. (Of course, it should also
--         work for any other `SLG` we give it, not just these examples.)
--         
--         ```{.shell}
--         ghci> acceptsSLG slg1 "CCV"
--         True
--         ghci> acceptsSLG slg1 "CV"
--         True
--         ghci> acceptsSLG slg1 "V"
--         False
--         ghci> acceptsSLG slg1 "VC"
--         False
--         ghci> acceptsSLG slg2 "ababac"
--         True
--         ghci> acceptsSLG slg2 "ababacb"
--         False
--         ghci> acceptsSLG slg2 ""
--         False
--         ``` 
--         
--         You certainly can do this in a manner that closely parallels the `step`,
--         `walk`, `ambit`, etc. strategy designed for FSAs, but in this case it
--         will probably be easier to just define `acceptsSLG` directly as a single
--         recursive function. Note that you should be a little careful with the
--         edge cases, since, for instance, an SLG by definition will never
--         accept the empty string.
--         

acceptsSLG :: SLG -> String -> Bool
acceptsSLG slg "" = False
acceptsSLG slg [c] = if ((elem c (finalsSLG slg)) && (elem c (startsSLG slg))) then True else False
acceptsSLG slg (c:cs) = if (((not (elem c (startsSLG slg))) || (not (checkTransitions slg (c:cs)))) || (not (checkLastChar slg (c:cs)))) then False else True
  where
    checkTransitions :: SLG -> String -> Bool
    checkTransitions slg [c] = True
    checkTransitions slg (c:cs) = all (\(a, b) -> (elem (a, b) (ttableSLG slg))) (pair (c:cs) (cs))
      where
        pair :: [a] -> [b] -> [(a, b)]
        pair [] _ = []
        pair _ [] = []
        pair (x:xs) (y:ys) = (x, y) : pair xs ys
    checkLastChar :: SLG -> String -> Bool
    checkLastChar slg [c] = if (elem c (finalsSLG slg)) then True else False
    checkLastChar slg (c:cs) = checkLastChar slg cs
    
--         
--     #.  Every SLG can be converted to an FSA that recognizes exactly the same
--         language. So your second task is to figure out how to do that.
--         Here are some examples to get you thinking.
--         
--         - - -
--         
--         The SLG `slg1` above is equivalent to `fsa1` below.
--         
--         ```{=latex}
--         fsa1 = fsaslg1.tex
--         ```
--         
--         - - -
--         
--         - - -
--         
--         And the SLG `slg2` above is equivalent to `fsa2` below.
--         
--         ```{=latex}
--         fsa2 = fsaslg2.tex
--         ```
--         
--         - - -
--         
--         Think about why these FSAs accept the same strings as the corresponding
--         SLGs, and try to suss out the pattern. Then write a function `slgToFSA`
--         that takes an `slg` and produces an equivalent FSA.
--         
slgToFSA :: SLG -> FSA
slgToFSA slg = FSAWith states syms i f delta
  where
    states = [1] ++ [ord x | x <- (alphasSLG slg)]
    syms = alphasSLG slg
    i = [1]
    f = [ord x | x <- (finalsSLG slg)]
    delta = [(1, x, (ord x)) | x <- startsSLG slg] ++ [((ord x), y, (ord y)) | (x, y) <- ttableSLG slg]

--         
--         Remember an SLG has no states, just direct transitions between symbols.
--         But of course an FSA does have states. So when you make the conversion,
--         you will have to choose some `Int`s for your states. Of course you can
--         choose any numbers you want, but you may be interested in the function
--         `ord :: Char -> Int` that maps characters to their standard ASCII codes,
--         which is already imported for you with this module.
--         
--         ```{.shell}
--         ghci> ord 'A' == 65
--         True
--         ghci> ord 'z' == 122
--         True
--         ```
--         
--         The imported `FSA.hs`{.tt} module also defines a function `showFSA`
--         that you can use to display the results of your conversion. For
--         instance, running
--         
--         ```{.shell}
--         ghci> showFSA (slgToFSA slg1)
--         ```
--         
--         should print out an encoding of `fsa1` above, if all has gone well. And
--         you can check that an SLG and the FSA it is converted to accept the same
--         strings by comparing the results of `acceptsSLG` and `accepts`:
--         
--         ```{.shell}
--         ghci> accepts (slgToFSA slg1) "CCV" == acceptsSLG slg1 "CCV"
--         True
--         ```
--         
-- # Converting REs to FSAs

-- In class, we considered a variant of FSAs that allow "free" transitions between
-- states, called **Epsilon Finite-State Automata**. Here we make that notion
-- precise.

-- ```
-- type EpsTransition = (State, Maybe Char, State)
-- data EpsFSA =
--   EpsWith [State] [Char] [State] [State] [EpsTransition]
-- ```

-- An $\epsilon$-transition is like a normal transition in that it has a source
-- state and a target state, and if it has a genuine label, that label is a
-- `Char`acter. But it might also have `Nothing` as its label, indicating that the
-- move can be made without consuming any characters.

-- - - -

-- Using this kind of machine, we sketched a proof that every Regular Expression
-- can be converted into a Epsilon Finite-State Automaton that recognizes exactly
-- the same language that the RE matches. Now it is time to make that proof
-- official by writing a function `reToFSA :: Regexp -> EpsFSA`.

-- (@) The procedure we outlined consisted in building bigger FSAs out of smaller
--     FSA components. Implementing this in code is mostly straightforward, but
--     there is one bookkeeping catch to keep in mind. If the two component FSAs
--     that you're gluing together happen to use the same numbers for some of their
--     states, you can end up unintentionally merging states that ought to be kept
--     separate.
--     
--     - - -
--     
--     Fortunately the numbers attached to the states never matter, so you can
--     always re-number them to avoid such collisions. Write a function that
--     increments all the state numbers in an `EpsFSA` by `n` (this will need to be
--     applied to _all_ of the relevant parts of the machine: $Q$, $I$, $F$, and
--     $\Delta$).
--     
statesEps (EpsWith q a i f d) = q -- some convenience functions
alphasEps (EpsWith q a i f d) = a -- for working with EpsFSAs
startsEps (EpsWith q a i f d) = i
finalsEps (EpsWith q a i f d) = f
ttableEps (EpsWith q a i f d) = d

shift :: Int -> EpsFSA -> EpsFSA
shift n epsFSA = EpsWith states syms i f delta
  where
      states = [(x + n) | x <- statesEps epsFSA]
      syms = alphasEps epsFSA
      i = [(x + n) | x <- startsEps epsFSA]
      f = [(x + n) | x <- finalsEps epsFSA]
      delta = [((x + n), c, (y + n)) | (x, c, y) <- ttableEps epsFSA]
--     
-- (@) Onto the real work. Write a function `unionFSA` that takes two `EpsFSA`s as
--     inputs and produces a new `EpsFSA` that recognizes any string that either of
--     the inputs recognizes. That is, it should accept any string that either
--     the first or the second (or both) would accept. Don't forget to use your
--     `shift` function to avoid state-clashes. You'll have to use one FSA to
--     decide what number to pick for `shift`ing the other. The function
--     `maximum :: [Int] -> Int`, imported in this assignment, may help.
--     
unionFSA :: EpsFSA -> EpsFSA -> EpsFSA
unionFSA eps1 eps2 = EpsWith states syms i f delta
  where
    shiftedEps2 = shift ((maximum ((statesEps eps1) ++ (statesEps eps2))) + 1) eps2
    
    states = statesEps eps1 ++ statesEps shiftedEps2
    syms = alphasEps eps1 ++ alphasEps eps2
    i = startsEps eps1 ++ startsEps shiftedEps2
    f = finalsEps eps1 ++ finalsEps shiftedEps2
    delta = ttableEps eps1 ++ ttableEps shiftedEps2

--     
-- (@) Write a function `catFSA` that takes two `EpsFSA`s as inputs and produces a
--     new `EpsFSA` that recognizes any string composed of a part recognized by the
--     first followed by a part recognized by the second.
--     
catFSA :: EpsFSA -> EpsFSA -> EpsFSA
catFSA eps1 eps2 = EpsWith states syms i f delta
  where
    shiftedEps2 = shift ((maximum ((statesEps eps1) ++ (statesEps eps2))) + 1) eps2

    states = statesEps eps1 ++ statesEps shiftedEps2
    syms = alphasEps eps1 ++ alphasEps eps2
    i = startsEps eps1
    f = finalsEps shiftedEps2
    delta = ttableEps eps1 ++ ttableEps shiftedEps2 ++ [(x, Nothing, y) | x <- finalsEps eps1, y <- startsEps shiftedEps2]

-- (@) Write a function `repFSA` that takes an `EpsFSA` as input and produces a new
--     `EpsFSA` that recognizes any string composed of a sequence of zero or more
--     sub-strings each of which would be recognized by the input machine.
--     
repFSA :: EpsFSA -> EpsFSA
repFSA eps = EpsWith states syms i f delta
  where
    emptyState = maximum (statesEps eps) + 1
    states = statesEps eps ++ [emptyState]
    syms = alphasEps eps
    i = [emptyState] 
    f = finalsEps eps ++ [emptyState]
    delta = ttableEps eps ++ [(x, Nothing, y) | x <- finalsEps eps, y <- startsEps eps] ++ [(emptyState, Nothing, x) | x <- startsEps eps]
      

-- (@) Time for the main event. Write a function `reToFSA` that translates any
--     `Regexp` to its corresponding `EpsFSA`.
--     
reToFSA :: Regexp -> EpsFSA
reToFSA re = case re of
  Zero    -> EpsWith states syms i f delta
    where
      states = [1]
      syms = []
      i = [1]
      f = []
      delta = []
  One     -> EpsWith states syms i f delta
    where
      states = [1]
      syms = []
      i = [1]
      f = [1]
      delta = []
  Lit c   ->  EpsWith states syms i f delta
    where
      states = [1, 2]
      syms = [c]
      i = [1]
      f = [2]
      delta = [(1, Just c, 2)]
  Alt r s -> unionFSA (reToFSA r) (reToFSA s)
  Cat r s -> catFSA (reToFSA r) (reToFSA s)
  Star r  -> repFSA (reToFSA r)

--     To test your conversion, you'll need to convert the final `EpsFSA` back to a
--     regular `FSA`, since our `accepts` function wouldn't know what to do with a
--     `Nothing`-transition. You can do this with the function `unEps`, which has
--     been imported from the `FSA.hs`{.tt} module. For instance, given the test
--     suite of REs below, ...
--     
re1 :: Regexp
re1 = (char 'a' <|> char 'b') <.> char 'c' 


re2 :: Regexp
re2 = rep re1

re3 :: Regexp
re3 = rep (zero <.> char 'c')

re4 :: Regexp
re4 = (char 'a' <|> char 'b') <.> rep (char 'c')
--     
--     ... you should get the following results:
--     
--     ```{.shell}
--     ghci> accepts (unEps (reToFSA re2)) "acacbcac"
--     True
--     ghci> accepts (unEps (reToFSA re2)) "acacbca"
--     False
--     ghci> accepts (unEps (reToFSA re3)) ""
--     True
--     ghci> accepts (unEps (reToFSA re3)) "c"
--     False
--     ghci> accepts (unEps (reToFSA re4)) "accc"
--     True
--     ghci> accepts (unEps (reToFSA re4)) "bcc"
--     True
--     ghci> accepts (unEps (reToFSA re4)) "abccccc"
--     False
--     ghci> accepts (unEps (reToFSA (rep re4))) "abccccc"
--     True
--     ```
