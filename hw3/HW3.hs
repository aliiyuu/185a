{-# LANGUAGE NoImplicitPrelude #-}


module HW3 where 


-- The only bits of Haskell that will be available to you in this assignment
-- are the things you see imported here at the top. In particular, the only
-- pre-defined Haskell functions and types that you'll be able to use are the
-- ones you see in `import Prelude` block. Do not change anything in this
-- import block.

import FSA -- the functions exported by our FSA.hs file
import Prelude
  ( -- that basic types that we've seen for integers, booleans, characters, and strings
    Int, Bool(True, False), Char, String
    -- some basic arithmetic operations and relations:
    --   addition, subtraction, multiplication, greater/less than, equal to
  , (+), (-), (*), (<), (>), (==)
    -- some basic boolean operations:
    --   "and", "or", "not"
  , (&&), (||), not
    -- some list inspection functions, which you might want while checking your 
    -- work in ghci
  , take, drop, or, and, any, all, map, concat, elem, (++)
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
-- accompanying FSA.hs file from BruinLearn is also in that directory. Then
-- you just type:
--   > ghci HW3.hs
-- and you should be able to go. You can check to see if one of the functions
-- is in scope by asking ghci for its type with `:type` (or `:t` for short)
--   ghci> :type accepts
--   accepts :: FSA -> String -> Bool
-- Whenever you make a change to the file, you'll need to reload it in ghci
-- with `:reload` (or `:r` for short)
--   ghci> :reload

-- ::: {.tex-center}
-- **Ling 185A: Assignment 3**

-- Dylan Bumford, Winter 2024

-- due: Wed, Jan 31
-- :::

-- # Encoding FSAs

-- (@) Use this FSA to answer the questions that follow:

--     fsa.tex

--     #.  Translate this FSA into its Haskell representation:

myFSA :: FSA 
myFSA = FSAWith states syms i f delta 
  where states = [51, 22, 63, 34] 
        syms   = ['a', 'b']
        i      = [51] 
        f      = [34] 
        delta  = [(51, 'a', 51), (51, 'b', 22), (22, 'a', 22), (22, 'b', 63), (63, 'a', 63), (63, 'b', 51), (63, 'b', 34), (34, 'a', 34)] 

--     #.  Let's investigate the sorts of `String`s `myFSA` generates.
--         `FSA.hs`{.tt} defines an `accepts` function which tests whether an FSA
--         accepts a string. That is, `accepts` takes an FSA and a string and
--         returns `True` if the string is accepted by the FSA, `False` otherwise.
--         
--         `testSuite` defines a list of `String`s that the above FSA might or
--         might not accept. Use a list comprehension to pair each `String` in
--         `testSuite` with the `Bool` corresponding to whether or not it is
--         accepted by `myFSA`. Put your answer in `testResults`.

testSuite :: [String]
testSuite = [str1, str2, str3, str4, str5]
  where str1 = "bab"
        str2 = "aa"
        str3 = "babba"
        str4 = "bbbabb"
        str5 = "bbbabbb"

testResults :: [(String, Bool)]
testResults = [(str, accepts myFSA str) | str <- testSuite]

--         Inspecting `testResults` in `ghci`{.tt} may help you ascertain what
--         pattern the FSA encodes. Another way to see how it works is to start
--         tracing paths through it, writing down the strings you can generate by
--         doing so. Once you feel you understand how the FSA behaves, characterize
--         in your own words the strings it accepts inside this block comment:

{-
The FSA accepts any string that has a number of b's that is divisible by 3 (except 0).
-}

--         If you are desperate for things to think about, try to define a `Regexp`
--         with the same behavior as `myFSA`. Check your answer by calling `match
--         myRE "bbbabbb"` and `match myRE "bbbabb"` (you'll need to import the
--         `Regexp` module at the top of this file). Note: this is tricky and
--         completely optional.

-- myRE :: Regexp
-- myRE = rep (rep a <.> b <.> rep a <.> b <.> rep a <.> b <.> rep a)

-- # Designing FSAs

-- (@) Define an FSA that generates all and only those strings over the alphabet
--     `['a','b']` with an **even number of `'a'`s**. I suggest that you first
--     sketch it out on paper and then translate your diagram to Haskell.

evenas :: FSA
evenas = FSAWith states syms i f delta
  where states = [1, 2]
        syms   = ['a', 'b']
        i      = [1]
        f      = [1]
        delta  = [(1, 'b', 1), (1, 'a', 2), (2, 'b', 2), (2, 'a', 1)]

--     Now do the same for strings with an **odd number of `'a'`s**.

oddas :: FSA
oddas = FSAWith states syms i f delta
  where states = [1, 2]
        syms   = ['a', 'b']
        i      = [1]
        f      = [2]
        delta  = [(1, 'b', 1), (1, 'a', 2), (2, 'b', 2), (2, 'a', 1)]
--     
--     Use `accepts` (from the `FSA`{.tt} module) and `all` (from the
--     `Prelude`{.tt} imports) to construct tests for your FSAs. A suite of test
--     items is defined for you in both cases. Use the types to guide you! `all`
--     has type `(a -> Bool) -> [a] -> Bool`: it takes a function from `a` to
--     `Bool` and a list of `a`s, and returns `True` if every `a` in the list
--     makes the function `True` (and returns `False` otherwise). Here, the `a`
--     type will be `String`.

testEven :: Bool
testEven = all (accepts evenas) suite
  where suite = ["aa","aba","abbabbbb","","aaaaaabaa"]

testOdd :: Bool
testOdd = all (accepts oddas) suite
  where suite = ["aaa","ba","abbabbba","a","aaaaaaba"]

-- (@) Vowel harmony ([`link`{.tt}](https://en.wikipedia.org/wiki/Vowel_harmony))
--     is a phonological pattern in which (simplifying greatly) all the vowels
--     within some domain are identical.

--     Define an FSA that accepts a string if and only if all the vowels within a
--     morpheme are identical. We will work with a very simple alphabet with one
--     consonant `'k'`, two vowels `'i'` and `'u'`, and a space character for
--     morpheme boundaries `' '`. Thus, for example, `"ikik kukku"`, `"kkuuk"`, and
--     `" k i u"` should all be accepted, but `"kiku"` should not be.

--     Check your answer using `accepts`.

fsaHarmony :: FSA
fsaHarmony = FSAWith states syms i f delta
  where
    states = [1, 2, 3, 4]
    syms   = ['k', 'i', 'u', ' ']
    i      = [1]
    f      = [1, 2, 3]
    delta  = [(1, 'k', 1), (1, 'i', 2), (1, ' ', 1), (1, 'u', 3), (2, 'k', 2), (2, 'i', 2), (2, 'u', 4), (2, ' ', 1), (3, 'k', 3), (3, 'u', 3), (3, 'i', 4), (3, ' ', 1)]

--     

--     ```{.shell}
--     ghci> accepts fsaHarmony "ikik kukku"
--     True
--     ghci> accepts fsaHarmony "kkuuk"
--     True
--     ghci> accepts fsaHarmony "  k i u"
--     True
--     ghci> accepts fsaHarmony "kiku"
--     False
--     ```

-- (@) Define an FSA on the same alphabet accepting exactly the strings in which
--     any `'i'`s appear immediately after a `'k'`. This FSA should accept `"ki"`
--     and `"kiki"`, but not `"kikii"`, or `"ki i"`.

--     Check your answer using `accepts`.

fsaKI :: FSA
fsaKI = FSAWith states syms i f delta
  where
    states = [1, 2, 3, 4, 5]
    syms   = ['k', 'i', 'u', ' ']
    i      = [1]
    f      = [1, 3, 4, 5]
    delta  = [(1, 'i', 2), (1, 'k', 3), (1, 'u', 5), (1, ' ', 1), (3, 'k', 3), (3, 'u', 5), (3, 'i', 4), (3, ' ', 1), (4, 'i', 2), (4, 'k', 3), (4, 'u', 5), (4, ' ', 1), (5, 'i', 2), (5, 'k', 3), (5, 'u', 5), (5, ' ', 1)]

--     

--     ```{.shell}
--     ghci> accepts fsaKI "ki"
--     True
--     ghci> accepts fsaKI "kiki"
--     True
--     ghci> accepts fsaKI "kikii"
--     False
--     ghci> accepts fsaKI "ki i"
--     False
--     ```

-- (@) Assume our alphabet is contains just `c` and `v`. Write a function
--     `requireCs :: Int -> FSA` that constructs different FSAs for different
--     `Int`s. When given the number `n`, it should return an FSA that accepts all
--     and only those strings that contain exactly `n`-many `'c'`s. Hint: It might
--     be helpful to think about this as two sub-questions: what are the
--     transitions emitting `'c'` that we're allowed to take, and what are the
--     transitions emitting `'v'` that we're allowed to take?

requireCs :: Int -> FSA
requireCs n = FSAWith states syms i f (deltaC ++ deltaV)
  where
    states = [x | x <- [1..n+2]]
    syms   = ['c', 'v']
    i      = [1]
    f      = [n+1]
    deltaC = [(x, 'c', x+1) | x <- [1..n+1]] ++ [(n+2, 'c', n+2)]
    deltaV = [(x, 'v', x) | x <- [1..n+2]]
--     
--     For instance,
--     
--     ```{.shell}
--     ghci> accepts (requireCs 2) "cc"
--     True
--     ghci> accepts (requireCs 2) "cv"
--     False
--     ghci> accepts (requireCs 2) "cvc"
--     True
--     ghci> accepts (requireCs 2) "cvcc"
--     False
--     ghci> accepts (requireCs 2) "cvccv"
--     False
--     ghci> accepts (requireCs 3) "cvccv"
--     True
--     ghci> accepts (requireCs 3) "cvcv"
--     False
--     ```
