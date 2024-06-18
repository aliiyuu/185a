{-# LANGUAGE NoImplicitPrelude #-}


module HW2 where 



-- The only bits of Haskell that will be available to you in this assignment
-- are the things you see imported here at the top. In particular, the only
-- pre-defined Haskell functions and types that you'll be able to use are the
-- ones you see in `import Prelude` block

import Regexp
  ( -- the type and data constructors for Regexp
    Regexp(..)
    -- ways to build small Regexps as building blocks
  , zero, one, char, str
    -- functions to build larger Regexps out of smaller ones
  , (<|>), (<.>), rep
    -- functions to generate strings from a Regexp and/or see if
    -- a String matches a Regexp
  , mset, match
  )

import Prelude
  ( -- the basic types that we've seen for integers, booleans, characters, and strings
    Int, Bool(True, False), Char, String
    -- some basic arithmetic operations and relations:
    --   addition, subtraction, multiplication, greater/less than, equal to
  , (+), (-), (*), (<), (>), (==)
    -- some basic boolean operations:
    --   "and", "or", "not"
  , (&&), (||), not
    -- some basic list processing functions, which you might want while checking your 
    -- work in ghci:
    --   take/drop the first n elements, concatenation
  , take, drop, (++)
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
-- accompanying Regexp.hs file from BruinLearn is also in that directory. Then
-- you just type:
--   > ghci HW2.hs
-- and you should be able to go. You can check to see if one of the functions
-- is in scope by asking ghci for its type with `:type` (or `:t` for short)
--   ghci> :type concatIntList
--   concatIntList :: IntList -> IntList -> IntList
-- Whenever you make a change to the file, you'll need to reload it in ghci
-- with `:reload` (or `:r` for short)
--   ghci> :reload


-- ::: {.tex-center}
-- **Ling 185A: Assignment 2**

-- Dylan Bumford, Winter 2024

-- due: Wed, Jan 24
-- :::

-- # Recursion on `Nat`s

-- Here is the `Nat` type from last week. It says that a `Nat` is either `Z`
-- (zero), or the `S` (successor) of a `Nat`.

data Nat = Z | S Nat
  deriving Show

-- And here's the `toInt` function we defined. It turns a `Nat` into an `Int` by
-- defining a base case and a recursive step. The recursive step for `S n` assumes
-- that we can compute `toInt n`. Since `S n` is the successor of `n`, we know
-- `toInt (S n)` should be `1` greater than `toInt n`.

toInt :: Nat -> Int
toInt Z     = 0
toInt (S n) = 1 + toInt n

-- (@) Define a function `toNat` that goes in the opposite direction, converting
--     an `Int` to a `Nat`. You can check your answer by loading (or refreshing)
--     your module in `ghci`{.tt}, and then calling, say, `toNat 5`. 
--     
toNat :: Int -> Nat
toNat 0 = Z
toNat n = S (toNat (n-1))

-- (@) Here we're going to define some arithmetic functions on `Nat`s. It would
--     completely defeat the purpose of the exercise if you were to use `toInt`
--     and/or `toNat` in your definitions, so please do not. But you can use them
--     when testing your functions to see if they do what you expect.

--     #.  Define a function `add` that sums two `Nat`s. Hint: for the recursive
--         step, you will find it useful to remember the following fact about addition:
--         `(1 + m) + n == m + (1 + n)`. You can check your answer by refreshing
--         `ghci`{.tt} with `:r`{.tt}, and then calling, say,
--         `add (S (S (S Z))) (S (S Z))`, or more transparently
--         `toInt (add (toNat 3) (toNat 2))`.

add :: Nat -> Nat -> Nat
add Z     n = n
add (S m) n = add (m) (S (n))
--         
--     #.  Define a function `mul` to multiply two `Nat`s. You will likely find
--         it useful to make use of the `add` function above.
--     
mul :: Nat -> Nat -> Nat
mul Z     n = Z
mul (S m) n = add (mul m n) (n)

--     #.  Define a function `equal` that determines whether two `Nat`s are equal.
--     
equal :: Nat -> Nat -> Bool
equal Z Z = True
equal (S n) (S m) = equal n m
equal _ _ = False

-- # Recursion on lists

-- Here is the type we defined for `IntList`s: an `IntList` is either `Empty`, or
-- th   e `Cons` of an `Int` onto an `IntList`:

data IntList = Empty | Cons Int IntList
  deriving Show

-- (@) Define `concatIntList` that concatenates two `IntList`s. That is, the
--     result of `concatIntList u v` should be a single `IntList` containing first
--     all the elements of `u` and then all the elements of `v`. For instance,
--     applying `concatIntList` to `Cons 1 (Cons 2 Empty)` and `Cons 3 (Cons 4 Empty)`
--     should give `Cons 1 (Cons 2 (Cons 3 (Cons 4 Empty)))`. You may feel
--     that this is eerily similar to the definition of `add` you wrote above.

concatIntList :: IntList -> IntList -> IntList
concatIntList Empty       ys = ys
concatIntList (Cons x xs) ys = (Cons x (concatIntList xs ys))

--     Now convert your definition into one that works on Haskell's native
--     representation of lists, recalling that for Haskell's lists, `Empty` is
--     pronounced `[]`, and `Cons x xs` as `(x : xs)`

concatList :: [Int] -> [Int] -> [Int]
concatList []     ys = ys
concatList (x:xs) ys = x : concatList xs ys

-- (@) Define a function `count` to count how many of the elements in a list of
--     `Int`s satisfy some property `p`. Since a count is always a natural number,
--     have your function return a `Nat`, as in the type specified below.
--     
count :: (Int -> Bool) -> [Int] -> Nat
count p [] = Z
count p (x:xs) = if (p x) then S (count p xs) else count p xs
--     
--     For instance, you should get these results in `ghci`{.tt}.
--     
--     ```{.shell}
--     ghci> count (\x -> x > 3) [2, 5, 8, 11, 14]
--     S (S (S (S Z)))
--     ghci> count (\x -> x < 10) [2, 5, 8, 11, 14]
--     S (S (S Z))
--     ```
--     
-- (@) Define a function `append` that when given a character `c` and a string `u`
--     returns a string just like `u` but with `c` tacked on to the end.
--     
append :: Char -> String -> String
append c "" = [c]
append c (u:us) = u : append c us
--     
--     For instance, you should get these results in `ghci`{.tt}.
--     
--     ```{.shell}
--     ghci> append 'x' "this"
--     "thisx"
--     ghci> append 'y' ""
--     "y"
--     ```
--     
-- (@) Define a function `reverse` that when given a string `u` returns a string
--     just like `u` but with all the characters in the opposite order. You may want
--     to use the `append` function you just defined here.
--     
reverse :: String -> String
reverse ""     = ""
reverse (u:us) = append u (reverse us)
--     
--     For instance, you should get these results in `ghci`{.tt}.
--     
--     ```{.shell}
--     ghci> reverse "tomorrow"
--     "worromot"
--     ghci> reverse "omorrow"
--     "worromo"
--     ```

-- # Regular Expressions

-- In this section, you will make use of the `Regexp.hs`{.tt} module that has been
-- imported above. When building `Regexp`s, I recommend using the functions `str`,
-- `char`, `(<.>)`, `(<|>)`, and `rep`, rather than the data constructors `Lit`,
-- `Cat`, `Alt`, and `Star` directly, as these functions will be a little faster
-- and more readable. Feel free to check your work in `ghci`{.tt} by using the
-- `match` and/or `mset` functions from the library.

-- (@) Define a function `anyOf` that turns a list of characters into a `Regexp` that
--     matches any string consisting of exactly one character from the list. For
--     instance, `anyOf ['a','b','c']` should match `"a"`, `"b"`, and `"c"`, but
--     nothing else. In other words `mset (anyOf ['a','b','c'])` should return
--     `["a","b","c"]`.
--     
anyOf :: [Char] -> Regexp
anyOf []     = Zero
anyOf (c:cs) = char c <|> anyOf cs
--     
-- (@) Once you've defined `anyOf`, these you should be able to use the following
--     `Regexp`s to pick out various character classes:
--     
anych, alpha, lower, upper, digit :: Regexp
anych = anyOf (['!'..'~'] ++ " \n\r\t") -- matches any single character
lower = anyOf ['a'..'z'] -- matches any lowercase letter
upper = anyOf ['A'..'Z'] -- matches any uppercase letter
alpha = lower <|> upper -- matches any letter
digit = anyOf ['0'..'9'] -- matches any digit

--     For instance, `alpha` matches any string consisting of a single alphabetical
--     letter. Using these definitions, together with the other functions from
--     `Regexp.hs`{.tt}, define `Regexp`s for the following string patterns.

--     #.  Any alphanumeric string that begins with uppercase `S`{.tt}.

startsWithS :: Regexp
startsWithS = char 'S' <.> rep (alpha <|> digit)


--     #.  Any alphanumeric string with an even number of letters (0, 2, 4, ...).

evenLetters :: Regexp
evenLetters = rep digit <|> rep(rep digit <.> alpha <.> rep digit <.> alpha <.> rep digit)

--     #.  Any string that begins with an uppercase letter followed by any number
--         of lowercase letters.

capitalized :: Regexp
capitalized = upper <.> rep lower

--     #.  Any alphabetical string that begins or ends with a lowercase `z`{.tt}.

termZ :: Regexp
termZ =  (char 'z' <.> rep alpha) <|> (rep alpha <.> char 'z')

--     #.  Any string with at least one `i`{.tt} or `I`{.tt}.

oneI :: Regexp
oneI = rep anych <.> (char 'i' <|> char 'I') <.> rep anych

-- (@) Write a function `showRE` that displays a `Regexp` in a string format
--     approximating its mathematical notation. Instead of the emptyset symbol for
--     `Zero`, you can use the representation "0" and instead of the epsilon symbol
--     for `One`, just use the representation "1". For alternation, use a pipe "|",
--     for concatenation a period ".", and for repetition, an asterisk "\*". Pay
--     attention to parentheses. This remind you of the `showForm` function from
--     the slides.
--     
showRE :: Regexp -> String
showRE re = case re of
  Zero    -> "0"
  One     -> "1"
  Lit c   ->  [c]
  Alt r s -> "(" ++ showRE r ++ " | " ++ showRE s ++ ")"
  Cat r s -> "(" ++ showRE r ++ " . " ++ showRE s ++ ")"
  Star r  -> showRE r ++ "*"

--     ```{.shell}
--     ghci> showRE (Alt (Star (Lit 'a')) (Cat (Star (Alt (Lit 'b') (Lit 'c'))) One))
--     "(a* | ((b | c)* . 1))"
--     
--     ghci> showRE (Cat (Cat Zero (Star (Alt (Lit 'b') ( Lit 'c')))) (Lit 'd'))
--     "((0 . (b | c)*) . d)"
--     ```

--     (Note that when creating test examples for this problem, you should use the
--     actual `Regexp` data constructors, as I've done here. The `(<.>)`, `(<|>)`,
--     and `rep` operators exploit the algebraic properties of REs to simplify
--     them, but here you want to actually see them in their raw, unsimplified
--     form. I mean, if you're curious, you should try some examples with both
--     versions and see the difference!)
