module Regexp where

------------------------------------------------------------------------
-- the type Regexp defines the different forms a regular
-- expression can take
------------------------------------------------------------------------

data Regexp
  = Zero               -- nothing (0)
  | One                -- empty string (epsilon)
  | Lit Char           -- single character (c)
  | Cat Regexp Regexp  -- concatenation (.)
  | Alt Regexp Regexp  -- union (|)
  | Star Regexp        -- repetition (*)
  deriving (Eq, Show)


------------------------------------------------------------------------
-- here are the functions you can use to build your REs
-- (r <|> s) represents a choice between r and s
-- (r <.> s) represents an r match followed by an s match
-- (rep r) represents a repetition of r matches (zero or more of them)
------------------------------------------------------------------------

-- in defining these operators, we can simplify complex expressions
-- a bit by leveraging those little algebraic facts presented in class
-- about how <.>, <|>, Zero, and One obey certain laws of arithmetic

-- for instance, there's no point in building a regexp that chooses between
-- some pattern e and Zero, because nothing can match Zero, so any match
-- of (e <|> Zero) would just be an e match anyway
(<|>) :: Regexp -> Regexp -> Regexp
Zero <|> e    = e
e    <|> Zero = e
-- if neither argument is Zero, then we have to construct a choice
e1   <|> e2   = Alt e1 e2

-- there's no point in building an RE that tries to match a Zero before
-- or after some other pattern e, because nothing matches Zero, so
-- (e <.> Zero) is equivalent Zero
-- similarly, since One only matches "", and "" concatenated with anything
-- is just that thing again, there's no point in building an RE of the form
-- (e <.> One), since that is equivalent to e
(<.>) :: Regexp -> Regexp -> Regexp
Zero <.> e    = Zero
e    <.> Zero = Zero
One  <.> e    = e
e    <.> One  = e
-- if neither argument is Zero or One, then we have to construct a concatenation
e1   <.> e2    = Cat e1 e2

-- and here are some facts about repetition that you can work out if you
-- think about them
rep :: Regexp -> Regexp
rep Zero     = One -- none of the repetitions of Zero ever add any hits
rep One      = One -- arbitrary repetitions of "" are still ""
rep (Star e) = Star e -- (Star e) already contains all the repetitions you could want!
-- if the argument is none of the above, then we have to construct a repetition
rep e        = Star e

-- pop quiz: if <|> is addition, and <.> is multiplication, then based
-- on the little facts in the definition of star, what do you think star is?


------------------------------------------------------------------------
-- here are some basic Regexps to get you started
------------------------------------------------------------------------

-- the simplest regular expressions
zero :: Regexp
zero = Zero

one :: Regexp
one = One

char :: Char -> Regexp
char c = Lit c

str :: String -> Regexp
str ""     = One
str (c:cs) = Lit c <.> str cs

------------------------------------------------------------------------
-- given a Regexp r, the function mset generates all of the Strings that
-- could ever match r
------------------------------------------------------------------------

mset :: Regexp -> [String]
mset r = case r of
  Zero    -> [] -- no matches
  One     -> [""] -- only matches the empty list
  Lit c   -> [[c]] -- only matches the string whose only character is c
  Alt r s -> mset r ++ mset s -- all the matches in r plus all the matches in s
  Cat r s -> [u++v | u <- mset r, v <- mset s] -- an r matched followed by an s one
  -- for (Star r), we build:
  --      all the matches for 1 instance of r
  -- plus all the matches for 2 instances of r
  -- plus all the matches for 3 instances of r
  -- etc
  -- plus all the matches for 0 instances of r (aka One)
  Star r   -> concat [ mset (repeat r n) | n <- [0..] ]
  where
    -- (repeat r n) makes (r <.> ... <.> r <.> One)
    --                     ^^^^^^^^^^^^^^^
    --                         n times
    repeat r 0 = One -- base case
    repeat r n = r <.> repeat r (n-1) -- recursing on n

------------------------------------------------------------------------
-- given a Regexp r and a String u, the function match determines whether
-- u matches r by looking directly at the shape of r and the characters
-- in u (rather than blindly enumerating every possible r-matching string
-- and hoping to hit u)
------------------------------------------------------------------------

match :: Regexp -> String -> Bool
match re u = case re of
  Zero    -> False
  One     -> u == ""
  Lit c   -> u == [c]
  Alt r s -> match r u || match s u
  Cat r s ->
    or [ match r v && match s w | (v,w) <- splits u ]
  Star r  ->
    u == "" ||
    or [ match r v && match (Star r) w | (v,w) <- drop 1 (splits u) ]
  where
    -- all the ways of splitting a String u into a first part
    -- and a second part
    splits :: String -> [(String, String)]
    splits u = [splitAt i u | i <- [0..length u]]
    -- splitAt :: Int -> String -> (String, String)
    -- (splitAt n u) breaks u apart at the nth position
    -- e.g., splitAt 2 "somestring" == ("som","estring")
    -- it, too, comes with Haskell, but is defined (recursively!)
    -- in the class slides

------------------------------------------------------------------------
-- you can and should ignore what's below
-- it just uses a trick called "compiling with continuations" to speed
-- up the definition of match above if it's taking forever
-- in case you're curious, it's adapted from Pedro Vasconcelos,
-- after Danvy & Nielsen's 2001 "Defunctionalization at work" and
-- Harper's (1999) "Proof-directed debugging"
------------------------------------------------------------------------

type Cont = String -> Bool

-- an auxiliary function to do all the work
accept :: Regexp -> String -> Cont -> Bool
accept Zero    _       _ = False
accept One     cs      k = k cs
accept (Lit c) (c':cs) k = c==c' && k cs
accept (Lit c) _       k = False
accept (Cat  e1 e2) cs k = accept e1 cs (\cs' -> accept e2 cs' k)
accept (Alt e1 e2) cs  k = accept e1 cs k || accept e2 cs k
accept (Star e) cs     k = acceptStar e cs k
  where
    acceptStar e cs k
      = k cs || accept e cs (\cs' -> cs' /= cs && acceptStar e cs' k)
-- acceptStar piles up as much `accept e cs (\cs' -> ... accept e cs' (...))`
-- as needed to consume all of cs. The (cs' /= cs) condition ensures that some
-- of cs is consumed on each call; useful when e is (Star One) and cs
-- is a non-matching string. The smart constructors actually take care of this
-- already, by normalizing (Star One) to One.

-- the interface function that you can actually use
match' :: Regexp -> String -> Bool
match' re s = accept re s null
