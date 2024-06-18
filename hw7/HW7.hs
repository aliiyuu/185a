{-# LANGUAGE NoImplicitPrelude #-}


module HW7 where 


-- The only bits of the standard Haskell library that will be available to you
-- are the things you see imported here:

import Prelude
  ( -- that basic types that we've seen for integers, booleans, characters, and strings
    Int, Bool(True, False), Char, String
    -- the type constructor Maybe (and its data constructors, Just and Nothing)
  , Maybe(..)
    -- some basic arithmetic operations and relations:
  , (+), (-), (*), (<), (>), (==), (>=), (<=), maximum, minimum, max, min
    -- some basic boolean operations:
  , (&&), (||), not
    -- some list inspection and processing functions
  , take, drop, or, and, any, all, map, filter, concat, elem, (++), (.), words
    -- and some classes for showing and comparing things (don't worry about these)
  , Show, Eq, Ord, undefined
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
--   > ghci HW7.hs
-- and you should be able to go. You can check to see if one of the functions
-- is in scope by asking ghci for its type with `:type` (or `:t` for short)
--   ghci> :type ex1b
--   ex1b :: ParseTable
-- Whenever you make a change to the file, you'll need to reload it in ghci
-- with `:reload` (or `:r` for short)
--   ghci> :reload

-- ::: {.tex-center}
-- **Ling 185A: Assignment 7**

-- Dylan Bumford, Winter 2024 

-- due: Wed, Mar 6
-- :::

-- # Left-corner parsing review

-- Here's a simple CFG you should use for most of the questions below. Note that we
-- are relaxing the Chomsky Normal Form requirement that nonterminals be rewritten
-- as _exactly two_ other nonterminals. Instead, we allow nonterminals on the
-- left-hand side to produce _a list_ of nonterminals on the right.

-- center
-- tabular[t]{r@{$\ \rightarrow\ $}l@{\hskip 2em}r@{$\ \rightarrow\ $}l}
-- S   & NP VP                         & N     & baby, boy, actor, award, boss \\
-- S   & W S S                         & NP    & Mary, John \\
-- NP  & NP PS N                       & V     & met, saw, won, cried, watched \\
-- NP  & (D) N (PP) (SRC) (ORC)        & D     & the \\
-- VP  & V (NP) (PP)                   & P     & on, in, with \\
-- PP  & P NP                          & C     & that \\
-- SRC & C VP                          & PS    & 's \\
-- ORC & NP V                          & W     & while \\
-- tabular
-- center


data Cat = S | NP | VP | W | PS | N | D | PP | SRC | ORC | V | C | P
  deriving (Eq, Ord, Show)

-- notice the branching rules rewrite to a whole list of Cats,
-- not necessarily a pair of them
data Rule = Cat :- String | Cat :> [Cat]
  deriving (Eq, Ord, Show)


-- Recall that left-corner parsing can be thought of as a combination of bottom-up
-- and top-down parsing. The stack of a left-corner parser mixes (a) symbols with a
-- bar over them, which represent still-to-come constituents (tree nodes with no
-- children yet), and are analogous to the symbols on the stack in top-down
-- parsing, and (b) symbols without a bar over them, which represent
-- already-recognized constituents (tree nodes with no parent yet), and are
-- analogous to the symbols on the stack in bottom-up parsing. The
-- left-corner of a context-free rule is the first symbol on the right hand
-- side.

-- - - -

-- To illustrate, here again is the example we saw in class. The shift and
-- match rules should be relatively easy to understand. They are similar
-- to the rules of the same names in bottom-up and top-down parsing. Notice that
-- the shift rule, since it does bottom-up work, only manipulates
-- "un-barred" symbols (e.g. D at step 1, V at step 5), and the match
-- rule, since it does top-down work, only manipulates "barred" symbols (e.g.
-- N at step 3).

-- center
-- tabular{p{2em}lp{8em}l}
-- \toprule
--     & Type of transition    & Rule used                     & Configuration \\
-- \midrule
-- 0   & ---                   & ---                           & (S, the baby saw the boy) \\
-- 1   & shift        & D $\rightarrow$ the           & (D S, baby saw the boy) \\
-- 2   & lc-predict   & NP $\rightarrow$ D N          & (N NP S, baby saw the boy) \\
-- 3   & match        & N $\rightarrow$ baby          & (NP S, saw the boy) \\
-- 4   & lc-connect   & S $\rightarrow$ NP VP         & (VP, saw the boy) \\
-- 5   & shift        & V $\rightarrow$ saw           & (V VP, the boy) \\
-- 6   & lc-connect   & VP $\rightarrow$ V NP         & (NP, the boy) \\
-- 7   & shift        & D $\rightarrow$ the           & (D NP, boy) \\
-- 8   & lc-connect   & NP $\rightarrow$ D N          & (N, boy) \\
-- 9   & match        & N $\rightarrow$ boy           & ($\epsilon$, $\epsilon$) \\
-- \bottomrule
-- tabular
-- center

-- The lc-predict rule is a bit more complicated. It manipulates both
-- plain and barred symbols. The application of lc-predict at step 2, for
-- example, transitions from 'D S' to 'N NP S'.
-- This step is based on the fact that D is the left-corner of the rule 'NP
-- $\rightarrow$ D N': having recognized (in a bottom-up manner) a D, we predict
-- (in a top-down manner) an N; and if we manage to fulfill that prediction of an
-- N, we will have recognized (in a bottom-up manner) an NP.

-- - - -

-- The lc-connect rule, like the lc-predict, predicts "the rest"
-- of the right-hand side of a rule on the basis of having already recognized the
-- rule's left-corner. For example, when we've reached 'NP S', the
-- application of lc-connect at step 4 is based on the fact that NP is the
-- left-corner of the rule 'S $\rightarrow$ NP VP'. The difference here, compared
-- to the situation above with lc-predict, is that we already have a
-- _predicted_ S (i.e. the symbol S) waiting for us there on the stack.
-- Since we've already found an NP bottom-up, the prediction of an S will be
-- fulfilled if we find a VP in the coming words, so it can be swapped for a
-- predicted VP (i.e. the symbol VP).

-- - - -

-- One catch to look out for is that when lc-predict or
-- lc-connect applies to a unary grammar rule, there are no new barred
-- symbols created, because the only thing on the right-hand side of the rule
-- _is_ the left-corner. For example, the last step of parsing 'the baby
-- won', using the unary rule 'VP $\rightarrow$ V', is one such situation.


-- center
-- tabular{p{2em}lp{8em}l}
-- \toprule
--     & Type of step          & Rule used                     & Configuration \\
-- \midrule
-- 0   & ---                   & ---                           & (S, the baby won) \\
-- 1   & shift        & D $\rightarrow$ the           & (D S, baby won) \\
-- 2   & lc-predict   & NP $\rightarrow$ D N          & (N NP S, baby won) \\
-- 3   & match        & N $\rightarrow$ baby          & (NP S, won) \\
-- 4   & lc-connect   & S $\rightarrow$ NP VP         & (VP, won) \\
-- 5   & shift        & V $\rightarrow$ won           & (V VP, $\epsilon$) \\
-- 6   & lc-connect   & VP $\rightarrow$ V            & ($\epsilon$, $\epsilon$) \\
-- \bottomrule
-- tabular
-- center



-- # Incremental Parsing

-- Here are some simple type synonyms encoding the components of the tables above.

-- in a configuration, an item in memory is either a nonterminal we've already
-- got (un-barred) or a nonterminal we are predicting (barred)
data Chunk = Got Cat | Pre Cat

-- just for convenience, if you like:
got, pre :: Cat -> Chunk
got c = Got c
pre c = Pre c

-- the configuration's memory is just a list of chunks (nonterminals)
type Stack = [Chunk]
-- the buffer is a list of words
type Buffer = [String]
-- the configuration is a pair of a current stack and a current buffer
type Config = (Stack, Buffer)

-- between the three parsing strategies, we have six kinds of transitions
data Transition
  = Shift | Reduce
  | Match | Predict
  | LCPredict | LCConnect
  
-- one row in a derivation table identifies a transition, a grammar rule, and
-- a new config that results from applying the transition to the previous config
type ParseStep = (Transition, Rule, Config)
-- a table is just a list of rows
type ParseTable = [ParseStep]

-- You will need to provide your answers in this Haskell file, using the types
-- above where appropriate. BUT you are not actually writing any programs here. And
-- you are highly encouraged to work out the derivations with pencil and paper.
-- This file is only for submitting your final responses (and using the type system
-- to prevent any typos.)

-- (@) For this exercise, you'll investigate the memory requirements imposed by a
--     left-corner parsing schema by constructing left-corner parse tables for six
--     of the sentences from the class handout. We have (1b) "Mary's baby won" and
--     (1c) "Mary's baby's boss won", illustrating **Left Embedding**. We have (2b)
--     "John met the boy that saw the actor" and (2c) "John met the boy that saw
--     the actor that won the award", illustrating **Right Embedding**. And we have
--     (3b) "the actor the boy met won" and (3c) "the actor the boy the baby saw
--     met won", illustrating **Center Embedding**. The crucial question is whether
--     the memory requirements of the parsing algorithm --- as measured by the
--     maximum number of symbols on the stack at any given step --- increases
--     between each (b) sentence and the corresponding (c) sentence.
--     
--     - - -
--     
--     For each (b) sentence, please provide the entire derivation table,
--     identifying the transition, the production rule, and the buffer at each
--     step. For each (c) sentence, you don't need to provide the whole table
--     (though you can if you want), **but you need to provide at least the rows
--     containing the configurations that impose the largest memory load.** So if
--     you want, for the (c) sentences, you only need to include these maximally
--     costly row(s) in the `ParseTable` you define.

--     a. Complete the parse table for (1b): "Mary 's baby won'"
--     
ex1b :: ParseTable
ex1b =
  [ -- starting configuration:     ([pre S]                        , ["Mary","'s","baby","won"])
    (Shift     , NP :- "Mary"    , ([got NP, pre S]                , ["'s","baby","won"]))
  , (LCPredict , NP :> [NP, PS, N] , ([pre PS, pre N, got NP, pre S] , ["'s","baby","won"]))
  , (Match , PS :- "'s", ([pre N, got NP, pre S] , ["baby","won"]))
  , (Match , N :- "baby", ([got NP, pre S] , ["won"]))
  , (LCConnect , S :> [NP, VP], ([pre VP] , ["won"]))
  , (Shift , V :- "won", ([got V, pre VP] , []))
  , (LCConnect , VP :> [V], ([] , []))
  ]

--     a. Complete the parse table for (1c): "Mary 's baby 's boss won":

ex1c :: ParseTable
ex1c =
  [ -- starting configuration:   ([pre S]         , ["Mary","'s","baby","'s","boss","won"])
    (Shift     , NP :- "Mary"  , ([got NP, pre S] , ["'s","baby","'s","boss","won"]))
  , (LCPredict     , NP :> [NP, PS, N], ([pre PS, pre N, got NP, pre S], ["'s","baby","'s","boss","won"])) -- this line
  , (Match     , PS :- "'s", ([pre N, got NP, pre S], ["baby","'s","boss","won"]))
  , (Match     , N :- "baby", ([got NP, pre S], ["'s","boss","won"]))
  , (LCPredict     , NP :> [NP, PS, N], ([pre PS, pre N, got NP, pre S], ["'s","boss","won"])) -- this line
  , (Match     , PS :- "'s", ([pre N, got NP, pre S], ["boss","won"]))
  , (Match     , N :- "boss", ([got NP, pre S], ["won"]))
  , (LCConnect     , S :> [NP, VP], ([pre VP], ["won"]))
  , (Shift , V :- "won", ([got V, pre VP] , []))
  , (LCConnect , VP :> [V], ([] , []))
  ]

--     a. Complete the parse table for (2b): "John met the boy that saw the actor"
--     
ex2b :: ParseTable
ex2b =
  [ -- starting configuration: , ([pre S]         , ["John","met","the","boy","that","saw","the","actor"])
    (Shift     , NP :- "John"  , ([got NP, pre S] , ["met","the","boy","that","saw","the","actor"]))
  , (LCConnect     , S :> [NP, VP], ([pre VP], ["met","the","boy","that","saw","the","actor"]))
  , (Shift     , V :- "met", ([got V, pre VP], ["the","boy","that","saw","the","actor"]))
  , (LCConnect , VP :> [V, NP], ([pre NP] , ["the","boy","that","saw","the","actor"]))
  , (Shift , D :- "the", ([got D, pre NP] , ["boy","that","saw","the","actor"]))
  , (LCConnect , NP :> [D, N, SRC], ([pre N, pre SRC] , ["boy","that","saw","the","actor"]))
  , (Match , N :- "boy", ([pre SRC] , ["that","saw","the","actor"]))
  , (Shift , C :- "that", ([got C, pre SRC] , ["saw","the","actor"]))
  , (LCConnect , SRC :> [C, VP], ([pre VP] , ["saw","the","actor"]))
  , (Shift , V :- "saw", ([got V, pre VP] , ["the, actor"]))
  , (LCConnect , VP :> [V, NP], ([pre NP] , ["the, actor"]))
  , (Shift , D :- "the", ([got D, pre NP] , ["actor"]))
  , (LCConnect , NP :> [D, N], ([pre N] , ["actor"]))
  , (Match , N :- "actor", ([] , []))
  ]

--     a. Complete the parse table for (2c): "John met the boy that saw the actor
--        that won the award"

ex2c :: ParseTable
ex2c =
  [ -- starting configuration: , ([pre S]         , ["John","met","the","boy","that","saw","the","actor","that","won","the","award"])
    (Shift     , NP :- "John"  , ([got NP, pre S] , ["met","the","boy","that","saw","the","actor","that","won","the","award"])) -- this line
  , (LCConnect     , S :> [NP, VP], ([pre VP], ["met","the","boy","that","saw","the","actor", "that","won","the","award"]))
  , (Shift     , V :- "met", ([got V, pre VP], ["the","boy","that","saw","the","actor","that","won","the","award"])) -- this line
  , (LCConnect , VP :> [V, NP], ([pre NP] , ["the","boy","that","saw","the","actor","that","won","the","award"]))
  , (Shift , D :- "the", ([got D, pre NP] , ["boy","that","saw","the","actor","that","won","the","award"])) -- this line
  , (LCConnect , NP :> [D, N, SRC], ([pre N, pre SRC] , ["boy","that","saw","the","actor","that","won","the","award"])) -- this line
  , (Match , N :- "boy", ([pre SRC] , ["that","saw","the","actor","that","won","the","award"]))
  , (Shift , C :- "that", ([got C, pre SRC] , ["saw","the","actor","that","won","the","award"])) -- this line
  , (LCConnect , SRC :> [C, VP], ([pre VP] , ["saw","the","actor","that","won","the","award"]))
  , (Shift , V :- "saw", ([got V, pre VP] , ["the, actor","that","won","the","award"])) -- this line
  , (LCConnect , VP :> [V, NP], ([pre NP] , ["the, actor","that","won","the","award"]))
  , (Shift , D :- "the", ([got D, pre NP] , ["actor","that","won","the","award"])) -- this line
  , (LCConnect , NP :> [D, N, SRC], ([pre N, pre SRC] , ["actor","that","won","the","award"])) -- this line
  , (Match , N :- "actor", ([pre SRC] , ["that","won","the","award"]))
  , (Shift , C :- "that", ([got C, pre SRC] , ["won","the","award"])) -- this line
  , (LCConnect , SRC :> [C, VP], ([pre VP] , ["won","the","award"]))
  , (Shift , V :- "won", ([got V, pre VP] , ["the","award"])) -- this line
  , (LCConnect , VP :> [V, NP], ([pre NP] , ["the, award"]))
  , (Shift , D :- "the", ([got D, pre NP] , ["award"])) -- this line
  , (LCConnect , NP :> [D, N], ([pre N] , ["award"]))
  , (Match , N :- "award", ([] , []))
  ]
--         
--     a. Complete the parse table for (3b): "the actor the boy met won"
--     
ex3b :: ParseTable
ex3b =
  [ -- starting configuration: , ([pre S]        , ["the","actor","the","boy","met","won"])
    (Shift     , D :- "the"    , ([got D, pre S] , ["actor","the","boy","met","won"]))
  , (LCPredict     , NP :> [D, N, ORC], ([pre N, pre ORC, got NP, pre S], ["actor","the","boy","met","won"]))
  , (Match , N :- "actor", ([pre ORC, got NP, pre S] , ["the","boy","met","won"]))
  , (Shift     , D :- "the"    , ([got D, pre ORC, got NP, pre S] , ["boy","met","won"]))
  , (LCPredict     , NP :> [D, N], ([pre N, got NP, pre ORC, got NP, pre S], ["boy","met","won"]))
  , (Match , N :- "boy", ([got NP, pre ORC, got NP, pre S] , ["met","won"]))
  , (LCConnect , ORC :> [NP, V], ([pre V, got NP, pre S] , ["met won"]))
  , (Match , V :- "met", ([got NP, pre S] , ["won"]))
  , (LCConnect , S :> [NP, VP], ([pre VP] , ["won"]))
  , (Shift     , V :- "won"    , ([got V, pre VP] , []))
  , (LCConnect , VP :> [V], ([] , []))
  ]

--     a. Complete the parse table for (3c): "the actor the boy the baby saw met won"

ex3c :: ParseTable
ex3c =
  [ -- starting configuration: , ([pre S]        , ["the","actor","the","boy","the","baby","saw","met","won"])
  -- starting configuration: , ([pre S]        , ["the","actor",["the","boy","the","baby","saw",]"met","won"])
    (Shift     , D :- "the"    , ([got D, pre S] , ["actor","the","boy","the","baby","saw","met","won"]))
  , (LCPredict     , NP :> [D, N, ORC], ([pre N, pre ORC, got NP, pre S], ["actor","the","boy","the","baby","saw","met","won"]))
  , (Match , N :- "actor", ([pre ORC, got NP, pre S] , ["the","boy","the","baby","saw","met","won"]))
  , (Shift     , D :- "the"    , ([got D, pre ORC, got NP, pre S] , ["boy","the","baby","saw","met","won"]))
  , (LCPredict     , NP :> [D, N, ORC], ([pre N, pre ORC, got NP, pre ORC, got NP, pre S], ["boy","the","baby","saw","met","won"]))
  , (Match , N :- "boy", ([pre ORC, got NP, pre ORC, got NP, pre S] , ["the","baby","saw","met","won"]))
  , (Shift     , D :- "the"    , ([got D, pre ORC, got NP, pre ORC, got NP, pre S] , ["baby","saw","met","won"]))
  , (LCPredict     , NP :> [D, N], ([pre N, got NP, pre ORC, got NP, pre ORC, got NP, pre S], ["baby","saw","met","won"])) -- this line
  , (Match , N :- "baby", ([got NP, pre ORC, got NP, pre ORC, got NP, pre S] , ["saw","met","won"]))
  , (LCConnect , ORC :> [NP, V], ([pre V, got NP, pre ORC, got NP, pre S] , ["saw","met","won"]))
  , (Match , V :- "saw", ([got NP, pre ORC, got NP, pre S] , ["met","won"]))
  , (LCConnect , ORC :> [NP, V], ([pre V, got NP, pre S] , ["met","won"]))
  , (Match , V :- "met", ([got NP, pre S] , ["won"]))
  , (LCConnect , S :> [NP, VP], ([pre VP] , ["won"]))
  , (Shift , V :- "won", ([got V, pre VP] , []))
  , (LCConnect , VP :> [V], ([] , []))
  ] 
--         
--     a.  Based on your tables, as the depth of **Left Embedding** increases,
--         does the memory load required by a left-corner parser increase,
--         decrease, or stay constant?
--         
data Monotonicity = Increase | Decrease | Constant

leftEmbeddingMemory :: Monotonicity
leftEmbeddingMemory = Constant
--         
--         As the depth of **Right Embedding** increases, does the memory load
--         required by a left-corner parser increase, decrease, or stay constant?
--     
rightEmbeddingMemory :: Monotonicity
rightEmbeddingMemory = Constant

--         As the depth of **Center Embedding** increases, does the memory load
--         required by a left-corner parser increase, decrease, or stay constant?
--     
centerEmbeddingMemory :: Monotonicity
centerEmbeddingMemory = Increase

-- (@) Suppose you run into Martian who, oddly, appears to have the context-free
--     grammar defined in Section 1. Then you discover certain new kinds of
--     sentences that this Martian judges to be acceptable sentences of their
--     language, including:
--     
--     i.  John said loudly Mary won
--     i.  Mary said quietly John 's boss won
--     i.  the boss said slowly the actor met Mary

--     So now the question is, what new rules should we add to the grammar above in
--     order to account for these new kinds of sentences? We will consider two
--     hypotheses.
--         
--     Hypothesis 1:
--     :   tabular[t]{r@{$\ \rightarrow\ $}l}
--         VP      & SAID ADV S \\
--         SAID    & said \\
--         ADV     & loudly, quietly, slowly
--         tabular
--         
--     Hypothesis 2:
--     :   tabular[t]{r@{$\ \rightarrow\ $}l}
--         VP      & X S \\
--         X       & SAID ADV \\
--         SAID    & said \\
--         ADV     & loudly, quietly, slowly
--         tabular

--     Note that no matter which of these two hypotheses we adopt, the new grammar
--     will generate exactly the same set of sentences. So there is _no way to
--     distinguish between these two hypotheses on the basis of which sentences the
--     two grammars generate_.
--     
--     - - -

--     Suppose we know, however, that this Martian uses **bottom-up** parsing. And
--     it's generally accepted that a memory limitation is responsible for the fact
--     that, although this Martians finds iv.\@ to be a perfectly unremarkable
--     sentence, v.\@ makes their head spin.
--     
--     - - -
--     
--     So although v., like iv., is generated by the rules in our current grammar
--     and is therefore assumed to in fact be _grammatical_ for these Martians,
--     there is something else g oing wrong when they try to process v.
--     
--     iv. 2714  John met the boy
--     iv. 1F631 John met the boy that saw the actor

--     In order to decide between **Hypothesis 1** and **Hypothesis 2**, you ask
--     the Martian for their judgments of the following sentences. The first three
--     are processed without issue, but ix.\@ takes the Martian forever to make any
--     sense of.
--     
--     vi. 2714  John won
--     vi. 2714  Mary said quietly John won
--     vi. 2714  John said slowly Mary said quietly John won
--     vi. 1F631 John said slowly John said loudly Mary said quietly John won
--     
--     How can we use this information to choose between **Hypothesis 1** and
--     **Hypothesis 2**? Explain your reasoning. Notice that in this question,
--     unlike above, the issue is not whether or not larger and larger structures
--     with a certain kind of embedding pattern lead to processing difficulty _at
--     some point_ --- they clearly do --- but rather _at which point_ we see the
--     difficulty arising.

{-------------------------------
Since the Martians use bottom-up parsing, it makes sense for them to have more trouble processing
right-embedding structures. If there are too many layers of right embeddings and it is not possible to
quickly reduce the items on the stack to one constituent, the stack can become large and cause memory
processing issues such as in ix. Notice that Hypothesis 1 only has the rule  VP -> SAID ADV S
while Hypothesis 2 has both rules X -> SAID ADV and VP -> X S. In this case, every time the
Martian saw any SAID ADV (like "said slowly"), this could be reduced in Hypothesis 2 to a constituent and prevent
the memory issues in ix.

If we use Hypothesis 1, the whole sentence will need to be shifted before we can start reducing.
In Hypothesis 2, we can start reducing at every SAID ADV. In  viii. we would have 8 constituents
in the stack after going through the full sentence if we use Hypothesis 1, but in Hypothesis 2 we would
have 6 becausee the SAID ADV's can be reduced to X's. In ix. Hypothesis 1 puts all 11 words on
the stack before reducing while in Hypothesis 2 the maximum would be 8 due to reducing, meaning
Hypothesis 1 is more likely to be accurate because the lack of reducing means the memory load increases at
a very high rate.
--------------------------------}


-- (@) In this problem we will consider the garden-path sentence *while John
--     watched the baby cried* from the perspective of **incremental parsing**.
--     
--     a.  Give a **bottom-up** derivation of this sentence by listing, in
--         order, the configurations that result from either an application of
--         shift or an application of reduce. (Here, you only
--         need to supply the configuration component of each row, not the
--         transition name or production rule involved.) Remember, all the stack
--         symbols in a bottom up derivation are chunks you've _already seen_, so
--         they should all be un-barred.
--         

gardenTableBU :: [Config]
gardenTableBU =
  [ ([], ["while","John","watched","the","baby","cried"]) -- starting config
  , ([got W], ["John","watched","the","baby","cried"]) -- shift
  , ([got W, got NP], ["watched","the","baby","cried"]) -- shift
  , ([got W, got NP, got V], ["the","baby","cried"]) -- shift
  , ([got W, got NP, got VP], ["the","baby","cried"]) -- reduce
  , ([got W, got S], ["the","baby","cried"]) -- reduce
  , ([got W, got S, got D], ["baby","cried"]) -- shift
  , ([got W, got S, got D, got N], ["cried"]) -- shift
  , ([got W, got S, got NP], ["cried"]) -- reduce
  , ([got W, got S, got NP, got V], []) -- shift
  , ([got W, got S, got NP, got VP], []) -- reduce
  , ([got W, got S, got S], []) -- reduce
  , ([got S], []) -- reduce
  ]

--         Now that you have a successful parse, put yourself in the shoes of a
--         person who at first **mis-parses** the sentence in the way we have been
--         considering. How would that derivation have gone differently? Specifically,
--         at what step in the derivation above could you have made a wrong turn, and
--         what does that wrong turn consist in?

{-------------------------------
A mis-parse would interpret "John watched the baby" as an S, so "while John watched
the baby" would result in W S on the stack and create a situation with no rule to process
"cried" by itself. Instead of applying the V -> VP rule immediately after
seeing "watched", this parse would shift until seeing "baby", so "watched" would
still be its own transitive verb and the only option would be to reduce "the baby" to an NP after shifting the D and N,
"watched the baby" to a VP from VP -> V NP, and "John watched the baby" to an S (this time using S -> NP VP).
-------------------------------}

--     a.  Now, provide a **top-down** derivation of the garden-path sentence using
--         the rules predict and match. Keep in mind, all the
--         stack symbols here are _predictions_, so they should all be barred.

gardenTableTD :: [Config]
gardenTableTD =
  [ ([pre S], ["while","John","watched","the","baby","cried"]) -- starting config
  , ([pre W, pre S, pre S], ["while","John","watched","the","baby","cried"]) -- predict
  , ([pre S, pre S], ["John","watched","the","baby","cried"]) -- match
  , ([pre NP, pre VP, pre S], ["John","watched","the","baby","cried"]) -- predict
  , ([pre VP, pre S], ["watched","the","baby","cried"]) -- match
  , ([pre V, pre S], ["watched","the","baby","cried"]) -- predict
  , ([pre S], ["the","baby","cried"]) -- match
  , ([pre NP, pre VP], ["the","baby","cried"]) -- predict
  , ([pre D, pre N, pre VP], ["the","baby","cried"]) -- predict
  , ([pre N, pre VP], ["baby","cried"]) -- match
  , ([pre VP], ["cried"]) -- match
  , ([pre V], ["cried"]) -- predict
  , ([], []) -- match
  ]

--         As before, consider how a **mis-parse** would have gone instead. At what
--         step in the derivation could the wrong turn have happened, and what does
--         that wrong turn consist in? What differences (if any) do you see from how
--         the shift-reduce wrong turn transpires?

{-------------------------------
In a mis-parse, once "John" has been matched as a NP and the stack is [pre VP, pre S],
the parser would predict [pre V, pre NP] instead of [pre V] for the existing pre VP, leading "watched" to be
matched to the V but "the baby" to cause a prediction of a D and N earlier and be matched to the NP.
The stack in this contains all constituents that we have not seen yet but anticipate seeing, while it contains
all constituents that we have already seen in bottom-up, so the wrong turn comes from predicitng using the wrong rule
(predicting too many constituents) rather than shifting too many times.
-------------------------------}

--     a.  Let's suppose that the human parsing system "backtracks" when it reaches
--         a dead end configuration and realizes that it took a wrong turn, and has
--         to go back a few steps to start off down a different path. This works
--         simply by looking back (right-to-left) through the buffer in an obvious
--         way (i.e. going back to the point in the sentence where a wrong turn was
--         taken, and trying again). And suppose that this backtracking can be
--         detected in experiments where we track the movements of people's eyes as
--         they read. Explain how we could use our garden path sentence in such an
--         experiment to decide whether humans use a bottom-up parser or a top-down
--         parser. (Assume for this question that these are the only two
--         possibilities.)
--         

{-------------------------------
We could use the garden path sentence above in an experiment by tracking the size of the backwards and forwards eye movements
when reading the sentence; in top-down parsing, the movements when backtracking would be somewhat larger as top-down is recursive
and allows for entire constituents to be predicted, meaning people would attempt to go all the way back to a point where they had
expanded a certain constituent using the wrong prediction and start matching after making another one. However, in a bottom-up parser
it is not possible to "look ahead" and predict entire future constituents, so the eye movements may be smaller and perhaps
more frequent (e.g. only being able to go back to "baby" after first reaching the end) since it is only possible to
shift forwards and reduce adjacent constituents in the stack.
-------------------------------}
