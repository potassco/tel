{-# LANGUAGE FlexibleContexts, CPP, RecordWildCards, ViewPatterns, ScopedTypeVariables, DeriveDataTypeable, OverloadedStrings #-}

module Main (main) where

import Text.Parsec (Stream, ParsecT, ParseError, char, (<|>), optional, many1, digit, oneOf, spaces, try, string, notFollowedBy, (<?>), many, lower, option, sepBy, parse, eof, endOfLine, manyTill, anyChar, skipMany)
import Text.Parsec.Expr (buildExpressionParser, Operator(..), Assoc(..))
import Control.Monad
import Control.Monad.State
import Data.Maybe
import qualified Data.List as List
import Data.Char (digitToInt)
import Data.Map (Map)
import qualified Data.Map as Map
import qualified Data.Set as Set
import System.Console.CmdArgs
import System.IO
import System.Exit
import System.Process

#define TEL_TESTS

#ifdef TEL_TESTS
import Test.HUnit ((@?=))
import Test.Framework (testGroup, defaultMainWithArgs)
import Test.Framework.Providers.HUnit (testCase)
import qualified Data.Vector as Vector
import qualified Data.HashMap.Lazy as HashMap
import qualified Data.Aeson as Aeson
import qualified Data.ByteString.Lazy.Char8 as BS
#endif

-- {{{1 data structures

data Term = Term String [Term]
    deriving (Eq, Ord)

data Formula
    = FormulaTrue
    | FormulaFalse
    | FormulaAtom Term
    | FormulaNegation Formula
    | FormulaPrevious Formula
    | FormulaNext Formula
    | FormulaSince Formula Formula
    | FormulaUntil Formula Formula
    | FormulaTrigger Formula Formula
    | FormulaRelease Formula Formula
    | FormulaAnd Formula Formula
    | FormulaOr Formula Formula
    | FormulaImplies Formula Formula
    deriving (Eq, Ord)

data Theory = Theory [Formula]

data Literal = Literal { literalCurrent :: Bool, literalPositive :: Bool, literalAtom :: Term}

data RuleType = InitialRule | DynamicRule | FinalRule deriving Eq

data Rule = Rule RuleType [Literal] [Literal]

data Program = Program [Rule]

-- {{{1 printing

data Associativity = AssociativityLeft Integer | AssociativityRight Integer | AssociativityNone Integer | AssociativityAtomic deriving Eq

assocPrec (AssociativityLeft x)  = Just x
assocPrec (AssociativityRight x) = Just x
assocPrec (AssociativityNone x)  = Just x
assocPrec (AssociativityAtomic)  = Nothing

assocGreater a b | Just pa <- assocPrec (prec a)
                 , Just pb <- assocPrec (prec b) = pa > pb
                 | otherwise = True

prec (FormulaImplies _ _) = AssociativityLeft 10
prec (FormulaOr _ _)      = AssociativityLeft 9
prec (FormulaAnd _ _)     = AssociativityLeft 8
prec (FormulaRelease _ _) = AssociativityLeft 7
prec (FormulaTrigger _ _) = AssociativityLeft 7
prec (FormulaSince _ _)   = AssociativityLeft 7
prec (FormulaUntil _ _)   = AssociativityLeft 7
prec (FormulaTrue)        = AssociativityAtomic
prec (FormulaFalse)       = AssociativityAtomic
prec (FormulaAtom _)      = AssociativityAtomic
prec (FormulaNext _)      = AssociativityNone 1
prec (FormulaPrevious _)  = AssociativityNone 1
prec (FormulaNegation _)  = AssociativityNone 1

showLeft t s
    | assocGreater t s = show s
    | (AssociativityLeft x) <- prec t
    , Just y <- assocPrec (prec s)
    , x >= y
    = show s
    | otherwise = "(" ++ show s ++ ")"
showRight t s
    | assocGreater t s = show s
    | (AssociativityRight x) <- prec t
    , Just y <- assocPrec (prec s)
    , x >= y
    = show s
    | otherwise = "(" ++ show s ++ ")"
showUnary t s
    | assocGreater t s = show s
    -- | prec t == prec s = show s
    | otherwise = "(" ++ show s ++ ")"

instance Show Term where
    show (Term name []) = name
    show (Term name args) = name ++ "(" ++ List.intercalate "," (map show args) ++ ")"

instance Show Formula where
    show FormulaTrue            = "#true"
    show FormulaFalse           = "#false"
    show (FormulaAtom x)        = show x
    show t@(FormulaNegation x)  = "~" ++ showUnary t x
    show t@(FormulaPrevious x)  = "#previous " ++ showUnary t x
    show t@(FormulaNext x)      = "#next " ++ showUnary t x
    show t@(FormulaSince x y)   = showLeft t x ++ " #since " ++ showRight t y
    show t@(FormulaUntil x y)   = showLeft t x ++ " #until " ++ showRight t y
    show t@(FormulaTrigger x y) = showLeft t x ++ " #trigger " ++ showRight t y
    show t@(FormulaRelease x y) = showLeft t x ++ " #release " ++ showRight t y
    show t@(FormulaAnd x y)     = showLeft t x ++ " & " ++ showRight t y
    show t@(FormulaOr x y)      = showLeft t x ++ " | " ++ showRight t y
    show t@(FormulaImplies x y) = showLeft t x ++ " -> " ++ showRight t y

instance Show Theory where
    show (Theory t) = List.intercalate "\n" [ show f ++ "." | f <- t ]

instance Show Literal where
    show Literal {..} = (if literalCurrent then "" else "#previous ") ++ (if literalPositive then "" else "~") ++ show literalAtom

instance Show Rule where
    show (Rule _ (map show -> hd) (map show -> bd))
        | [] <- bd  = List.intercalate "; " hd
        | otherwise = List.intercalate "; " hd ++ " :- " ++ List.intercalate ", " bd

isDynamic r | Rule DynamicRule _ _ <- r = True
            | otherwise                 = False
isInitial r | Rule InitialRule _ _ <- r = True
            | otherwise                 = False

partitionProgram (Program rules) = (initial, dynamic, final) where
    (dynamic, List.partition isInitial -> (initial, final)) = List.partition isDynamic rules

instance Show Program where
    show (Program t) = showPart "#initial." initial ++ showPart "#dynamic." dynamic ++ showPart "#final." final where
        (initial, dynamic, final) = partitionProgram (Program t)
        showPart _ [] = ""
        showPart h p = h ++ "\n" ++ concat [ show r ++ ".\n" | r <- p ]

showTranslated b (Program t)
    =  concat [ showRule r ++ ".\n" | r <- initial ]
    ++ "#show.\n"
    ++ concat
        [ "#show " ++ name ++ "/" ++ show arity ++ ".\n"
        | (name, arity) <- Set.toList . Set.fromList $
            [ (name, arity) | (name, arity) <- concat $ map sigsRule t
            , take 2 name /= "__"
            ]
        ]
    where
        sigsRule (Rule _ hd bd) = (map sigLiteral hd) ++ (map sigLiteral bd)
        sigLiteral Literal {..} = (name, length args) where Term name args = literalAtom
        (initial, _, _) = partitionProgram (Program t)
        showRule (Rule _ (map showLiteral -> hd) (map showLiteral -> bd))
            | [] <- bd  = List.intercalate "; " hd
            | otherwise = List.intercalate "; " hd ++ " :- " ++ List.intercalate ", " bd
        showLiteral Literal {..}
            |     literalPositive && (time < 0 || time > b) = "#false"
            | not literalPositive && (time < 0 || time > b) = "#true"
            | otherwise = (if literalPositive then "" else "not ") ++ show literalAtom
            where Term _ (read . show . last -> time :: Int) = literalAtom

-- {{{1 parsing

int :: (Stream s m Char, Integral i) => ParsecT s u m i
int = ap sign nat

sign :: (Stream s m Char, Num i) => ParsecT s u m (i -> i)
sign = (char '-' >> return negate) <|> (optional (char '+') >> return id)

nat :: (Stream s m Char, Integral i) => ParsecT s u m i
nat = do
    n <- liftM (numberValue) (many1 digit)
    seq n (return n)

numberValue :: Integral i => String -> i
numberValue = foldl (\ x -> ((10 * x) +) . fromIntegral . digitToInt) 0

letterOrDigit :: Stream s m Char => ParsecT s u m Char
letterOrDigit = oneOf $ ['a'..'z'] ++ ['A'..'Z'] ++ ['0'..'9'] ++ ['_']

commentP :: Stream s m Char => ParsecT s u m ()
commentP = spaces >> (skipMany $ char '%' >> manyTill anyChar (try endOfLine >> spaces))

lexeme :: Stream s m Char => ParsecT s u m r -> ParsecT s u m r
lexeme p = p <* commentP

charL :: Stream s m Char => Char -> ParsecT s u m Char
charL = lexeme . char

reservedOp :: Stream s m Char => String -> ParsecT s u m ()
reservedOp name = lexeme $ try (string name >> notFollowedBy letterOrDigit <?> ("end of " ++ show name))

formulaP :: Stream s m Char => ParsecT s u m Formula
formulaP = buildExpressionParser
    [ [ Prefix ((lexeme $ string "~") >> return FormulaNegation)
      , Prefix ((try . lexeme . string $ "#previous^") >> return weakPrevious)
      , Prefix ((try . lexeme . string $ "#next^") >> return weakNext)
      , Prefix ((try . lexeme . string $ "#always+") >> return alwaysF)
      , Prefix ((try . lexeme . string $ "#always-") >> return alwaysP)
      , Prefix ((try . lexeme . string $ "#eventually+") >> return eventuallyF)
      , Prefix ((try . lexeme . string $ "#eventually-") >> return eventuallyP)
      , Prefix ((reservedOp "#previous") >> return FormulaPrevious)
      , Prefix ((reservedOp "#next") >> return FormulaNext)
      ]
    , [ Infix (reservedOp "#since" >> return FormulaSince) AssocLeft
      , Infix (reservedOp "#until" >> return FormulaUntil) AssocLeft
      , Infix (reservedOp "#release" >> return FormulaRelease) AssocLeft
      , Infix (reservedOp "#trigger" >> return FormulaTrigger) AssocLeft
      ]
    , [ Infix ((lexeme $ string "&") >> return FormulaAnd) AssocLeft ]
    , [ Infix ((lexeme $ string "|") >> return FormulaOr) AssocLeft ]
    , [ Infix ((lexeme $ string "->") >> return FormulaImplies) AssocLeft ]
    ]
    atomP where
        initial        = FormulaNegation $ FormulaPrevious FormulaTrue
        final          = FormulaNegation $ FormulaNext FormulaTrue
        weakPrevious f = FormulaOr (FormulaPrevious f) initial
        weakNext f     = FormulaOr (FormulaNext f) final
        alwaysP        = FormulaTrigger FormulaFalse
        alwaysF        = FormulaRelease FormulaFalse
        eventuallyP    = FormulaSince FormulaTrue
        eventuallyF    = FormulaUntil FormulaTrue

        termP :: Stream s m Char => ParsecT s u m Term
        termP = (\(show -> name) -> Term name []) <$> lexeme int <|> predicateP

        predicateP :: Stream s m Char => ParsecT s u m Term
        predicateP = do
            p <- many $ char '_'
            f <- lower
            t <- lexeme $ many letterOrDigit
            args <- option [] $ do
                charL '('
                list <- termP `sepBy` (charL ',')
                charL ')'
                return list
            return $ Term (p ++ f : t) args

        atomP :: Stream s m Char => ParsecT s u m Formula
        atomP
            =   reservedOp "#true"  *> pure FormulaTrue
            <|> reservedOp "#false" *> pure FormulaFalse
            <|> reservedOp "#initial" *> pure initial
            <|> reservedOp "#final" *> pure final
            <|> FormulaAtom <$> predicateP
            <|> charL '(' *> formulaP <* charL ')'

theoryP :: Stream s m Char => ParsecT s u m Theory
theoryP = Theory <$> (many (lexeme formulaP <* charL '.'))

parseTheory :: String -> Either ParseError Theory
parseTheory text = parse (commentP *> lexeme theoryP <* eof) "" text

-- {{{1 normalization

type NormalizeState = (Int, [Rule], Map Formula Term)

appendRule :: Rule -> State NormalizeState ()
appendRule r = modify $ \(i, l, m) -> (i, r:l, m)

appendRules :: [Rule] -> State NormalizeState ()
appendRules = mapM_ appendRule

newIdent :: State NormalizeState Term
newIdent = get >>= \(i, l, m) -> put (i + 1, l, m) >> return (Term ("__l" ++ show i) [])

normalizeFormula :: Formula -> State NormalizeState Term
normalizeFormula f = do
    (_, _, m) <- get
    let ret = Map.lookup f m
    if isJust ret
        then return $ fromJust ret
        else do
            i <- normalizeFormula' f
            modify $ \(n, l, m') -> (n, l, Map.insert f i m')
            return i
    where
        normalizeFormula' :: Formula -> State NormalizeState Term
        normalizeFormula' f
            | FormulaTrue <- f = do
                i <- newIdent
                appendRules [Rule rt [Literal True True i] [] | rt <- static]
                return i
            | FormulaFalse <- f = do
                i <- newIdent
                appendRules [Rule rt [] [Literal True True i] | rt <- static]
                return i
            | FormulaAtom p <- f = return p
            | FormulaAnd a b <- f = do
                [x, y, i] <- nb a b
                appendRules [Rule rt [Literal True True z] [Literal True True i] | rt <- static, z <- [x, y]]
                appendRules [Rule rt [Literal True True i] [Literal True True x, Literal True True y] | rt <- static]
                return i
            | FormulaOr a b <- f = do
                [x, y, i] <- nb a b
                appendRules [Rule rt [Literal True True i] [Literal True True z] | rt <- static, z <- [x, y]]
                appendRules [Rule rt [Literal True True x, Literal True True y] [Literal True True i] | rt <- static]
                return i
            | FormulaImplies a b <- f = do
                [x, y, i] <- nb a b
                appendRules [Rule rt [Literal True True y] [Literal True True i, Literal True True x] | rt <- static]
                appendRules [Rule rt [Literal True True i] [Literal True False x] | rt <- static]
                appendRules [Rule rt [Literal True True i] [Literal True True y] | rt <- static]
                appendRules [Rule rt [Literal True True x, Literal True False y, Literal True True i] [] | rt <- static]
                return i
            | FormulaNegation a <- f = do
                [x, i] <- nu a
                appendRules [Rule rt [Literal True False x] [Literal True True i] | rt <- static]
                appendRules [Rule rt [Literal True True i] [Literal True False x] | rt <- static]
                return i
            | FormulaPrevious a <- f = pn a False
            | FormulaNext a <- f = pn a True
            | FormulaSince a b <- f = su a b False
            | FormulaUntil a b <- f = su a b True
            | FormulaTrigger a b <- f = tr a b False
            | FormulaRelease a b <- f = tr a b True

        static = [InitialRule, DynamicRule]
        nu a = sequence [normalizeFormula a, newIdent]
        nb a b = sequence [normalizeFormula a, normalizeFormula b, newIdent]
        pn a s = do
            [x, i] <- nu a
            let rt = if s then FinalRule else InitialRule
            appendRules
                [ Rule DynamicRule [Literal s True x] [Literal (not s) True i]
                , Rule DynamicRule [Literal (not s) True i] [Literal s True x]
                , Rule rt [Literal True False i] []
                ]
            return i
        su a b s = do
            [x, y, i] <- nb a b
            let rt = if s then FinalRule else InitialRule
            appendRules
                [ Rule DynamicRule [Literal (not s) True x, Literal (not s) True y] [Literal (not s) True i]
                , Rule DynamicRule [Literal s True i, Literal (not s) True y] [Literal (not s) True i]
                , Rule DynamicRule [Literal (not s) True i] [Literal (not s) True x, Literal s True i]
                , Rule DynamicRule [Literal (not s) True i] [Literal (not s) True y]
                , Rule rt [Literal True True y] [Literal True True i]
                , Rule rt [Literal True True i] [Literal True True y]
                ]
            return i
        tr a b s = do
            [x, y, i] <- nb a b
            let rt = if s then FinalRule else InitialRule
            appendRules
                [ Rule DynamicRule [Literal (not s) True y] [Literal (not s) True i]
                , Rule DynamicRule [Literal (not s) True x, Literal s True i] [Literal (not s) True i]
                , Rule DynamicRule [Literal (not s) True i] [Literal (not s) True x, Literal (not s) True y]
                , Rule DynamicRule [Literal (not s) True i] [Literal s True i, Literal (not s) True y]
                , Rule rt [Literal True True y] [Literal True True i]
                , Rule rt [Literal True True i] [Literal True True y]
                ]
            return i

normalizeTheory (Theory t) = Program rules where
    state = (0, [], Map.empty)
    nt = mapM_ (\f -> normalizeFormula f >>= \i -> appendRule (Rule InitialRule [Literal True True i] [])) t
    (_, rules, _) = execState nt state

-- {{{1 bounded translation

addTime k (Term name args) = Term name (args ++ [Term (show k) []])

translateLiteral k (Literal {..})
    | not literalCurrent = translateLiteral (k-1) Literal {literalCurrent = True, ..}
    | otherwise          = Literal {literalAtom = addTime k literalAtom, ..}
translateRule k (Rule _ hd bd) = Rule InitialRule (map (translateLiteral k) hd) (map (translateLiteral k) bd)

translateRules k rules = map (translateRule k) rules

translateProgram b p = Program $ translateRules 0 initial ++ concat [ translateRules i dynamic | i <- [1..b] ] ++ translateRules b final where
    (initial, dynamic, final) = partitionProgram p

-- {{{1 unit tests

#ifdef TEL_TESTS
tests =
    -- {{{2 Parsing
    [ testGroup "Parsing"
        [ testCase "empty" (testParseSimple "")
        , testCase "atomic" $ do
            testParseSimple "#true."
            testParseSimple "#false."
            let atm = "p ( 1 , 2 , f ( _a , 3 ) ) ."
                atm' = [ x | x <- atm, x /= ' ' ]
            testParseSimple atm'
            testParse atm atm'
            testParse "(a)." "a."
        , testCase "unary" $ do
            testParseSimple "~a."
            testParseSimple "~(~a)."
            testParseSimple "#previous a."
            testParseSimple "#next a."
        , testCase "binary" $ do
            testParseSimple "a #until b."
            testParseSimple "a #trigger b."
            testParseSimple "a #since b."
            testParseSimple "a #release b."
        , testCase "boolean" $ do
            testParseSimple "a & b."
            testParseSimple "a | b."
            testParseSimple "a -> b."
        , testCase "derived" $ do
            testParse "#initial." "~(#previous #true)."
            testParse "#final." "~(#next #true)."
            testParse "#next^ b." "#next b | ~(#next #true)."
            testParse "#previous^ b." "#previous b | ~(#previous #true)."
            testParse "#always+ b." "#false #release b."
            testParse "#always- b." "#false #trigger b."
            testParse "#eventually+ b." "#true #until b."
            testParse "#eventually- b." "#true #since b."
        , testCase "complex" $ do
            let test1 = FormulaImplies t o where
                    t = FormulaTrue
                    f = FormulaFalse
                    p = FormulaAtom (Term "p" [])
                    o = FormulaOr f a
                    a = FormulaAnd p r
                    r = FormulaRelease p tr
                    tr = FormulaTrigger p un
                    un = FormulaUntil p si
                    si = FormulaSince p ne
                    ne = FormulaNext pr
                    pr = FormulaPrevious ng
                    ng = FormulaNegation p
                test2 = show $ Theory [test1, test1]
            testParseSimple test2
        ]
    -- {{{2 Normalizing
    , testGroup "normalizing"
        [ testCase "empty" (testNormalize "" [])
        , testCase "atomic" $ do
            testNormalize "#true." ["#initial.", "__l0.", "__l0.", "#dynamic.", "__l0."]
            testNormalize "#false." ["#initial.", "__l0.", " :- __l0.", "#dynamic.", " :- __l0."]
            testNormalize "a." ["#initial.", "a."]
        , testCase "unary" $ do
            testNormalize "~a."
                [ "#initial."
                , "__l0."
                , "__l0 :- ~a."
                , "~a :- __l0."
                , "#dynamic."
                , "__l0 :- ~a."
                , "~a :- __l0."
                ]
            testNormalize "~(~a)."
                [ "#initial."
                , "__l1."
                -- l1 == ~(~a)
                , "__l1 :- ~__l0."
                , "~__l0 :- __l1."
                -- l0 == ~a
                , "__l0 :- ~a."
                , "~a :- __l0."
                , "#dynamic."
                -- l1 == ~(~a)
                , "__l1 :- ~__l0."
                , "~__l0 :- __l1."
                -- l0 == ~a
                , "__l0 :- ~a."
                , "~a :- __l0."
                ]
            testNormalize "#previous a."
                [ "#initial."
                , "__l0."
                , "~__l0."
                , "#dynamic."
                , "__l0 :- #previous a."
                , "#previous a :- __l0."
                ]
            testNormalize "#next a."
                [ "#initial."
                , "__l0."
                , "#dynamic."
                , "#previous __l0 :- a."
                , "a :- #previous __l0."
                , "#final."
                , "~__l0."
                ]
        , testCase "boolean" $ do
            testNormalize "a & b."
                [ "#initial."
                , "__l0."
                , "__l0 :- a, b."
                , "b :- __l0."
                , "a :- __l0."
                , "#dynamic."
                , "__l0 :- a, b."
                , "b :- __l0."
                , "a :- __l0."
                ]
            testNormalize "a | b."
                [ "#initial."
                , "__l0."
                , "a; b :- __l0."
                , "__l0 :- b."
                , "__l0 :- a."
                , "#dynamic."
                , "a; b :- __l0."
                , "__l0 :- b."
                , "__l0 :- a."
                ]
            testNormalize "a -> b."
                [ "#initial."
                , "__l0."
                , "a; ~b; __l0."
                , "__l0 :- b."
                , "__l0 :- ~a."
                , "b :- __l0, a."
                , "#dynamic."
                , "a; ~b; __l0."
                , "__l0 :- b."
                , "__l0 :- ~a."
                , "b :- __l0, a."
                ]
        , testCase "binary" $ do
            testNormalize "a #until b."
                [ "#initial."
                , "__l0."
                , "#dynamic."
                , "#previous __l0 :- #previous b."
                , "#previous __l0 :- #previous a, __l0."
                , "__l0; #previous b :- #previous __l0."
                , "#previous a; #previous b :- #previous __l0."
                , "#final."
                , "__l0 :- b."
                , "b :- __l0."
                ]
            testNormalize "a #since b."
                [ "#initial."
                , "__l0."
                , "__l0 :- b."
                , "b :- __l0."
                , "#dynamic."
                , "__l0 :- b."
                , "__l0 :- a, #previous __l0."
                , "#previous __l0; b :- __l0."
                , "a; b :- __l0."
                ]
            testNormalize "a #trigger b."
                [ "#initial."
                , "__l0."
                , "__l0 :- b."
                , "b :- __l0."
                , "#dynamic."
                , "__l0 :- #previous __l0, b."
                , "__l0 :- a, b."
                , "a; #previous __l0 :- __l0."
                , "b :- __l0."
                ]
            testNormalize "a #release b."
                [ "#initial."
                , "__l0."
                , "#dynamic."
                , "#previous __l0 :- __l0, #previous b."
                , "#previous __l0 :- #previous a, #previous b."
                , "#previous a; __l0 :- #previous __l0."
                , "#previous b :- #previous __l0."
                , "#final."
                , "__l0 :- b."
                , "b :- __l0."
                ]
        , testCase "nested" $ do
            testNormalize "a & b -> p."
                [ "#initial."
                , "__l1."
                -- l1 <=> (l0 => p)
                , "__l0; ~p; __l1."
                , "__l1 :- p."
                , "__l1 :- ~__l0."
                , "p :- __l1, __l0."
                -- l0 <=> a & b
                , "__l0 :- a, b."
                , "b :- __l0."
                , "a :- __l0."
                , "#dynamic."
                -- l1 <=> (l0 => p)
                , "__l0; ~p; __l1."
                , "__l1 :- p."
                , "__l1 :- ~__l0."
                , "p :- __l1, __l0."
                -- l0 <=> a & b
                , "__l0 :- a, b."
                , "b :- __l0."
                , "a :- __l0."
                ]
        ]
    -- {{{2 Translating
    , testGroup "translating"
        [ testCase "empty" (testTranslate 3 "" [[]])
        , testCase "atomic" $ do
            testTranslate 3 "#true." [[]]
            testTranslate 3 "#false." []
            testTranslate 3 "a." [["a(0)"]]
            testTranslate 3 "#initial." [[]]
            testTranslate 3 "#final." []
            testTranslate 0 "#final." [[]]
        , testCase "unary" $ do
            testTranslate 3 "~a." [[]]
            testTranslate 3 "~(~a)." []
            testTranslate 3 "#previous a." []
            testTranslate 3 "#previous^ a." [[]]
            testTranslate 3 "#next a." [["a(1)"]]
            testTranslate 0 "#next a." []
            testTranslate 3 "#next^ a." [["a(1)"]]
            testTranslate 0 "#next^ a." [[]]
            testTranslate 3 "#next (#previous a)." [["a(0)"]]
            testTranslate 0 "#next (#previous a)." []
            testTranslate 3 "#previous (#next a)." []
        , testCase "boolean" $ do
            testTranslate 3 "a & b." [["a(0)", "b(0)"]]
            testTranslate 3 "a | b." [["a(0)"], ["b(0)"]]
            testTranslate 3 "a -> b. a." [["a(0)", "b(0)"]]
        , testCase "binary" $ do
            testTranslate 3 "a #until b." [["a(0)", "a(1)", "a(2)", "b(3)"],["a(0)", "a(1)", "b(2)"],["a(0)", "b(1)"],["b(0)"]]
            testTranslate 3 "a #since b." [["b(0)"]]
            testTranslate 3 "a #trigger b." [["b(0)"]]
            testTranslate 3 "a #release b." [["a(0)", "b(0)"],["a(1)", "b(0)", "b(1)"],["a(2)", "b(0)", "b(1)", "b(2)"],["b(0)", "b(1)", "b(2)", "b(3)"]]
        , testCase "derived" $ do
            testTranslate 3 "#always+ a." [["a(0)","a(1)","a(2)","a(3)"]]
            testTranslate 3 "#always- a." [["a(0)"]]
            testTranslate 3 "#eventually+ a." [["a(0)"],["a(1)"],["a(2)"],["a(3)"]]
            testTranslate 3 "#eventually- a." [["a(0)"]]
            -- Note: does only make sense with infinite traces
            testTranslate 3 (unlines
                [ "#always+ (load -> #next loaded)."
                , "#always+ (load & #previous loaded -> #false)."
                , "#always+ (shoot & #previous loaded & ~fail -> unloaded)."
                , "#always+ (#previous loaded & ~unloaded -> loaded)."
                , "#always+ (#previous unloaded & ~loaded -> unloaded)."
                , "#always+ (#next (shoot | load | wait))."
                , "#always+ (#next (shoot & load -> #false))."
                , "#always+ (#next (shoot & wait -> #false))."
                , "#always+ (#next (wait & load -> #false))."
                ]) []
        ]
    -- }}}2
    ]
    where
        testParse s r = (fmap show . parseTheory $ s) @?= Right r
        testParseSimple s = testParse s s

        fromEither (Right a) = a
        fromEither _         = error "should not happen"
        testNormalize s r = (lines . show . normalizeTheory . fromEither . parseTheory $ s) @?= r

        testTranslate b prg ret = do
            let n = showTranslated b . translateProgram b . normalizeTheory . fromEither . parseTheory $ prg
            (_, out, _) <- readProcessWithExitCode "clingo" ["0", "--outf=2"] n
            let Just (Aeson.Object dec) = Aeson.decode $ BS.pack out :: Maybe Aeson.Value
                (HashMap.lookup "Result" -> (Just (Aeson.String res))) = dec
                toAtom (Aeson.String s) = s
                toValue (Aeson.Object (HashMap.lookup "Value" -> Just (Aeson.Array (Vector.toList -> set)))) = List.sort (map toAtom set)
                (HashMap.lookup "Call" -> Just (Aeson.Array (Vector.head -> Aeson.Object
                    (HashMap.lookup "Witnesses" -> Just (Aeson.Array (Vector.toList -> r)))))) = dec
                r' = List.sort $ map toValue r
            if res == "SATISFIABLE"
                then r' @?= ret
                else [] @?= ret

#endif

-- {{{1 main

data Tel
    = Normalize
    | Translate {translateBound :: Int}
#ifdef TEL_TESTS
    | Test {testList :: Bool, testSelect :: [String]}
#endif
    deriving (Show, Data, Typeable)

main = do
    options <- cmdArgs (modes
        [ Translate (def &= typ "BOUND" &= argPos 0) &= auto &= help "Translate the temporal formula read from stdin into a bounded asp program"
        , Normalize &= help "Normalize the temporal formula read from stdin"
#ifdef TEL_TESTS
        , Test
            (def &= explicit &= name "l" &= name "list-tests"   &= help "list available tests but don't run any; useful to guide subsequent --select-tests")
            (def &= explicit &= name "t" &= name "select-tests" &= help "only tests that match at least one glob pattern given by an instance of this argument will be run")
            &= help "Run unit tests"

#endif
        ] &= help "Translate or normalize temporal formulas")
    case options
        of
            Normalize -> do
                contents <- getContents
                let theoryE = parseTheory contents
                case theoryE of
                    Right theory -> putStr (show . normalizeTheory $ theory)
                    Left err     -> hPutStrLn stderr (show err) >> exitFailure
            Translate {..} -> do
                contents <- getContents
                let theoryE = parseTheory contents
                case theoryE of
                    Right theory -> do
                        putStr (showTranslated translateBound . translateProgram translateBound . normalizeTheory $ theory)
                    Left err     -> hPutStrLn stderr (show err) >> exitFailure
#ifdef TEL_TESTS
            Test l patterns  ->
                let x [] = []
                    x (h:t) = "-t":h:(x t)
                in defaultMainWithArgs tests $ (if l then ["-l"] else []) ++ x patterns
#endif
