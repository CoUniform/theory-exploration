module Utils where

import Data.List
import Control.Monad
import Text.ParserCombinators.Parsec
import Text.ParserCombinators.Parsec.Expr
import Text.ParserCombinators.Parsec.Language
import Text.ParserCombinators.Parsec.Token


prependSpace :: String -> String
prependSpace = (' ' :)

composeList :: [a -> a] -> a -> a
composeList = foldl (.) id

-- with space in the beginning
unwordsShowS :: [ShowS] -> ShowS
unwordsShowS = composeList . map (\wS -> (prependSpace . wS))

unwordsWith :: String -> [ShowS] -> ShowS
unwordsWith sep [] = id
unwordsWith sep (hS : wSs) = hS . composeList (map (\wS -> ((sep ++) . wS)) wSs) 

listUnion :: Eq a => [[a]] -> [a]
listUnion = foldr union []

freshifyName :: [String] -> String -> String
freshifyName forbidden x | x `elem` forbidden = freshifyName forbidden (x ++ "\'")
                         | otherwise = x

noDup :: Eq a => [a] -> Bool
noDup [] = True
noDup (x : xs) = not (elem x xs) && noDup xs

firstJust :: [Maybe a] -> Maybe a
firstJust [] = Nothing
firstJust (Nothing : ms) = firstJust ms
firstJust (m : ms) = m

getLines :: IO String
getLines = do
  l <- getLine
  case l of "" -> return ""
            _ -> ((l ++ "\n") ++) <$> getLines


langDef :: LanguageDef st 
langDef = emptyDef{ identStart = choice (map char ['a'..'z']),
                    opLetter = oneOf $ nub $ concat $ reservedOpNames langDef,
                    reservedOpNames = [".", "\\", "λ", "/\\", "->", "∀", "∃", ":", ";"],
                    reservedNames = ["fix", "forall", "exists"] }

lexer = makeTokenParser langDef

pIdentifier = identifier lexer
pNatural = natural lexer
pReserved = reserved lexer
pReservedOp = reservedOp lexer
pParens = parens lexer

pConst :: [String] -> Parser String
pConst fVars = do
  c <- pIdentifier <|> (show <$> pNatural)
  guard (not $ c `elem` fVars)
  return c

pVar :: [String] -> Parser String
pVar fVars = do
  c <- pIdentifier
  guard (c `elem` fVars)
  return c

parseWholeString :: Parser a -> String -> Either ParseError a
parseWholeString p = parse (p <* eof) ""


data NatInf = Nat Int | Inf

decrNatInf :: NatInf -> NatInf
decrNatInf (Nat n) = Nat (n - 1)
decrNatInf Inf = Inf
