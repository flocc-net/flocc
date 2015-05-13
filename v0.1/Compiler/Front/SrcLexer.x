{

module Compiler.Front.SrcLexer ( Token(..), scan ) where

}

%wrapper "basic"

$digit = 0-9			-- digits
$alpha = [a-zA-Z]		-- alphabetic characters
@int = [\+\-]?[0-9]+ 

tokens :-

  $white+				;
  "--".*				;
  let					{ \s -> TokLet }
  in					{ \s -> TokIn }
  if                                    { \s -> TokIf }
  then                                  { \s -> TokThen }
  else                                  { \s -> TokElse }
  null                                  { \s -> TokNull }
  [\\]                                  { \s -> TokBSlash }
  \->                                   { \s -> TokArrow }
  [\=]                                  { \s -> TokEq }
  [\,]                                  { \s -> TokComma }
  [_]                                   { \s -> TokUnderscore }
  \(                                    { \s -> TokLParen }
  \)                                    { \s -> TokRParen }
  \[                                    { \s -> TokLSqParen }
  \]                                    { \s -> TokRSqParen }
  $alpha [$alpha $digit \_ \']*		{ \s -> TokVar s }
  (True|False)                          { \s -> TokBool (read s) }
  @int                                  { \s -> TokInt (read s) }
  @int?\.$digit+([eE]@int)?             { \s -> TokFloat (read s) }
  @int\.$digit*([eE]@int)?              { \s -> TokFloat (read s) }
  \"\"                                  { \s -> TokString "" }
-- TODO: Need to make string lits work properly
--  \"(\\.|[^\\"])+\"                     { \s -> TokString (read s) }

{

-- |Data type for Lexer tokens
data Token
  = TokLet
  | TokIn
  | TokIf
  | TokThen
  | TokElse
  | TokBSlash
  | TokArrow
  | TokEq
  | TokComma
  | TokUnderscore
  | TokLParen
  | TokRParen
  | TokLSqParen
  | TokRSqParen
  | TokVar String
  | TokBool Bool
  | TokInt Int
  | TokFloat Float
  | TokString String
  | TokNull
    deriving (Eq, Show)

scan :: String -> [Token]
scan = alexScanTokens

}
