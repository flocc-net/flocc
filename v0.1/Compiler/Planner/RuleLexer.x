{

module Compiler.Planner.RuleLexer ( Token(..), PosnToken(..), scanRuleSet ) where

}

%wrapper "posn"

$digit = 0-9			-- digits
$alpha = [a-zA-Z]		-- alphabetic characters
@int = [\+\-]?[0-9]+ 

tokens :-

  $white+				;
  "--".*				;
  ruleset                               { makeToken $ \s -> TokRuleset }
  level                                 { makeToken $ \s -> TokLevel }
  let					{ makeToken $ \s -> TokLet }
  in					{ makeToken $ \s -> TokIn }
  if                                    { makeToken $ \s -> TokIf }
  then                                  { makeToken $ \s -> TokThen }
  else                                  { makeToken $ \s -> TokElse }
  null                                  { makeToken $ \s -> TokNull }
  [\\]                                  { makeToken $ \s -> TokBSlash }
  \=>                                   { makeToken $ \s -> TokImplies }
  \->                                   { makeToken $ \s -> TokArrow }
  [\=]                                  { makeToken $ \s -> TokEq }
  [\,]                                  { makeToken $ \s -> TokComma }
  [_]                                   { makeToken $ \s -> TokUnderscore }
  \(                                    { makeToken $ \s -> TokLParen }
  \)                                    { makeToken $ \s -> TokRParen }
  \[                                    { makeToken $ \s -> TokLSqParen }
  \]                                    { makeToken $ \s -> TokRSqParen }
  \|                                    { makeToken $ \s -> TokBar }
  \:                                    { makeToken $ \s -> TokColon }
  \;                                    { makeToken $ \s -> TokSemiColon }
  $alpha [$alpha $digit \_ \']*		{ makeToken $ \s -> TokVar s }
  (True|False)                          { makeToken $ \s -> TokBool (read s) }
  @int                                  { makeToken $ \s -> TokInt (read s) }
  @int?\.$digit+([eE]@int)?             { makeToken $ \s -> TokFloat (read s) }
  @int\.$digit*([eE]@int)?              { makeToken $ \s -> TokFloat (read s) }
  \"\"                                  { makeToken $ \s -> TokString "" }
-- TODO: Need to make string lits work properly
--  \"(\\.|[^\\"])+\"                   { makeToken $ \s -> TokString (read s) }

{


data PosnToken = PosnTok Int Int Int Token
  deriving (Eq) 

instance Show PosnToken where
  show (PosnTok _ _ _ t) = show t

makeToken :: (String -> Token) -> AlexPosn -> String -> PosnToken
makeToken f (AlexPn charOff lineNum colNum) s = PosnTok charOff lineNum colNum (f s)

-- |Data type for Lexer tokens
data Token
  = TokRuleset
  | TokLevel 
  | TokLet
  | TokIn
  | TokIf
  | TokThen
  | TokElse
  | TokBSlash
  | TokImplies
  | TokArrow
  | TokEq
  | TokComma
  | TokUnderscore
  | TokLParen
  | TokRParen
  | TokLSqParen
  | TokRSqParen
  | TokBar
  | TokColon
  | TokSemiColon
  | TokVar String
  | TokBool Bool
  | TokInt Int
  | TokFloat Float
  | TokString String
  | TokNull
    deriving (Eq, Show)

scanRuleSet :: String -> [PosnToken]
scanRuleSet = alexScanTokens

}
