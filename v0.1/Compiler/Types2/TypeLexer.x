{

module Compiler.Types2.TypeLexer ( Token(..), PosnToken(..), scanTypes ) where

}

%wrapper "posn"

$digit = 0-9			-- digits
$ucAlpha = [A-Z]                -- upper case characters
$lcAlpha = [a-z]                -- lower case characters
$alpha = [a-zA-Z]		-- alphabetic characters

tokens :-

  [\ \t\f\v\r]+                         ;
  [\n]+                                 { makeToken $ \s -> TokEOL }
  "--".*\n				;
  \->                                   { makeToken $ \s -> TokArrow }
  \=>                                   { makeToken $ \s -> TokImplies }
  [\,]                                  { makeToken $ \s -> TokComma }
  [_]                                   { makeToken $ \s -> TokUnderscore }
  \(                                    { makeToken $ \s -> TokLParen }
  \)                                    { makeToken $ \s -> TokRParen }  
  \:\:                                  { makeToken $ \s -> TokColon }
  forall                                { makeToken $ \s -> TokForall }
  $ucAlpha [$alpha $digit \_ \']*       { makeToken $ \s -> TokName s }
  $lcAlpha [$alpha $digit \_ \']*	{ makeToken $ \s -> TokVar s }

{

data PosnToken = PosnTok Int Int Int Token
  deriving (Eq) 

instance Show PosnToken where
  show (PosnTok _ _ _ t) = show t

makeToken :: (String -> Token) -> AlexPosn -> String -> PosnToken
makeToken f (AlexPn charOff lineNum colNum) s = PosnTok charOff lineNum colNum (f s)

-- |Data type for Lexer tokens
data Token = 
    TokArrow
  | TokImplies
  | TokEOL
  | TokComma
  | TokUnderscore
  | TokLParen
  | TokRParen
  | TokColon
  | TokForall
  | TokName String
  | TokVar String
    deriving (Eq)

instance Show Token where
  show t = case t of 
    TokArrow   -> " -> "
    TokImplies -> " => "
    TokEOL     -> "\n"
    TokComma   -> ", "
    TokUnderscore -> "_"
    TokLParen -> "(" 
    TokRParen -> ")"
    TokColon  -> ":"
    TokForall -> " forall "
    TokName s -> " " ++ s ++ " "
    TokVar  s -> " " ++ s ++ " "

scanTypes :: String -> [PosnToken]
scanTypes = alexScanTokens

}
