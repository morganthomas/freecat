import FreeCat.Core (FreeCat, runFreeCat, digestContext, digestExpr, evaluate)
import FreeCat.Parser (lexAndParseContext, lexAndParseExpr)
import System.Environment (getArgs)
import Text.Parsec (ParseError)

main :: IO ()
main = do
  args <- getArgs
  case args of
    [contextFilename, expr] -> do
      contextSource <- readFile contextFilename
      rawContext <- runParse $ lexAndParseContext contextSource
      rawExpr <- runParse $ lexAndParseExpr expr
      result <- runFreeCat (do
          context <- digestContext rawContext
          (expr, exprType) <- digestExpr context rawExpr
          evaluate context expr
        )
      case result of
        Left err -> error (show err)
        Right (result, st) -> putStrLn (show result)
    _ -> error "wrong number of command line args, expected 2"

runParse :: Either ParseError a -> IO a
runParse (Left e) = error (show e)
runParse (Right x) = return x
