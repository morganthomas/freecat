import FreeCat.Core (FreeCat, runFreeCat)
import FreeCat.Digest (digestContext, digestExpr)
import FreeCat.Evaluate (evaluate)
import FreeCat.Parser (runParse, lexAndParseContext, lexAndParseExpr)
import System.Environment (getArgs)

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
          result <- evaluate context expr
          return (context, result)
        )
      case result of
        Left err -> error (show err)
        Right ((context, result), st) -> do
          putStrLn ("context:\n" ++ show context)
          putStrLn ("final result: " ++ show result)
    _ -> error "wrong number of command line args, expected 2"
