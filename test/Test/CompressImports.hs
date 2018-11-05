module Test.CompressImports where

import System.FilePath (isValid)
import System.FilePath.Posix (isAbsolute)
import System.Environment (setEnv)
import System.Environment.Blank (getEnvDefault, getArgs)

foo :: FilePath -> Bool
foo x = isValid x && isAbsolute x

bar :: IO ()
bar = do
  xs <- getArgs
  if not (null xs)
    then do
      x <- getEnvDefault "foo" (head xs)
      setEnv "bar" x
    else pure ()
