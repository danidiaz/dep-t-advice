module Main (main) where

import Test.DocTest
main = doctest ["-ilib", "lib/Control/Monad/Dep/Advice.hs"]

