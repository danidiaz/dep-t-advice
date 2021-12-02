module Main (main) where

import Test.DocTest

main =
  doctest
    [ "-ilib",
      "lib/Dep/Advice.hs"
    , "lib/Dep/Advice/Basic.hs"
    , "lib/Dep/SimpleAdvice.hs"
    , "lib/Dep/SimpleAdvice/Basic.hs"
    ]
