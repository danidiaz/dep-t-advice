module Main (main) where

import Test.DocTest

main =
  doctest
    [ "-ilib",
      "lib/Dep/Advice.hs"
    , "lib/Dep/Advice/Basic.hs"
    , "lib/Dep/SimpleAdvice.hs"
    , "lib/Dep/SimpleAdvice/Basic.hs"
    , "lib/Dep/ReaderAdvice.hs"
    , "lib/Dep/ReaderAdvice/Basic.hs"
    , "lib/Dep/IOAdvice.hs"
    , "lib/Dep/IOAdvice/Basic.hs"
    ]
