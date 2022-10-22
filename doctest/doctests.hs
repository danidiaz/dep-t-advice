module Main (main) where

import Test.DocTest
main = doctest ["-ilib", 
    "lib/Control/Monad/Dep/Advice.hs", 
    "lib/Control/Monad/Dep/Advice/Basic.hs",
    "lib/Control/Monad/Dep/SimpleAdvice.hs", 
    "lib/Control/Monad/Dep/SimpleAdvice/Basic.hs",
    "lib/Control/Monad/Dep/ReaderAdvice.hs", 
    "lib/Control/Monad/Dep/ReaderAdvice/Basic.hs"
    ]

