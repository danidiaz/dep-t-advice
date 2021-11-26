# Revision history for dep-t-advice


## 0.6.0.0 

* SyntheticCallStackException renamed to SyntheticStackTraceException.
  SyntheticStackTraceException now contains NonEmpty stack traces. 

  Also, for each frame, the full path in the environment to the component is
  provided. This is helpful for Dep.Tagged components.
  
  [Issue #18](https://github.com/danidiaz/dep-t-advice/issues/18).

* `Dep.Advice.component` can now treat components with nested records.

## 0.5.1.0 

* `Control.Monad.whatever` renamed to `whatever`. 

  The old modules still remain, but deprecated.

* Added `fromSimple_`.

* Added `injectFailures` and `keepCallStack`.

## 0.5.0.0 

* The Advice type has changed to get rid of the existential type.
  This breaks the 'makeAdvice' function.   
* Added 'Control.Monad.Dep.SimpleAdvice' and 'Control.Monad.Dep.SimpleAdvice.Basic'.
* Moved some "basic" advices.
* Removed distributeDepT.
* 'adviseRecord' now receives a 'NonEmpty' path-in-record, ordered innermost-first.
* More flexible type for doLocally.

## 0.4.7.0 

* Added 'distributeDepT' and 'component'.

## 0.4.6.1 

* Modified a signature to make it compile with GHC 9.0.1.

## 0.4.6.0 

* `adviseRecord` and `deceiveRecord` now work with records having fields wrapped in `Identity`.

  This is for better compatibility with the [barbies](http://hackage.haskell.org/package/barbies) package.

## 0.4.5.0 

* Added runFromDep.

  This required bumping the minimum version of dep-t to 0.4.4.0.

## 0.4.4.0 

* Added 'adviseRecord' and 'deceiveRecord' that manipulate entire
  records-of-functions (also work on newtypes) instead of a single bare
  function. 

  Useful when the components to put on the environment come in their own record
  types.

## 0.4.0.0 

* Added 'deceive' function.

* BREAKING CHANGE. The form of the 'HasX' constraints expected by 'Ensure' has
  changed. Now they expect the effect monad as their first parameter. This is
  in order to help with deriving.

## 0.3.0.0 

* BREAKING CHANGE. Removed the dependency on "constraints" to reduce the
  dependency footprint. This changes the signature of restrictArgs.

## 0.2.0.0 

* BREAKING CHANGE. The Advice type is no longer parameterized by the `cem` and
  `cr` constraints. Instead, it's directly parameterized by the types `e` of
  the environment, `m` of the base monad and `r` of the result, which are left
  polymorphic when needed. This simplifies a bunch of things. The `ca`
  constraint paramter remains however.

## 0.1.0.0 -- YYYY-mm-dd

* First version. Released on an unsuspecting world.
