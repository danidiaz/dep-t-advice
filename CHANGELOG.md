# Revision history for dep-t-advice

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
