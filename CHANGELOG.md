# Revision history for dep-t-advice

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
