# dep-t-advice

This package is a companion to
[dep-t](http://hackage.haskell.org/package/dep-t). It provides a mechanism for
handling cross-cutting concerns in your application by adding "advices" to the
functions in your record-of-functions, in a way that is composable and
independent of each function's particular number of arguments.

## Rationale

So, you have decided to structure your program in a record-of-functions style,
using [dep-t](http://hackage.haskell.org/package/dep-t). Good choice!

You have already selected your functions, decided which base monad use for
`DepT`, and now you are ready to construct the environment record, which serves
as your [composition
root](https://stackoverflow.com/questions/6277771/what-is-a-composition-root-in-the-context-of-dependency-injection).

Now seems like a good moment to handle some of those pesky ["croscutting
concerns"](https://en.wikipedia.org/wiki/Cross-cutting_concern), don't you
think?

Stuff like:

- Logging
- Caching
- Monitoring
- Validation
- Setting up transaction boundaries.
- Setting up exception handlers for uncaught exceptions.

But how will you go about it?

### A perfectly simple and reasonable solution

Imagine that you want to make this function print its argument to stdout:

    foo :: Int -> DepT e IO () 

Easy enough:

    foo' :: Int -> DepT e IO ()
    foo' arg1 = do
        liftIO $ putStrLn (show arg1)
        foo arg1

You can even write your own general "printArgs" combinator:

    printArgs :: Show a => (a -> DepT e IO ()) -> (a -> DepT e IO ())
    printArgs f arg1 = do
        liftIO $ putStrLn (show arg1)
        f arg1

You could wrap `foo` in `printArgs` when constructing the record-of-functions,
or perhaps you could modify the corresponding field after the record had been
constructed.

This solution works, and is easy to understand. There's an annoyance though:
you need a different version of `printArgs` for each number of arguments a
function might have.

And if you want to compose different combinators (say, `printArgs` and
`printResult`) before applying them to functions, you need a composition
combinator specific for each number of arguments.

### The solution using "advices"

The `Advice` datatype provided by this package encapsulates a transformation on
`DepT`-effectful functions, *in a way that is polymorphic over the number of
arguments*. The same advice will work for functions with `0`, `1` or `N`
arguments.

Advice values are parameterized by the constraints they require of the function:

- The function arguments. "All the arguments must be showable".
- The `DepT` environment and the base monad. "The environment must have a
  logger, and the base monad must have a `MonadIO` instance."
- The function return type. "The function must return a type that is a
  `Monoid`."

Here's how a `printArgs` advice might be defined:

    printArgs :: forall cr. Handle -> String -> Advice Show (BaseConstraint MonadIO) cr
    printArgs h prefix =
      makeArgsAdvice
        ( \args -> do
            liftIO $ hPutStr h $ prefix ++ ":"
            hctraverse_ (Proxy @Show) (\(I a) -> liftIO (hPutStr h (" " ++ show a))) args
            liftIO $ hPutStrLn h "\n"
            liftIO $ hFlush h
            pure args
        )

The advice receives the arguments of the function in the form of an [n-ary
product](http://hackage.haskell.org/package/sop-core-0.5.0.1/docs/Data-SOP-NP.html#t:NP)
from [sop-core](http://hackage.haskell.org/package/sop-core-0.5.0.1). But it
must be polymorphic on the shape of the type-level list which indexes the
product. This makes the advice work for any number of parameters.

The advice would be applied like this:

    advise (printArgs @Top stdout "foo args: ") foo

The `@Top` type application is necessary because `printArgs` is polymorphic on
the `cr` constraint on the function results, and the `advise` function requires
all the constraints to be "concrete" in order to apply the advice. 

## Links

- [Aspect Oriented Programming with
  Spring](https://docs.spring.io/spring-framework/docs/current/reference/html/core.html#aop)
  and [Spring AOP
  APIs](https://docs.spring.io/spring-framework/docs/current/reference/html/core.html#aop-api).

- [Using the “constraints” package to make a wrapped function less
  polymorphic](https://stackoverflow.com/questions/65800809/using-the-constraints-package-to-make-a-wrapped-function-less-polymorphic)


