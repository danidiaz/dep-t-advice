# dep-t-advice

This package is a companion to
[dep-t](http://hackage.haskell.org/package/dep-t). It provides a mechanism for
handling cross-cutting concerns in your application by adding "advices" to the
functions in your record-of-functions, in a way that is composable and
independent of each function's particular number of arguments.

[![dep-t-advice.png](https://i.postimg.cc/L8Cm279S/dep-t-advice.png)](https://postimg.cc/tsxKzBnv)

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

    foo :: Int -> DepT e_ IO () 

Easy enough:

    foo' :: Int -> DepT e_ IO ()
    foo' arg1 = do
        liftIO $ putStrLn (show arg1)
        foo arg1

You can even write your own general "printArgs" combinator:

    printArgs :: Show a => (a -> DepT e_ IO ()) -> (a -> DepT e_ IO ())
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

Advices can't change the type of a function, but they might:

- Analyze and change the values of the function's arguments.

- Add additional effects to the function, either effects from the base monad, or effects from handlers found in the environment.

- Change the result value of the function.

- Sidestep the execution of the function altogether, providing al alternative result.

Here's how a `printArgs` advice might be defined:

    printArgs :: forall e_ m r. MonadIO m => Handle -> String -> Advice Show e_ m r
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

    advise (printArgs stdout "foo args: ") foo

## Advices should be applied at the composition root

It's worth emphasizing that advices should be applied at the ["composition
root"](https://stackoverflow.com/questions/6277771/what-is-a-composition-root-in-the-context-of-dependency-injection),
the place in our application in which all the disparate functions are assembled
and we commit to a concrete monad, namely `DepT`.

Before being brought into the composition root, the functions need not be aware
that `DepT` exists. They might be working in some generic `MonadReader`
environment, plus some constraints on that environment.

Once we decide to use `DepT`, we can apply the advice, because advice only
works on functions that end on a `DepT` action. Also, advice might depend on
the full gamut of functionality stored in the environment.

## What about  `Dep.ReaderAdvice` and `Dep.IOAdvice`?

`Advice`s from `Dep.Advice` require us to work with `DepT`, but `DepT` is kind
of weird. Instead, we may might to use more common monads for our effects, like
`ReaderT` o plain old `IO`.

That's why `Dep.ReaderAdvice` and `Dep.IOAdvice` exist: they provide alternative
versions of the `Advice` type which work with those monads.

Ain't that a lot of code duplication? Why not have a single `Advice` type which
works with all monads? That leads us to...

## What about `Dep.SimpleAdvice`?

`Dep.SimpleAdvice` provides a version of the `Advice` type that can be used with
different concrete monads like `ReaderT` or `IO`.

See [this
thread](https://discourse.haskell.org/t/decorate-your-records-of-functions-with-this-weird-trick/3675)
in the Haskell Discourse for more info.

There's a catch, however. `Dep.SimpleAdvice` depends on the `coerce` mechanism
of Haskell, and it can sometimes be finicky, for example when some required
constructor hasn't been imported, or when there are polymorphic functions
involved.

That's the reason `Dep.ReaderAdvice` and `Dep.IOAdvice` are still necessary. For
their particular monads, they work in more cases.

## Historical aside

According to Wikipedia, the term "advice" in the sense of aspect-oriented
programming goes back to 1966. Quoting from [PILOT: A Step Toward Man-Computer
Symbiosis](http://publications.csail.mit.edu/ai/browse/0200browse.shtml):

> There are two ways a user can modify programs in this subjective model of
> programming: he can modify the interface between procedures, or he can modify
> the procedure itself. (Since procedures are themselves made up of procedures,
> modifying a procedure at one level may correspond to modifying the interface
> between procedures at a lower level.) Modifying the interface between
> procedures is called advising. Modifying a procedure itself is editing.

> Advising is the basic innovation in the model, and in the PILOT system.
> Advising consists of inserting new procedures at any or all of the entry or
> exit points to a particular procedure (or class of procedures). The
> procedures inserted are called "advice procedures" or simply "advice".

> Since each piece of advice is itself a procedure, it has its own entries and
> exits. In particular, this means that the execution of advice can cause the
> procedure that it modifies to be bypassed completely, e.g., by specifying as
> an exit from the advice one of the exits from the original procedure; or the
> advice may change essential variables and continue with the computation so
> that the original procedure is executed, but with modified variables.
> Finally, the advice may not alter the execution or affect the original
> procedure at all, e.g., it may merely perform some additional computation
> such as printing a message or recording history. Since advice can be
> conditional, the decision as to what is to be done can depend on the results
> of the computation up to that point.

> The principal advantage of advising is that the user need not be concerned
> about the details of the actual changes in his program, nor the internal
> representation of advice. He can treat the procedure to be advised *as a
> unit*, a single block, and make changes to it without concern for the
> particulars of this block. This may be contrasted with editing in which the
> programmer must be cognizant of the internal structure of the procedure.

[tweet](https://twitter.com/DiazCarrete/status/1446783366678949891).

## Links

- [Aspect Oriented Programming with
  Spring](https://docs.spring.io/spring-framework/docs/current/reference/html/core.html#aop)
  and [Spring AOP
  APIs](https://docs.spring.io/spring-framework/docs/current/reference/html/core.html#aop-api).

- [Using the “constraints” package to make a wrapped function less
  polymorphic](https://stackoverflow.com/questions/65800809/using-the-constraints-package-to-make-a-wrapped-function-less-polymorphic)

- [variadic-function](https://hackage.haskell.org/package/variadic-function) a
  Hackage library which also deals with functions of any number of elements.
  [Reddit
  thread](https://www.reddit.com/r/haskell/comments/oeyaz2/ann_typeablemock_mocks_that_can_fit_into_any/).

- [Inferring the arity of zipWith, with lots of type-level hackery](https://www.youtube.com/watch?v=iGSKqcebhfs&t=957s). YouTube video.

- [Functional Pearl: The Decorator Pattern in Haskell](https://twitter.com/DiazCarrete/status/1403985337513394178)

  > An arity-generic decorator needs to solve two problems: intercept recursive calls and handle functions of any arity uniformly

