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
- Setting up transaction boundaries.
- Setting up exception handlers.

But how will you go about it?

### The perfectly reasonable and simple solution

### The solution using "advices"

## Links

- [Aspect Oriented Programming with
  Spring](https://docs.spring.io/spring-framework/docs/current/reference/html/core.html#aop)
  and [Spring AOP
  APIs](https://docs.spring.io/spring-framework/docs/current/reference/html/core.html#aop-api).

- [Using the “constraints” package to make a wrapped function less polymorphic](https://stackoverflow.com/questions/65800809/using-the-constraints-package-to-make-a-wrapped-function-less-polymorphic)


