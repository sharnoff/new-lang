## A short list of syntax ideas, kept for further thought

```
use foo.{bar, baz}.qux.{foo, bar};
// equivalent to
use foo.bar.qux.{foo, bar};
use foo.baz.qux.{foo, bar};
```

```
// As a module:
mod Foo {
    type Self {
        field_1: (),
        // ...
    }

    fn bar(&self) -> int { ... }
}
```

```
mod foo {
    impl MyTrait for Self {
        ...
    }
}

// or:

impl MyTrait for mod foo {
    ...
}
```

```
impl Foo with Vec<Bar> as ctx {
    fn foo() {
        ctx.foo()
    }
}

...

with my_vec as Foo.ctx {
    Foo.foo()
}
```

```
where:
    forall S. T<S> :: Display,
impl Foo<T> {
    ...
}

// vs.

impl Foo<T>
where:
    forall S. T<S> :: Display,
{
    ...
}
```

```
trait Foo {
    fn foo(&self) -> i32;
}

impl Foo for Bar {
    fn foo = |this| this.baz.into();
}

// vs:

impl Foo for Bar {
    fn foo = self.baz.into();
}

// vs:

impl Foo for Bar {
    fn foo(&self) = self.baz.into();
    fn foo(&self) => self.baz.into();
}
```
