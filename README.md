# Bupropion

Fancy diagnostics for [Miette](https://crates.io/crates/miette):

```rust
fn main() {
  bupropion::BupropionHandlerOpts::install(|| {
        // Build the bupropion handler options, for specific
        // error presenting.
        bupropion::BupropionHandlerOpts::new()
    })
    .into_diagnostic()?;
}
```

The image for an error can be:

![image](https://github.com/aripiprazole/bupropion/assets/51281661/11d1248c-cc96-4128-be37-4035c9147e5a)
