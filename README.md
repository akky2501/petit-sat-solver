Petit SAT Solver
====

a tiny sat solver

## Usage

```bash
$ cargo run --release bench/uf100/uf100-01.cnf
```

## Status

- [x] parse DIMACS format text
- [x] DPLL
- [x] 2 Watch Literal
- [x] CDCL (linear-time first uip calculation)
- [ ] learnt clause elimination
- [ ] learnt clause minimization
- [x] VSIDS
- [ ] phase caching
- [ ] restarting


## Author

[akky2501](https://github.com/akky2501)