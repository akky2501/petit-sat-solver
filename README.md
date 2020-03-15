Petit SAT Solver
====

a tiny sat solver

## Usage

```bash
$ cargo run --release bench/uf100/uf100-01.cnf
```

## Status

- [x] Parse DIMACS format text
- [x] DPLL
- [x] 2 Watch Literal
- [x] CDCL (linear-time first uip calculation)
- [ ] Learnt Clause Elimination
- [ ] VSIDS
- [ ] restarting
- [ ] Learnt Clause Minimization


## Author

[akky2501](https://github.com/akky2501)