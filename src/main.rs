use std::{env, fs};

struct Problem {
    variables: usize,
    clause: Vec<Vec<i64>>,
}

fn parse_dimacs(text: &str) -> Result<Problem, ()> {
    let mut lines = text.lines();

    let (vnum, cnum) = loop {
        if let Some(l) = lines.next() {
            match l.chars().nth(0).ok_or(())? {
                'c' => continue,
                'p' => {
                    let mut lsp = l.split_whitespace();
                    let _ = lsp.next().ok_or(())?; // consume 'p'
                    let _ = lsp.next().ok_or(())?; // consume 'cnf'
                    let v = lsp.next().ok_or(())?; // consume variables
                    let c = lsp.next().ok_or(())?; // consume clauses
                    break (v.parse().unwrap(), c.parse().unwrap());
                }
                _ => continue,
            }
        } else {
            return Err(());
        }
    };

    let mut cs = vec![];
    for _ in 0..cnum {
        if let Some(l) = lines.next() {
            let mut c = l
                .split_whitespace()
                .map(|s| s.parse().unwrap())
                .collect::<Vec<i64>>();
            if let Some(0) = c.pop() {
                // consume 0
                cs.push(c);
            } else {
                return Err(());
            }
        } else {
            return Err(());
        }
    }

    Ok(Problem {
        variables: vnum,
        clause: cs,
    })
}

type Var = usize;
type Lit = i64;

#[derive(Clone, Copy, Debug, Eq, PartialEq)]
enum Assignment {
    UnDef,
    Def(bool),
}

impl Assignment {
    fn flip(&mut self) {
        match self {
            Assignment::Def(ref mut b) => *b = !*b,
            _ => unreachable!(),
        }
    }
}

#[derive(Debug)]
struct Clause {
    lits: Vec<Lit>, // literals
    pos: usize,     // number of literals assigned T
    neg: usize,     // number of literals assigned F
}

impl Clause {
    fn notice_pos(&mut self, _: Lit, _: &Vec<Assignment>) {
        self.pos += 1;
    }

    fn notice_neg(&mut self, _: Lit, _: &Vec<Assignment>) {
        self.neg += 1;
    }

    fn notice_pos_to_undef(&mut self, _: Lit, _: &Vec<Assignment>) {
        self.pos -= 1;
    }

    fn notice_neg_to_undef(&mut self, _: Lit, _: &Vec<Assignment>) {
        self.neg -= 1;
    }

    fn is_unit(&self, assigns: &Vec<Assignment>) -> Option<Lit> {
        if self.pos == 0 && self.lits.len() - 1 == self.neg {
            self.lits
                .iter()
                .find(|l| assigns[l.abs() as usize] == Assignment::UnDef)
                .cloned()
        } else {
            None
        }
    }

    fn is_conflict(&self, _: &Vec<Assignment>) -> bool {
        self.pos == 0 && self.lits.len() == self.neg
    }
}

#[derive(Debug)]
struct ClauseMap {
    pos_map: Vec<Vec<usize>>,
    neg_map: Vec<Vec<usize>>,
}

impl ClauseMap {
    fn new(n: usize) -> ClauseMap {
        let pos_map = vec![vec![]; n + 1];
        let neg_map = vec![vec![]; n + 1];
        ClauseMap { pos_map, neg_map }
    }

    fn get(&self, l: Lit) -> &Vec<usize> {
        if l > 0 {
            &self.pos_map[l as usize]
        } else {
            &self.neg_map[-l as usize]
        }
    }

    fn insert(&mut self, l: Lit, c: usize) {
        if l > 0 {
            self.pos_map[l as usize].push(c);
        } else {
            self.neg_map[-l as usize].push(c);
        }
    }
}

#[derive(Debug)]
struct Solver {
    assigns: Vec<Assignment>, // assigns of variables
    db: Vec<Clause>,          // clause data base
    clause_map: ClauseMap,    // literal -> clause index
    decision: Vec<Var>,       // decision stack (trail), length is desision level
    deduced: Vec<Var>,        // deduced literal trail (0 is for decision)
}

impl Solver {
    fn new(p: Problem) -> Solver {
        // preprocess
        let db = p
            .clause
            .into_iter()
            .map(|x| Clause {
                lits: x,
                pos: 0,
                neg: 0,
            })
            .collect::<Vec<_>>();

        let mut clause_map = ClauseMap::new(p.variables);
        for (idx, c) in db.iter().enumerate() {
            for &l in &c.lits {
                clause_map.insert(l, idx);
            }
        }

        Solver {
            assigns: vec![Assignment::UnDef; p.variables + 1],
            db,
            clause_map,
            decision: Vec::with_capacity(p.variables),
            deduced: Vec::with_capacity(p.variables),
        }
    }

    fn run(&mut self) -> bool {
        loop {
            while let Some(_conflict) = self.bcp() {
                // DPLL
                while let Some(x) = self.deduced.pop() {
                    if x == 0 {
                        break;
                    }
                    self.cancel_clause(x);
                    self.assigns[x] = Assignment::UnDef;
                }
                if let Some(x) = self.decision.pop() {
                    self.cancel_clause(x);
                    self.assigns[x].flip();
                    self.update_clause(x);
                    self.deduced.push(x);
                } else {
                    return false; // UNSAT
                }
            }

            if let Some((x, v)) = self.decide() {
                self.assigns[x] = Assignment::Def(v);
                self.update_clause(x); // x,-xを含んだ節の情報を更新する
                self.deduced.push(0); // push dummy (decision)
                self.decision.push(x);
            } else {
                return true; // SAT
            }
        }
    }

    // return selected var & assignment value
    fn decide(&mut self) -> Option<(Var, bool)> {
        for (x, v) in self.assigns.iter().enumerate() {
            if v == &Assignment::UnDef {
                return Some((x, true));
            }
        }
        None
    }

    // return conflicting clause index
    fn bcp(&mut self) -> Option<usize> {
        loop {
            let last_len = self.deduced.len();
            for idx in 0..self.db.len() {
                let c = &self.db[idx];
                if c.is_conflict(&self.assigns) {
                    return Some(idx);
                }
                if let Some(l) = c.is_unit(&self.assigns) {
                    let x = l.abs() as Var;
                    self.assigns[x] = Assignment::Def(l > 0);
                    self.update_clause(x);
                    self.deduced.push(x);
                }
            }
            if last_len == self.deduced.len() {
                return None;
            }
        }
    }

    // update counter/watch list with clause containing x
    fn update_clause(&mut self, x: Var) {
        if let Assignment::Def(v) = self.assigns[x] {
            let l = if v { x as Lit } else { -(x as Lit) };
            for &idx in self.clause_map.get(l) {
                self.db[idx].notice_pos(l, &self.assigns);
            }
            for &idx in self.clause_map.get(-l) {
                self.db[idx].notice_neg(-l, &self.assigns);
            }
        }
    }

    // cancel counter/watch list with clause containing x
    fn cancel_clause(&mut self, x: Var) {
        if let Assignment::Def(v) = self.assigns[x] {
            let l = if v { x as Lit } else { -(x as Lit) };
            for &idx in self.clause_map.get(l) {
                self.db[idx].notice_pos_to_undef(l, &self.assigns);
            }
            for &idx in self.clause_map.get(-l) {
                self.db[idx].notice_neg_to_undef(-l, &self.assigns);
            }
        }
    }
}

fn bench1000(sat: bool, num: i32) {
    use std::fs::File;
    for i in 1..=1000 {
        let path = format!(
            "./bench/{0}{1}/{0}{1}-0{2}.cnf",
            if sat { "uf" } else { "uuf" },
            num,
            i
        );
        println!("solving... {}", path);
        assert_eq!(solve(&path), sat, "wrong answer at {}.", i);
    }
}

#[test]
fn test_uf50() {
    bench1000(true, 50);
}

#[test]
fn test_uuf50() {
    bench1000(false, 50);
}

#[test]
fn test_uf100() {
    bench1000(true, 100);
}

#[test]
fn test_uuf100() {
    bench1000(false, 100);
}

fn solve(file_name: &str) -> bool {
    let dimacs_text = fs::read_to_string(file_name).unwrap();
    let problem = parse_dimacs(&dimacs_text).unwrap();
    let mut solver = Solver::new(problem);
    solver.run()
}

fn main() {
    let args = env::args().collect::<Vec<_>>();
    let file_name = &args[1];
    let dimacs_text = fs::read_to_string(file_name).unwrap();
    let problem = parse_dimacs(&dimacs_text).unwrap();
    let mut solver = Solver::new(problem);
    let result = if solver.run() { "SAT" } else { "UNSAT" };
    println!("{}", result)
}
