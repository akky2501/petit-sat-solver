extern crate fxhash;
use fxhash::FxHashSet;
use std::ops::Index;
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

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum AssignmentCell {
    UnDef,
    Def(bool),
}

#[derive(Debug)]
struct Assignment {
    base: Lit,
    values: Vec<AssignmentCell>,
}

impl Assignment {
    fn new(n: usize) -> Self {
        Assignment {
            base: n as Lit,
            values: vec![AssignmentCell::UnDef; 2 * n + 1],
        }
    }

    #[inline]
    fn count(&self) -> usize {
        self.base as usize
    }

    #[inline]
    fn idx(&self, l: Lit) -> Var {
        (self.base + l) as Var
    }

    #[inline]
    fn set_pos(&mut self, l: Lit) {
        let p = self.idx(l);
        let n = self.idx(-l);
        self.values[p] = AssignmentCell::Def(true);
        self.values[n] = AssignmentCell::Def(false);
    }

    #[inline]
    fn flip(&mut self, l: Lit) {
        let p = self.idx(l);
        let n = self.idx(-l);
        self.values.swap(p, n);
    }

    #[inline]
    fn set_undef(&mut self, l: Lit) {
        let p = self.idx(l);
        let n = self.idx(-l);
        self.values[p] = AssignmentCell::UnDef;
        self.values[n] = AssignmentCell::UnDef;
    }

    #[inline]
    fn value(&self, l: Lit) -> bool {
        match self.values[self.idx(l)] {
            AssignmentCell::Def(b) => b,
            _ => unreachable!(),
        }
    }

    #[inline]
    fn is_def(&self, l: Lit) -> bool {
        match self.values[self.idx(l)] {
            AssignmentCell::Def(_) => true,
            _ => false,
        }
    }

    #[inline]
    fn is_undef(&self, l: Lit) -> bool {
        !self.is_def(l)
    }
}

impl Index<Lit> for Assignment {
    type Output = AssignmentCell;

    #[inline]
    fn index(&self, l: Lit) -> &AssignmentCell {
        let l = self.idx(l);
        &self.values[l]
    }
}

#[derive(Debug)]
struct Clause {
    lits: Vec<Lit>, // literals ([0], [1] are watched literals)
}

impl Clause {
    fn notice_neg(&mut self, lit: Lit, assigns: &Assignment) -> Lit {
        if self.lits[1] == lit {
            self.lits.swap(0, 1);
        }
        let mut new_wl = 0;
        for i in 2..self.lits.len() {
            match assigns[self.lits[i]] {
                AssignmentCell::Def(false) => (),
                _ => {
                    new_wl = i;
                    break;
                }
            }
        }
        self.lits.swap(0, new_wl);
        self.lits[0] // return new watched literal
    }

    fn is_unit(&self, assigns: &Assignment) -> Option<Lit> {
        use AssignmentCell::*;
        let l1 = self.lits[0];
        let l2 = self.lits[1];
        match (assigns[l1], assigns[l2]) {
            (Def(false), UnDef) => Some(l2),
            (UnDef, Def(false)) => Some(l1),
            _ => None,
        }
    }

    fn is_conflict(&self, assigns: &Assignment) -> bool {
        use AssignmentCell::*;
        let l1 = self.lits[0];
        let l2 = self.lits[1];
        match (assigns[l1], assigns[l2]) {
            (Def(false), Def(false)) => true,
            _ => false,
        }
    }
}

#[derive(Debug)]
struct ClauseMap {
    base: Lit,
    map: Vec<FxHashSet<usize>>,
}

impl ClauseMap {
    fn new(n: usize) -> ClauseMap {
        let map = vec![FxHashSet::default(); 2 * n + 1];
        ClauseMap {
            base: n as Lit,
            map,
        }
    }

    #[inline]
    fn idx(&self, l: Lit) -> Var {
        (self.base + l) as Var
    }

    fn get(&self, l: Lit) -> &FxHashSet<usize> {
        let l = self.idx(l);
        &self.map[l]
    }

    fn insert(&mut self, l: Lit, c: usize) {
        let l = self.idx(l);
        self.map[l as usize].insert(c);
    }

    fn delete(&mut self, l: Lit, c: usize) {
        let l = self.idx(l);
        self.map[l].remove(&c);
    }
}

#[derive(Debug)]
struct Solver {
    assigns: Assignment,   // assigns of variables
    db: Vec<Clause>,       // clause data base
    clause_map: ClauseMap, // literal -> clause index
    decision: Vec<Var>,    // decision stack (trail), length is desision level
    deduced: Vec<Var>,     // deduced literal trail (0 is for decision)

    delete_list: Vec<usize>,
    insert_list: Vec<i64>,
}

impl Solver {
    fn new(p: Problem) -> Solver {
        // preprocess
        let db = p
            .clause
            .into_iter()
            .map(|x| Clause { lits: x })
            .collect::<Vec<_>>();

        let mut clause_map = ClauseMap::new(p.variables);
        for (idx, c) in db.iter().enumerate() {
            clause_map.insert(c.lits[0], idx); // watch literal/clause
            clause_map.insert(c.lits[1], idx);
        }

        let clen = db.len();
        Solver {
            assigns: Assignment::new(p.variables),
            db,
            clause_map,
            decision: Vec::with_capacity(p.variables),
            deduced: Vec::with_capacity(p.variables),

            delete_list: Vec::with_capacity(clen),
            insert_list: Vec::with_capacity(clen),
        }
    }

    fn run(&mut self) -> bool {
        loop {
            while let Some(_conflict) = self.bcp() {
                if !self.resolve_conflict_dpll() {
                    return false;
                }
            }

            if let Some((x, v)) = self.decide() {
                let l = if v { x as Lit } else { -(x as Lit) };
                self.assigns.set_pos(l);
                self.update_clause(x);
                self.deduced.push(0); // push dummy (decision)
                self.decision.push(x);
            } else {
                return true; // SAT
            }
        }
    }

    fn resolve_conflict_dpll(&mut self) -> bool {
        while let Some(x) = self.deduced.pop() {
            if x == 0 {
                break;
            }
            self.cancel_clause(x);
            self.assigns.set_undef(x as Lit);
        }
        if let Some(x) = self.decision.pop() {
            self.cancel_clause(x);
            self.assigns.flip(x as Lit);
            self.update_clause(x);
            self.deduced.push(x);
        } else {
            return false; // UNSAT
        }
        true
    }

    // return selected var & assignment value
    fn decide(&mut self) -> Option<(Var, bool)> {
        for i in 1..=self.assigns.count() {
            if self.assigns.is_undef(i as Lit) {
                return Some((i, true));
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
                    self.assigns.set_pos(l);
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
        let l = x as Lit;
        if self.assigns.is_def(l) {
            let neglit = if self.assigns.value(l) { -l } else { l };
            self.delete_list.clear();
            self.insert_list.clear();
            for &idx in self.clause_map.get(neglit) {
                let new_wl = self.db[idx].notice_neg(neglit, &self.assigns);
                if new_wl != neglit {
                    self.delete_list.push(idx); // unwatch clause
                    self.insert_list.push(new_wl); // watch new clause
                }
            }
            for (&idx, &new_wl) in self.delete_list.iter().zip(self.insert_list.iter()) {
                self.clause_map.delete(neglit, idx);
                self.clause_map.insert(new_wl, idx);
            }
        }
    }

    // cancel counter/watch list with clause containing x
    fn cancel_clause(&mut self, _x: Var) {
        // do nothing
    }
}

fn bench1000(sat: bool, num: i32) {
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
fn test_uf20() {
    bench1000(true, 20);
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

#[test]
fn test_true() {
    let problem = Problem {
        variables: 4,
        clause: vec![vec![1, 2], vec![-1, -2], vec![3, 4], vec![-3, 4]],
    };
    assert_eq!(Solver::new(problem).run(), true);
}

#[test]
fn test2() {
    let problem = Problem {
        variables: 2,
        clause: vec![vec![1, 2], vec![1, -2], vec![-1, -2]],
    };
    assert_eq!(Solver::new(problem).run(), true);
}

#[test]
fn test3() {
    let problem = Problem {
        variables: 2,
        clause: vec![vec![1, 2], vec![-1, 2], vec![1, -2], vec![-1, -2]],
    };
    assert_eq!(Solver::new(problem).run(), false);
}
#[test]
fn test4() {
    let problem = Problem {
        variables: 6,
        clause: vec![
            vec![4, 5],
            vec![-4, -5],
            vec![1, 6],
            vec![-1, -6],
            vec![-2, -3],
        ],
    };
    assert_eq!(Solver::new(problem).run(), true);
}
#[test]
fn test5() {
    let problem = Problem {
        variables: 9,
        clause: vec![vec![1, 6, 5, 4, 3, 9, 2]],
    };
    assert_eq!(Solver::new(problem).run(), true);
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
