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
    values: Vec<AssignmentCell>,
}

impl Assignment {
    fn new(n: usize) -> Self {
        Assignment {
            values: vec![AssignmentCell::UnDef; n + 1],
        }
    }

    #[inline]
    fn count(&self) -> usize {
        self.values.len() - 1
    }

    #[inline]
    fn def_idx(&self, l: Lit) -> Var {
        l.abs() as Var
    }

    #[inline]
    fn set_pos(&mut self, l: Lit) {
        let x = self.def_idx(l);
        self.values[x] = AssignmentCell::Def(l > 0);
    }

    #[inline]
    fn flip(&mut self, l: Lit) {
        let x = self.def_idx(l);
        if let AssignmentCell::Def(ref mut b) = self.values[x] {
            *b = !*b;
        }
    }

    #[inline]
    fn set_undef(&mut self, l: Lit) {
        let x = self.def_idx(l);
        self.values[x] = AssignmentCell::UnDef;
    }

    #[inline]
    fn value(&self, l: Lit) -> bool {
        let x = self.def_idx(l);
        match self.values[x] {
            AssignmentCell::Def(b) => {
                if l > 0 {
                    b
                } else {
                    !b
                }
            }
            _ => unreachable!(),
        }
    }

    #[inline]
    fn is_def(&self, l: Lit) -> bool {
        let x = self.def_idx(l);
        self.values[x] != AssignmentCell::UnDef
    }

    #[inline]
    fn is_undef(&self, l: Lit) -> bool {
        !self.is_def(l)
    }
}

#[derive(Debug)]
struct Clause {
    lits: Vec<Lit>, // literals
    wl: [usize; 2], // watched literal index
}

impl Clause {
    fn notice_neg(&mut self, lit: Lit, assigns: &Assignment) {
        // TODO: unwatch clause
        for i in 0..2 {
            let n = self.lits.len();
            let wl1 = self.wl[(i + 1) % 2];
            let wl0 = &mut self.wl[i];
            if lit == self.lits[*wl0] {
                let mut new_wl = (*wl0 + 1) % n;
                while new_wl != *wl0 {
                    if new_wl != wl1
                        && (assigns.is_undef(self.lits[new_wl]) || assigns.value(self.lits[new_wl]))
                    {
                        *wl0 = new_wl;
                        break;
                    }
                    new_wl = (new_wl + 1) % n;
                }
                break;
            }
        }
    }

    fn is_unit(&self, assigns: &Assignment) -> Option<Lit> {
        let l1 = self.lits[self.wl[0]];
        let l2 = self.lits[self.wl[1]];
        let d1 = assigns.is_def(l1);
        let d2 = assigns.is_def(l2);
        match (d1, d2) {
            (true, false) if assigns.value(l1) == false => Some(l2),
            (false, true) if assigns.value(l2) == false => Some(l1),
            _ => None,
        }
    }

    fn is_conflict(&self, assigns: &Assignment) -> bool {
        let l1 = self.lits[self.wl[0]];
        let l2 = self.lits[self.wl[1]];
        assigns.is_def(l1)
            && assigns.is_def(l2)
            && assigns.value(l1) == false
            && assigns.value(l2) == false
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
    assigns: Assignment,   // assigns of variables
    db: Vec<Clause>,       // clause data base
    clause_map: ClauseMap, // literal -> clause index
    decision: Vec<Var>,    // decision stack (trail), length is desision level
    deduced: Vec<Var>,     // deduced literal trail (0 is for decision)
}

impl Solver {
    fn new(p: Problem) -> Solver {
        // preprocess
        let db = p
            .clause
            .into_iter()
            .map(|x| Clause {
                lits: x,
                wl: [0, 1],
            })
            .collect::<Vec<_>>();

        let mut clause_map = ClauseMap::new(p.variables);
        for (idx, c) in db.iter().enumerate() {
            for &l in &c.lits {
                clause_map.insert(l, idx);
            }
        }

        Solver {
            assigns: Assignment::new(p.variables),
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
            }

            if let Some((x, v)) = self.decide() {
                let l = if v { x as Lit } else { -(x as Lit) };
                self.assigns.set_pos(l);
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
            for &idx in self.clause_map.get(neglit) {
                self.db[idx].notice_neg(neglit, &self.assigns);
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
