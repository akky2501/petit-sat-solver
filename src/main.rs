use std::collections::VecDeque;
use std::fmt;
use std::ops::{Index, IndexMut};
use std::{env, fs};

type Var = u32;
type Lit = i32;

struct Problem {
    variables: usize,
    clause: Vec<Vec<Lit>>,
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

    let mut clause = vec![];
    for _ in 0..cnum {
        if let Some(l) = lines.next() {
            let mut c = l
                .split_whitespace()
                .map(|s| s.parse().unwrap())
                .collect::<Vec<Lit>>();
            if let Some(0) = c.pop() {
                // consume 0
                clause.push(c);
            } else {
                return Err(());
            }
        } else {
            return Err(());
        }
    }

    Ok(Problem {
        variables: vnum,
        clause,
    })
}

struct LitArray<T> {
    base: Lit,
    values: Vec<T>,
}

impl<T: Default + Clone> LitArray<T> {
    fn new(n: usize) -> Self {
        LitArray {
            base: n as Lit,
            values: vec![T::default(); 2 * n + 1],
        }
    }
}

impl<T> LitArray<T> {
    #[inline]
    fn idx(&self, l: Lit) -> usize {
        (self.base + l) as usize
    }
}

impl<T> Index<Lit> for LitArray<T> {
    type Output = T;

    #[inline]
    fn index(&self, l: Lit) -> &Self::Output {
        let l = self.idx(l);
        &self.values[l]
    }
}

impl<T> IndexMut<Lit> for LitArray<T> {
    #[inline]
    fn index_mut(&mut self, l: Lit) -> &mut Self::Output {
        let l = self.idx(l);
        &mut self.values[l]
    }
}

impl<T: fmt::Debug> fmt::Debug for LitArray<T> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("LitArray")
            .field("base", &self.base)
            .field("values", &self.values)
            .finish()
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum AssignmentCell {
    UnDef,
    Def(bool),
}

impl AssignmentCell {
    fn is_undef(&self) -> bool {
        match self {
            AssignmentCell::UnDef => true,
            _ => false,
        }
    }
}

impl Default for AssignmentCell {
    fn default() -> Self {
        AssignmentCell::UnDef
    }
}

#[derive(Debug)]
struct Assignment {
    n: usize,
    values: LitArray<AssignmentCell>,
}

impl Assignment {
    fn new(n: usize) -> Self {
        Assignment {
            n,
            values: LitArray::new(n),
        }
    }

    #[inline]
    fn count(&self) -> usize {
        self.n
    }

    #[inline]
    fn set_negative(&mut self, l: Lit) {
        self.values[l] = AssignmentCell::Def(false);
        self.values[-l] = AssignmentCell::Def(true);
    }

    #[inline]
    fn set_undef(&mut self, l: Lit) {
        self.values[l] = AssignmentCell::UnDef;
        self.values[-l] = AssignmentCell::UnDef;
    }
}

impl Index<Lit> for Assignment {
    type Output = AssignmentCell;

    #[inline]
    fn index(&self, l: Lit) -> &Self::Output {
        &self.values[l]
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum ClauseState {
    Implied(Lit),
    Satisfied,
    Conflict,
    Otherwise(Lit),
}

#[derive(Debug)]
struct Clause {
    lits: Vec<Lit>, // literals ([0], [1] are watched literals)
}

impl Clause {
    fn new(lits: Vec<Lit>) -> Self {
        Clause { lits }
    }

    fn len(&self) -> usize {
        self.lits.len()
    }

    fn notice_negative(&mut self, lit: Lit, assigns: &Assignment) -> ClauseState {
        assert_eq!(AssignmentCell::Def(false), assigns[lit]);
        if self.lits[1] == lit {
            self.lits.swap(0, 1);
        }
        if assigns[self.lits[1]] == AssignmentCell::Def(true) {
            return ClauseState::Satisfied; // already sat
        }
        // assigns[lits[1]] is undef or false
        for i in 2..self.lits.len() {
            match assigns[self.lits[i]] {
                AssignmentCell::Def(false) => (),
                _ => {
                    self.lits.swap(0, i);
                    return ClauseState::Otherwise(self.lits[0]);
                }
            }
        }
        // assigns[lits[0]] is false
        if assigns[self.lits[1]] == AssignmentCell::Def(false) {
            ClauseState::Conflict
        } else {
            ClauseState::Implied(self.lits[1])
        }
    }

    fn is_all_false(&self, assigns: &Assignment) -> bool {
        self.lits.iter().all(|&l| match &assigns[l] {
            AssignmentCell::Def(false) => true,
            _ => false,
        })
    }
}

impl Index<usize> for Clause {
    type Output = Lit;

    #[inline]
    fn index(&self, i: usize) -> &Self::Output {
        &self.lits[i]
    }
}

#[derive(Debug)]
struct ClauseMap {
    map: LitArray<Vec<usize>>,
}

impl ClauseMap {
    fn new(n: usize) -> ClauseMap {
        ClauseMap {
            map: LitArray::new(n),
        }
    }

    fn swap_list(&mut self, l: Lit, list: &mut Vec<usize>) {
        std::mem::swap(list, &mut self.map[l]);
    }

    fn insert(&mut self, l: Lit, c: usize) {
        self.map[l].push(c);
    }
}

#[derive(Debug, Clone, Copy, Eq, PartialEq)]
enum Step {
    Decided(Lit),
    Deduced(Lit),
}

impl Step {
    fn literal(&self) -> Lit {
        match self {
            Step::Decided(l) => *l,
            Step::Deduced(l) => *l,
        }
    }
}

#[derive(Debug)]
struct Solver {
    assigns: Assignment,   // assigns of variables
    db: Vec<Clause>,       // clause data base
    clause_map: ClauseMap, // literal -> clause index
    trail: Vec<Step>,      // decision/deduced trail
    propagated: usize,     // how many literals are propagated ?
    current_level: usize,
    level: Vec<Option<usize>>,
    reason: Vec<Option<usize>>, // reason clause of deduction for CDCL
    analysis_marked: Vec<bool>,
}

impl Solver {
    fn new(p: Problem) -> Solver {
        // preprocess
        let db = p
            .clause
            .into_iter()
            .map(|x| Clause::new(x))
            .collect::<Vec<_>>();

        let mut clause_map = ClauseMap::new(p.variables);
        for (idx, c) in db.iter().enumerate() {
            clause_map.insert(c.lits[0], idx); // watch literal/clause
            clause_map.insert(c.lits[1], idx);
        }
        Solver {
            assigns: Assignment::new(p.variables),
            db,
            clause_map,
            trail: Vec::with_capacity(p.variables),
            propagated: 0,
            current_level: 0,
            level: vec![None; p.variables + 1],
            reason: vec![None; p.variables + 1],
            analysis_marked: vec![false; p.variables + 1],
        }
    }

    fn run(&mut self) -> bool {
        loop {
            while let Some(conflict) = self.bcp() {
                if self.current_level == 0 {
                    return false; // UNSAT
                }
                self.resolve_conflict_cdcl(conflict);
            }

            if let Some(l) = self.decide() {
                self.assigns.set_negative(l);
                self.trail.push(Step::Decided(l));
                self.current_level += 1;
                self.level[l.abs() as usize] = Some(self.current_level);
                self.reason[l.abs() as usize] = None;
            } else {
                assert!(self.db.iter().all(|c| !c.is_all_false(&self.assigns)));
                return true; // SAT
            }
        }
    }

    #[allow(dead_code)]
    fn resolve_conflict_dpll(&mut self) {
        while let Some(step) = self.trail.pop() {
            match step {
                Step::Deduced(l) => {
                    self.assigns.set_undef(l);
                    self.level[l.abs() as usize] = None;
                }
                Step::Decided(l) => {
                    self.propagated = self.trail.len(); // set back propagate level
                    self.assigns.set_negative(-l);
                    self.trail.push(Step::Deduced(-l));
                    self.current_level -= 1; // modify decision level
                    self.level[l.abs() as usize] = Some(self.current_level);
                    return;
                }
            }
        }
    }

    fn back_jump(&mut self, lv: usize) {
        while self.current_level > lv {
            match self.trail.pop() {
                Some(Step::Deduced(l)) => {
                    self.assigns.set_undef(l);
                    self.level[l.abs() as usize] = None;
                    self.reason[l.abs() as usize] = None;
                }
                Some(Step::Decided(l)) => {
                    self.assigns.set_undef(l);
                    self.level[l.abs() as usize] = None;
                    self.current_level -= 1;
                }
                _ => unreachable!(),
            }
        }
        assert_eq!(lv, self.current_level);
    }

    // linear-time first uip calculation
    // https://efforeffort.wordpress.com/2009/03/09/linear-time-first-uip-calculation/
    fn analyze(&mut self, conflict: usize) -> (Clause, usize) {
        let mut learnt = vec![0]; // dummy for first UIP
        let mut current_level_literals: usize = 0;
        let mut trail_last = self.trail.len();
        let mut literal;
        let mut reason_id = conflict;
        loop {
            let reason = &self.db[reason_id];
            for i in 0..reason.len() {
                let lit = reason[i];
                let var = lit.abs() as usize;
                if self.analysis_marked[var] {
                    continue;
                }
                self.analysis_marked[var] = true;
                if self.level[var] == Some(self.current_level) {
                    current_level_literals += 1;
                } else {
                    learnt.push(lit);
                }
            }

            loop {
                trail_last -= 1;
                literal = self.trail[trail_last].literal();
                if self.analysis_marked[literal.abs() as usize] {
                    break;
                }
            }

            if current_level_literals == 1 {
                break;
            }

            reason_id = self.reason[literal.abs() as usize].unwrap();
            current_level_literals -= 1;
        }

        // reset mark
        for i in trail_last..self.trail.len() {
            self.analysis_marked[self.trail[i].literal().abs() as usize] = false;
        }
        for &i in &learnt {
            self.analysis_marked[i.abs() as usize] = false;
        }

        assert_ne!(0, literal);
        learnt[0] = literal;
        let lv = learnt[1..]
            .iter()
            .fold(0, |lv, &l| lv.max(self.level[l.abs() as usize].unwrap()));
        (Clause::new(learnt), lv)
    }

    fn resolve_conflict_cdcl(&mut self, conflict: usize) {
        let (learnt, lv) = self.analyze(conflict); // fuip must be assigned to true
        let first_uip = learnt[0];
        self.db.push(learnt);
        self.back_jump(lv);
        // assigned true for fuip
        self.propagated = self.trail.len();
        self.assigns.set_negative(-first_uip);
        self.trail.push(Step::Deduced(-first_uip));
        self.level[first_uip.abs() as usize] = Some(self.current_level);
        self.reason[first_uip.abs() as usize] = Some(self.db.len() - 1);
    }

    // return selected literal which assigned false
    fn decide(&mut self) -> Option<Lit> {
        for i in 1..=self.assigns.count() {
            let l = i as Lit;
            if self.assigns[l].is_undef() {
                return Some(-l);
            }
        }
        None
    }

    // boolean constraint propagation
    // return conflicting clause index
    fn bcp(&mut self) -> Option<usize> {
        use ClauseState::*;
        let mut clause_list = Vec::with_capacity(0);
        while self.propagated < self.trail.len() {
            // get literal assigned false
            let l = match self.trail[self.propagated] {
                Step::Decided(l) | Step::Deduced(l) => l,
            };

            self.propagated += 1; // modify propagated level

            self.clause_map.swap_list(l, &mut clause_list); // reset/get clause list watched l
            let mut i = 0;
            while i < clause_list.len() as i64 {
                let idx = clause_list[i as usize];
                match self.db[idx].notice_negative(l, &self.assigns) {
                    Implied(unit) => {
                        self.assigns.set_negative(-unit);
                        self.trail.push(Step::Deduced(-unit));
                        self.level[unit.abs() as usize] = Some(self.current_level);
                        self.reason[unit.abs() as usize] = Some(idx);
                    }
                    Satisfied => (),
                    Conflict => {
                        self.clause_map.swap_list(l, &mut clause_list);
                        return Some(idx);
                    }
                    Otherwise(new_wl) => {
                        assert_ne!(l, new_wl);
                        self.clause_map.insert(new_wl, idx);
                        clause_list.swap_remove(i as usize);
                        i -= 1;
                    }
                }
                i += 1;
            }
            self.clause_map.swap_list(l, &mut clause_list);
        }
        None
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
        assert_eq!(sat, solve(&path), "wrong answer at {}.", path);
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
fn test_false() {
    let problem = Problem {
        variables: 2,
        clause: vec![vec![1, 2], vec![1, -2], vec![-1, 2], vec![-1, -2]],
    };
    assert_eq!(Solver::new(problem).run(), false);
}

#[test]
fn test_false2() {
    let problem = Problem {
        variables: 3,
        clause: vec![
            vec![1, 2, 3],
            vec![1, 2, -3],
            vec![1, -2, 3],
            vec![1, -2, -3],
            vec![-1, 2, 3],
            vec![-1, 2, -3],
            vec![-1, -2, 3],
            vec![-1, -2, -3],
        ],
    };
    assert_eq!(Solver::new(problem).run(), false);
}

#[test]
fn test_false3() {
    let src = "p cnf 4 8
    1  2 -3 0
   -1 -2  3 0
    2  3 -4 0
   -2 -3  4 0
    1  3  4 0
   -1 -3 -4 0
   -1  2  4 0
    1 -2 -4 0";
    let p = parse_dimacs(src).unwrap();
    assert_eq!(false, Solver::new(p).run());
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
