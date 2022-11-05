use std::fmt::Debug;

#[derive(PartialEq, Eq, Clone, Copy)]
pub struct Literal(u16, bool);

impl Debug for Literal {
    fn fmt(&self, f: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        if self.1 { 
            return write!(f, "{}", self.0);
        }
        write!(f, "¬{}", self.0)
    }
}

#[inline(always)]
fn is_unit(c: &[Literal]) -> bool {
    c.len() == 1
}

//Propagate all units across the formula
fn unit_prop(var_assigns: &mut [Option<bool>], f : &mut Vec<Vec<Literal>>) -> bool {
    // Keep track of whether or not f has been changed
    let mut changed = false;

    // Find all the current unit clauses
    let mut units = Vec::new();
    for clause in f.iter() {
        if is_unit(clause) {
            let id = clause[0].0;
            let val = clause[0].1;
            var_assigns[id as usize] = Some(val);
            units.push((id, val));
        }
    }

    // If we have no units we are done
    if units.is_empty() {
        return false;
    }

    // Foreach unit:
    //  - delete clauses that are made true by the assignment
    //  - delete literals that are made true by the assignment
    for (id, val) in units {
        let mut ix = 0;
        while ix < f.len() {
            let clause = &mut f[ix];
            let mut del = false;
            let mut iy = 0;
            while iy < clause.len() {
                let lit = clause[iy];
                if lit.0 == id {
                    changed = true;
                    if lit.1 == val {
                        del = true;
                        break;
                    }
                    clause.remove(iy);
                    continue;
                }
                // Only increment if we didn't delete the literal
                iy += 1;
            }
            // Only increment if we didn't delete the clause
            if del {
                f.remove(ix);
            } else {
                ix += 1;
            }
        }
    }
    changed
}

// Keep propagating units until no more are left
fn full_unit_prop(var_assigns: &mut [Option<bool>], f : &mut Vec<Vec<Literal>>) {
    let mut changed = unit_prop(var_assigns, f);
    while changed {
        changed = unit_prop(var_assigns, f);
    }
}

// Check whether a variable has the same polarity in each occurrence
fn is_pure(v: u16, f : &[Vec<Literal>]) -> Option<bool> {
    let mut seen = false;
    let mut val = false;
    for clause in f {
        for lit in clause {
            if v == lit.0 {
                if seen {
                    if val != lit.1 {
                        return None;
                    }
                } else {
                    seen = true;
                    val = lit.1;
                }
            }
        }
    }
    if !seen {
        return None;
    }
    Some(val)
}

// For each pure variable, replace all clauses containing it and
// replace with a unit clause consisting of that variable with it's occurring polarity
fn pure_lit_elim(var_assigns: &mut [Option<bool>], f: &mut Vec<Vec<Literal>>) {
    for (i, v) in var_assigns.iter_mut().enumerate() {
        if let Some(b) = is_pure(i as u16, f) {
            // Track the assignment
            *v = Some(b);

            // Delete all clauses containing i
            let mut ix = 0;
            while ix < f.len() {
                let mut del = false;
                for lit in &f[ix] {
                    if lit.0 == i as u16 && lit.1 == b {
                        del = true;
                        break;
                    }
                }
                if del {
                    f.remove(ix);
                } else {
                    ix += 1;
                }
            }

            // Add the unit clause
            f.push(vec![Literal(i as u16, b)]);
        }
    }
}

// Perform the DPLL algorithm on a formula in CNF
pub fn dpll(var_assigns: &mut [Option<bool>], f : &mut Vec<Vec<Literal>>) -> bool {
    full_unit_prop(var_assigns, f);
    pure_lit_elim(var_assigns, f);

    if f.is_empty() {
        return true;
    }

    if f.iter().any(|c| c.is_empty()) {
        return false;
    }

    // Pick the next variable to try
    let x = var_assigns.iter().position(|&x| x.is_none());
    let x_v = x.expect("We have assigned all variables, yet the formula is not empty.") as u16;
    
    // Try with true
    f.push(vec![Literal(x_v, true)]);
    if dpll(var_assigns, f) {
        return true;
    }

    // Try with false
    f.last_mut().unwrap()[0].1 = false;
    dpll(var_assigns, f)
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn check_unit() {
        let c = vec![Literal(0, false)];
        let d = vec![Literal(0, false), Literal(1, true), Literal(0, false)];
        let e: Vec<Literal> = vec![];
        assert!(is_unit(&c));
        assert!(!is_unit(&d));
        assert!(!is_unit(&e));
    }

    #[test]
    fn check_unit_prop_empty() {
        let mut c = vec![];
        
        let d: Vec<Vec<Literal>>= vec![];

        let mut vs = [None; 3];
        
        assert!(!unit_prop(&mut vs, &mut c));
        assert_eq!(c, d);
        assert_eq!(vs, [None, None, None]);
    }
    #[test]
    fn check_unit_prop_zero() {
        let mut c = vec![
            vec![Literal(0, true), Literal(2, true)], 
            vec![Literal(1, false), Literal(0, false)],
        ];
        let d = vec![
            vec![Literal(0, true), Literal(2, true)], 
            vec![Literal(1, false), Literal(0, false)],
        ];

        let mut vs = [None; 3];

        assert!(!unit_prop(&mut vs, &mut c));
        assert_eq!(c, d);
        assert_eq!(vs, [None, None, None]);
    }

    #[test]
    fn check_unit_prop_single() {
        let mut c = vec![
            vec![Literal(0, true)], 
            vec![Literal(1, false), Literal(0, false)]
        ];
        let d = vec![
            vec![Literal(1, false)], 
        ];

        let mut vs = [None, None];

        assert!(unit_prop(&mut vs, &mut c));
        assert_eq!(c, d);
        assert_eq!(vs, [Some(true), None]);
    }

    #[test]
    fn check_unit_prop_multi() {
        let mut c = vec![
            vec![Literal(0, true)],
            vec![Literal(2, false), Literal(1, false)], 
            vec![Literal(2, true), Literal(3, false), Literal(0, false)], 
            vec![Literal(1, false)],
            vec![Literal(0, false), Literal(1, true)], 
        ];

        let d = vec![
            vec![Literal(2, true), Literal(3, false)], 
            vec![], 
        ];

        let mut vs = [None; 4];

        assert!(unit_prop(&mut vs, &mut c));
        assert_eq!(c, d);
        assert_eq!(vs, [Some(true), Some(false), None, None]);
    }

    #[test]
    fn check_full_unit_prop() {
        let mut c = vec![
            vec![Literal(0, true)],
            vec![Literal(0, false), Literal(1, false)], 
            vec![Literal(4, false), Literal(2, false), Literal(1, false)], 
            vec![Literal(2, false), Literal(1, true), Literal(4, true)], 
        ];

        let d = vec![
            vec![Literal(2, false), Literal(4, true)], 
        ];

        let mut vs = [None; 4];

        full_unit_prop(&mut vs, &mut c);
        assert_eq!(c, d);
        assert_eq!(vs, [Some(true), Some(false), None, None]);
    }

    #[test]
    fn check_pure() {
        let c = [vec![Literal(0, true)], vec![Literal(1, false), Literal(0, false)]];
        assert_eq!(is_pure(0, &c), None);
        assert_eq!(is_pure(1, &c), Some(false))
    }

    #[test]
    fn check_pure_elim() {
        let mut c = vec![
            vec![Literal(0, true), Literal(3, true)],
            vec![Literal(0, true), Literal(2, false), Literal(5, false)],
            vec![Literal(0, true), Literal(5, true), Literal(9, true)],
            vec![Literal(1, true), Literal(8, true)],
            vec![Literal(4, false), Literal(5, true), Literal(6, false)],
            vec![Literal(4, true), Literal(7, true), Literal(9, false)],
        ];
        let mut vs = [None; 10];

        let d = [
            vec![Literal(0, true)],
            vec![Literal(1, true)],
            vec![Literal(5, true)],
            vec![Literal(7, true)],
        ];
        pure_lit_elim(&mut vs, &mut c);
        assert_eq!(c, d);
    }

    #[test]
    fn check_dpll_simple() {
        let mut c = vec![
            vec![Literal(0, true), Literal(1, true), Literal(2, true)],
            vec![Literal(0, false), Literal(1, true), Literal(2, false)],
            vec![Literal(1, false), Literal(2, true)],
        ];
        let mut vs = [None; 3];
        assert!(dpll(&mut vs, &mut c));
        assert_eq!(vs, [Some(true), Some(true), Some(true)]);
    }

    #[test]
    fn check_dpll_hard() {
        let mut c = vec![
            vec![Literal(0, true), Literal(3, true)],
            vec![Literal(0, true), Literal(2, false), Literal(5, false)],
            vec![Literal(0, true), Literal(5, true), Literal(9, true)],
            vec![Literal(1, true), Literal(8, true)],
            vec![Literal(4, false), Literal(2, false), Literal(6, true)],
            vec![Literal(4, false), Literal(5, true), Literal(6, false)],
            vec![Literal(4, true), Literal(5, true), Literal(7, false)],
            vec![Literal(4, true), Literal(7, true), Literal(9, false)],
        ];
        let mut vs = [None; 10];

        assert!(dpll(&mut vs, &mut c));
        //assert_eq!(vs, [Some(true), Some(true), Some(true)]);
    }
}
