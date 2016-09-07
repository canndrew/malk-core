use std::rc::Rc;
use std::ops;
use std::cmp::Ordering::*;

use TermKind::*;

/// A pointer to a term.
#[derive(Clone)]
pub struct Term(Rc<TermKind>);

impl ops::Deref for Term {
    type Target = TermKind;

    fn deref(&self) -> &TermKind {
        let Term(ref rc_term) = *self;
        &**rc_term
    }
}

impl Term {
    /// Create a new term.
    fn new(kind: TermKind) -> Term {
        Term(Rc::new(kind))
    }
}

/// The different kinds of term that can appear in the AST.
pub enum TermKind {
    /// The type of all types, and levels, which does not itself have a type.
    Omega,


    /// The type of universe levels.
    Level,

    /// Universe level zero.
    LevelZero,

    /// Universe level (pred + 1).
    LevelSucc {
        pred: Term,
    },

    /// Universe level max(a, b)
    LevelMax {
        a: Term,
        b: Term,
    },


    /// The type of types, indexed by levels.
    Type {
        level: Term,
    },

    /// A variable.
    Var(usize),

    /// The type of functions. (ie pi types)
    FuncType {
        arg_type: Term,
        res_type: Term,
    },

    /// Functions.
    FuncTerm {
        body: Term,
    },

    /// Function application.
    FuncApp {
        func: Term,
        arg: Term,
        arg_type: Term,
        res_type: Term,
    },

    /// The unit type.
    UnitType,

    /// The unit term.
    UnitTerm,

    /// The type of identifications (a == b)
    IdentType {
        term_type: Term,
        a: Term,
        b: Term,
    },

    /// Reflexivity,
    IdentTerm,

    /// J-elimination for identities.
    IdentElim {
        term_type: Term,
        a: Term,
        b: Term,
        path: Term,
        context: Term,
        proof: Term,
    },

    /// A recursive type. `rec_type` is under a context where Var(0) refers back to the type.
    RecType {
        rec_type: Term,
    },

    /// A recursive term. Used to mark `rec_term` as a member of a recursive type.
    RecTerm {
        rec_term: Term,
    },

    /*
    /// Recursive elimintation. Fold over the term `arg` or recursive type `arg_type`.
    RecElim {
        arg: Term,
        res: Term,
        arg_type: Term,
        res_type: Term,
    }
    */
}

/// Normalise a term assuming all it's subterms are already normalised. Does beta/eta reduction on
/// the head of the term.
pub fn reduce_head(term: &Term) -> Term {
    match **term {
        Omega |
        Level |
        LevelZero |
        LevelSucc { .. } |
        FuncType { .. } |
        Var(..) |
        UnitType |
        UnitTerm |
        IdentType { .. } |
        IdentTerm |
        RecType { .. } |
        RecTerm { .. } |
        Type { .. } => term.clone(),

        LevelMax { ref a, ref b } => {
            match (&**a, &**b) {
                (&LevelZero, _) => b.clone(),
                (_, &LevelZero) => a.clone(),
                (&LevelSucc { pred: ref a_pred }, &LevelSucc { pred: ref b_pred }) => {
                    let max = Term::new(LevelMax {
                        a: a_pred.clone(),
                        b: b_pred.clone(),
                    });
                    let max = reduce_head(&max);
                    Term::new(LevelSucc { pred: max })
                },
                _ => term.clone(),
            }
        },

        FuncTerm { ref body } => {
            match **body {
                FuncApp { ref func, ref arg, .. } => {
                    match **arg {
                        Var(0) => func.clone(),
                        _ => term.clone(),
                    }
                },
                _ => term.clone(),
            }
        },

        FuncApp { ref func, ref arg, .. } => {
            match **func {
                FuncTerm { ref body } => {
                    substitute(body, arg, 0)
                },
                _ => term.clone(),
            }
        },

        IdentElim { ref a, ref path, ref proof, .. } => {
            match **path {
                IdentTerm => {
                    substitute(proof, a, 0)
                },
                _ => term.clone(),
            }
        },

        /*
        RecElim { ref arg, ref res, ref arg_type, .. } => {
            match (**arg, **arg_type) => {
                (RecTerm { ref rec_term }, RecType { ref rec_type }) => {
                    let folded = recurse(rec_term, rec_type, arg_type, res, 0);
                    substitute(res, folded, 0)
                },
                _ => term.clone(),
            }
        },
        */
    }
}

/*
pub fn recurse(rec_term: &Term, rec_type: &Term, w_type: &Term, res: &Term, depth: usize) -> Term {
    match (**rec_type, **rec_term) {
        (FuncType { ref arg_type, ref res_type }, FuncTerm { ref body }) => {
            
        },
    }
}
*/

/// Normalise a term.
pub fn normalise(term: &Term) -> Term {
    match **term {
        Omega |
        Var(..) |
        Level |
        UnitType |
        UnitTerm |
        IdentTerm |
        LevelZero => term.clone(),

        LevelSucc { ref pred } => {
            Term::new(LevelSucc {
                pred: normalise(pred),
            })
        },

        LevelMax { ref a, ref b } => {
            let max = Term::new(LevelMax {
                a: normalise(a),
                b: normalise(b),
            });
            reduce_head(&max)
        },

        Type { ref level } => {
            Term::new(Type {
                level: normalise(level),
            })
        },

        FuncType { ref arg_type, ref res_type } => {
            Term::new(FuncType {
                arg_type: normalise(arg_type),
                res_type: normalise(res_type),
            })
        },

        FuncTerm { ref body } => {
            let func_term = Term::new(FuncTerm {
                body: normalise(body),
            });
            reduce_head(&func_term)
        },

        FuncApp { ref func, ref arg, ref arg_type, ref res_type } => {
            let func_app = Term::new(FuncApp {
                func: normalise(func),
                arg: normalise(arg),
                arg_type: normalise(arg_type),
                res_type: normalise(res_type),
            });
            reduce_head(&func_app)
        },

        IdentType { ref term_type, ref a, ref b } => {
            Term::new(IdentType {
                term_type: normalise(term_type),
                a: normalise(a),
                b: normalise(b),
            })
        },

        IdentElim { ref term_type, ref a, ref b, ref path, ref context, ref proof } => {
            let term_type = normalise(term_type);
            let a = normalise(a);
            let b = normalise(b);
            let path = normalise(path);
            let context = normalise(context);
            let proof = normalise(proof);
            let ident_elim = Term::new(IdentElim {
                term_type: term_type,
                a: a,
                b: b,
                path: path,
                context: context,
                proof: proof,
            });
            reduce_head(&ident_elim)
        },

        RecType { ref rec_type } => {
            Term::new(RecType {
                rec_type: normalise(rec_type),
            })
        },

        RecTerm { ref rec_term } => {
            Term::new(RecTerm {
                rec_term: normalise(rec_term),
            })
        },
    }
}

/// substitute `sub` for the variable at `index`.
pub fn substitute(term: &Term, sub: &Term, index: usize) -> Term {
    match **term {
        Omega |
        Level |
        LevelZero |
        UnitType |
        UnitTerm |
        IdentTerm => term.clone(),

        LevelSucc { ref pred } => {
            Term::new(LevelSucc {
                pred: substitute(pred, sub, index)
            })
        },

        LevelMax { ref a, ref b } => {
            Term::new(LevelMax {
                a: substitute(a, sub, index),
                b: substitute(b, sub, index),
            })
        },

        Type { ref level } => {
            Term::new(Type {
                level: substitute(level, sub, index),
            })
        },

        Var(i) => {
            match i.cmp(&index) {
                Less => term.clone(),
                Equal => sub.clone(),
                Greater => Term::new(Var(i - 1)),
            }
        },

        FuncType { ref arg_type, ref res_type } => {
            let arg_type = substitute(arg_type, sub, index);
            let sub = bump_index(sub, 1, 0);
            let res_type = substitute(res_type, &sub, index + 1);
            Term::new(FuncType {
                arg_type: arg_type,
                res_type: res_type,
            })
        },

        FuncTerm { ref body } => {
            let sub = bump_index(sub, 1, 0);
            Term::new(FuncTerm {
                body: substitute(body, &sub, index + 1),
            })
        },

        FuncApp { ref func, ref arg, ref arg_type, ref res_type } => {
            let func = substitute(func, sub, index);
            let arg = substitute(arg, sub, index);
            let arg_type = substitute(arg_type, sub, index);
            let sub = bump_index(sub, 1, 0);
            let res_type = substitute(res_type, &sub, index + 1);
            Term::new(FuncApp {
                func: func,
                arg: arg,
                arg_type: arg_type,
                res_type: res_type,
            })
        },

        IdentType { ref term_type, ref a, ref b } => {
            Term::new(IdentType {
                term_type: substitute(term_type, sub, index),
                a: substitute(a, sub, index),
                b: substitute(b, sub, index),
            })
        },

        IdentElim { ref term_type, ref a, ref b, ref path, ref context, ref proof } => {
            let term_type = substitute(term_type, sub, index);
            let a = substitute(a, sub, index);
            let b = substitute(b, sub, index);
            let path = substitute(path, sub, index);
            let new_sub = bump_index(sub, 3, 0);
            let context = substitute(context, &new_sub, index + 3);
            let new_sub = bump_index(sub, 1, 0);
            let proof = substitute(proof, &new_sub, index + 1);
            Term::new(IdentElim {
                term_type: term_type,
                a: a,
                b: b,
                path: path,
                context: context,
                proof: proof,
            })
        },

        RecType { ref rec_type } => {
            let new_sub = bump_index(sub, 1, 0);
            Term::new(RecType {
                rec_type: substitute(rec_type, &new_sub, index + 1),
            })
        },

        RecTerm { ref rec_term } => {
            Term::new(RecTerm {
                rec_term: substitute(rec_term, sub, index),
            })
        },
    }
}

/// Bump all the index of the variables in a term by `amount`, ignoring variables whose index is
/// less than `cutoff`. This is hygenic when it recurses into subcontexts (ie. cutoff is adjusted
/// appropriately).
///
/// # Example
/// ```
/// bump_index(`(Var(0), Var(1), Var(2))`, 1, 100) => `(Var(0), Var(101), Var(102))`
/// bump_index(`(Var(0), FuncTerm(Var(0))))`, 0, 100) => `(Var(100), FuncTerm(Var(0)))`
/// ```
pub fn bump_index(term: &Term, amount: usize, cutoff: usize) -> Term {
    match **term {
        Omega |
        Level |
        LevelZero |
        UnitType |
        UnitTerm |
        IdentTerm => term.clone(),

        LevelSucc { ref pred } => {
            Term::new(LevelSucc {
                pred: bump_index(pred, amount, cutoff),
            })
        },

        LevelMax { ref a, ref b } => {
            Term::new(LevelMax {
                a: bump_index(a, amount, cutoff),
                b: bump_index(b, amount, cutoff),
            })
        },

        Type { ref level } => {
            Term::new(Type {
                level: bump_index(level, amount, cutoff),
            })
        },

        Var(i) => {
            match i < cutoff {
                true => term.clone(),
                false => Term::new(Var(i + amount)),
            }
        },

        FuncType { ref arg_type, ref res_type } => {
            Term::new(FuncType {
                arg_type: bump_index(arg_type, amount, cutoff),
                res_type: bump_index(res_type, amount, cutoff + 1),
            })
        },

        FuncTerm { ref body } => {
            Term::new(FuncTerm {
                body: bump_index(body, amount, cutoff + 1),
            })
        },

        FuncApp { ref func, ref arg, ref arg_type, ref res_type } => {
            Term::new(FuncApp {
                func: bump_index(func, amount, cutoff),
                arg: bump_index(arg, amount, cutoff),
                arg_type: bump_index(arg_type, amount, cutoff),
                res_type: bump_index(res_type, amount, cutoff + 1),
            })
        },

        IdentType { ref term_type, ref a, ref b } => {
            Term::new(IdentType {
                term_type: bump_index(term_type, amount, cutoff),
                a: bump_index(a, amount, cutoff),
                b: bump_index(b, amount, cutoff),
            })
        },

        IdentElim { ref term_type, ref a, ref b, ref path, ref context, ref proof } => {
            Term::new(IdentElim {
                term_type: bump_index(term_type, amount, cutoff),
                a: bump_index(a, amount, cutoff),
                b: bump_index(b, amount, cutoff),
                path: bump_index(path, amount, cutoff),
                context: bump_index(context, amount, cutoff + 3),
                proof: bump_index(proof, amount, cutoff + 1),
            })
        }

        RecType { ref rec_type } => {
            Term::new(RecType {
                rec_type: bump_index(rec_type, amount, cutoff + 1),
            })
        },

        RecTerm { ref rec_term } => {
            Term::new(RecTerm {
                rec_term: bump_index(rec_term, amount, cutoff),
            })
        },
    }
}

