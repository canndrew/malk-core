use std::rc::Rc;
use std::ops;
use std::cmp::Ordering::*;

use TermKind::*;

/// A pointer to a term.
#[derive(Debug, Clone, PartialEq)]
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
#[derive(Debug, Clone, PartialEq)]
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

    /// A dependent pair type (ie. sigma type)
    PairType {
        head_type: Term,
        tail_type: Term,
    },

    /// A pair term.
    PairTerm {
        head: Term,
        tail: Term,
    },

    /// Dependent pair elimintation.
    PairElim {
        pair: Term,
        res: Term,
        head_type: Term,
        tail_type: Term,
    },

    /// The canonical empty type, (ie. bottom).
    NeverType,

    /// Never type elimintator
    NeverElim {
        never: Term,
    },

    /// Disjoint union, sum type.
    EitherType {
        left_type: Term,
        right_type: Term,
    },

    /// Inject left.
    EitherLeft {
        val: Term,
    },

    /// Inject right.
    EitherRight {
        val: Term,
    },

    /// Case match on a sum type.
    EitherElim {
        arg: Term,
        arg_type: Term,
        res_type: Term,
        on_left: Term,
        on_right: Term,
    },

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
        PairType { .. } |
        NeverType |
        NeverElim { .. } |
        EitherType { .. } |
        EitherLeft { .. } |
        EitherRight { .. } |
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
                    let res = substitute(body, arg, 0);
                    normalise(&res)
                },
                _ => term.clone(),
            }
        },

        PairTerm { ref head, ref tail } => {
            match (&**head, &**tail) {
                (&PairElim { pair: ref head_pair, res: ref head_res, .. },
                 &PairElim { pair: ref tail_pair, res: ref tail_res, .. }) => {
                    match (&**head_res, &**tail_res) {
                        (&Var(1), &Var(0)) => {
                            match **head_pair == **tail_pair {
                                true => head_pair.clone(),
                                false => term.clone(),
                            }
                        },
                        _ => term.clone(),
                    }
                },
                _ => term.clone(),
            }
        },

        PairElim { ref pair, ref res, .. } => {
            match **pair {
                PairTerm { ref head, ref tail } => {
                    let res = substitute(res, tail, 0);
                    let res = substitute(&res, head, 0);
                    normalise(&res)
                },
                _ => term.clone(),
            }
        },

        EitherElim { ref arg, ref on_left, ref on_right, .. } => {
            match **arg {
                EitherLeft { ref val } => {
                    let res = substitute(on_left, val, 0);
                    normalise(&res)
                },
                EitherRight { ref val } => {
                    let res = substitute(on_right, val, 0);
                    normalise(&res)
                },
                _ => term.clone(),
            }
        },

        IdentElim { ref a, ref path, ref proof, .. } => {
            match **path {
                IdentTerm => {
                    let res = substitute(proof, a, 0);
                    normalise(&res)
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
        NeverType |
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

        PairType { ref head_type, ref tail_type } => {
            Term::new(PairType {
                head_type: normalise(head_type),
                tail_type: normalise(tail_type),
            })
        },

        PairTerm { ref head, ref tail } => {
            let pair_term = Term::new(PairTerm {
                head: normalise(head),
                tail: normalise(tail),
            });
            reduce_head(&pair_term)
        },

        PairElim { ref pair, ref res, ref head_type, ref tail_type } => {
            let pair_elim = Term::new(PairElim {
                pair: normalise(pair),
                res: normalise(res),
                head_type: normalise(head_type),
                tail_type: normalise(tail_type),
            });
            reduce_head(&pair_elim)
        },

        NeverElim { ref never } => {
            Term::new(NeverElim {
                never: normalise(never),
            })
        },

        EitherType { ref left_type, ref right_type } => {
            Term::new(EitherType {
                left_type: normalise(left_type),
                right_type: normalise(right_type),
            })
        },

        EitherLeft { ref val } => {
            Term::new(EitherLeft {
                val: normalise(val),
            })
        },

        EitherRight { ref val } => {
            Term::new(EitherRight {
                val: normalise(val),
            })
        },

        EitherElim { ref arg, ref arg_type, ref res_type, ref on_left, ref on_right } => {
            let arg = normalise(arg);
            let arg_type = normalise(arg_type);
            let res_type = normalise(res_type);
            let on_left = normalise(on_left);
            let on_right = normalise(on_right);
            let either_elim = Term::new(EitherElim {
                arg: arg,
                arg_type: arg_type,
                res_type: res_type,
                on_left: on_left,
                on_right: on_right,
            });
            reduce_head(&either_elim)
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
        NeverType |
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

        PairType { ref head_type, ref tail_type } => {
            let head_type = substitute(head_type, sub, index);
            let new_sub = bump_index(sub, 1, 0);
            let tail_type = substitute(tail_type, &new_sub, index + 1);
            Term::new(PairType {
                head_type: head_type,
                tail_type: tail_type,
            })
        },

        PairTerm { ref head, ref tail } => {
            Term::new(PairTerm {
                head: substitute(head, sub, index),
                tail: substitute(tail, sub, index),
            })
        },

        PairElim { ref pair, ref res, ref head_type, ref tail_type } => {
            let pair = substitute(pair, sub, index);
            let head_type = substitute(head_type, sub, index);
            let new_sub = bump_index(sub, 1, 0);
            let tail_type = substitute(tail_type, &new_sub, index + 1);
            let new_sub = bump_index(sub, 2, 0);
            let res = substitute(res, &new_sub, index + 2);
            Term::new(PairElim {
                pair: pair,
                res: res,
                head_type: head_type,
                tail_type: tail_type,
            })
        },

        NeverElim { ref never } => {
            Term::new(NeverElim {
                never: substitute(never, sub, index),
            })
        },

        EitherType { ref left_type, ref right_type } => {
            Term::new(EitherType {
                left_type: substitute(left_type, sub, index),
                right_type: substitute(right_type, sub, index),
            })
        },

        EitherLeft { ref val } => {
            Term::new(EitherLeft {
                val: substitute(val, sub, index),
            })
        },

        EitherRight { ref val } => {
            Term::new(EitherRight {
                val: substitute(val, sub, index),
            })
        },

        EitherElim { ref arg, ref arg_type, ref res_type, ref on_left, ref on_right } => {
            let arg = substitute(arg, sub, index);
            let arg_type = substitute(arg_type, sub, index);
            let new_sub = bump_index(sub, 1, 0);
            let res_type = substitute(res_type, &new_sub, index + 1);
            let on_left = substitute(on_left, &new_sub, index + 1);
            let on_right = substitute(on_right, &new_sub, index + 1);
            Term::new(EitherElim {
                arg: arg,
                arg_type: arg_type,
                res_type: res_type,
                on_left: on_left,
                on_right: on_right,
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
        NeverType |
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

        PairType { ref head_type, ref tail_type } => {
            Term::new(PairType {
                head_type: bump_index(head_type, amount, cutoff),
                tail_type: bump_index(tail_type, amount, cutoff + 1),
            })
        },

        PairTerm { ref head, ref tail } => {
            Term::new(PairTerm {
                head: bump_index(head, amount, cutoff),
                tail: bump_index(tail, amount, cutoff),
            })
        },

        PairElim { ref pair, ref res, ref head_type, ref tail_type } => {
            Term::new(PairElim {
                pair: bump_index(pair, amount, cutoff),
                res: bump_index(res, amount, cutoff + 2),
                head_type: bump_index(head_type, amount, cutoff),
                tail_type: bump_index(tail_type, amount, cutoff + 1),
            })
        },

        NeverElim { ref never } => {
            Term::new(NeverElim {
                never: bump_index(never, amount, cutoff),
            })
        },

        EitherType { ref left_type, ref right_type } => {
            Term::new(EitherType {
                left_type: bump_index(left_type, amount, cutoff),
                right_type: bump_index(right_type, amount, cutoff),
            })
        },

        EitherLeft { ref val } => {
            Term::new(EitherLeft {
                val: bump_index(val, amount, cutoff),
            })
        },

        EitherRight { ref val } => {
            Term::new(EitherRight {
                val: bump_index(val, amount, cutoff),
            })
        },

        EitherElim { ref arg, ref arg_type, ref res_type, ref on_left, ref on_right } => {
            Term::new(EitherElim {
                arg: bump_index(arg, amount, cutoff),
                arg_type: bump_index(arg_type, amount, cutoff),
                res_type: bump_index(res_type, amount, cutoff + 1),
                on_left: bump_index(on_left, amount, cutoff + 1),
                on_right: bump_index(on_right, amount, cutoff + 1),
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

