//! Term creation functions.

use hashconsing::{ HashConsign, HConser } ;

use common::* ;
use term::{ RTerm, Term, Op } ;

/// Type of the term factory.
type Factory = RwLock< HashConsign<RTerm> > ;

lazy_static!{
  /// Term factory.
  static ref factory: Factory = RwLock::new(
    HashConsign::with_capacity( conf.instance.term_capa )
  ) ;
}

/// Creates a term.
#[inline(always)]
pub fn term(t: RTerm) -> Term {
  factory.mk(t)
}

/// Creates a variable.
#[inline(always)]
pub fn var<V: Into<VarIdx>>(v: V) -> Term {
  factory.mk( RTerm::Var(v.into()) )
}

/// Creates an integer constant.
#[inline(always)]
pub fn int<I: Into<Int>>(i: I) -> Term {
  factory.mk(
    RTerm::Int( i.into() )
  )
}
/// Creates the constant `0`.
#[inline(always)]
pub fn zero() -> Term {
  int( Int::zero() )
}
/// Creates the constant `1`.
#[inline(always)]
pub fn one() -> Term {
  int( Int::one() )
}

/// Creates a boolean.
#[inline(always)]
pub fn bool(b: bool) -> Term {
  factory.mk( RTerm::Bool(b) )
}
/// Creates the constant `true`.
#[inline(always)]
pub fn tru() -> Term {
  bool(true)
}
/// Creates the constant `false`.
#[inline(always)]
pub fn fls() -> Term {
  bool(false)
}

/// Creates an operator application.
///
/// Runs [`simplify`](fn.simplify.html) and returns its result.
#[inline(always)]
pub fn app(op: Op, args: Vec<Term>) -> Term {
  simplify(op, args)
}

/// Creates a less than or equal to.
#[inline(always)]
pub fn le(lhs: Term, rhs: Term) -> Term {
  app(Op::Le, vec![lhs, rhs])
}
/// Creates a less than.
#[inline(always)]
pub fn lt(lhs: Term, rhs: Term) -> Term {
  app(Op::Lt, vec![lhs, rhs])
}
/// Creates a greater than.
#[inline(always)]
pub fn gt(lhs: Term, rhs: Term) -> Term {
  app(Op::Gt, vec![lhs, rhs])
}
/// Creates a greater than or equal to.
#[inline(always)]
pub fn ge(lhs: Term, rhs: Term) -> Term {
  app(Op::Ge, vec![lhs, rhs])
}

/// Creates an equality.
#[inline(always)]
pub fn eq(lhs: Term, rhs: Term) -> Term {
  app(Op::Eql, vec![lhs, rhs])
}








#[doc = r#"Tries to simplify an operator application.

# Nullary / unary applications of `And` and `Or`

```
use hoice_lib::term ;
use hoice_lib::term::Op::* ;

let tru = term::bool(true) ;
let fls = term::bool(false) ;
let var_1 = term::var(7) ;
let var_2 = term::var(2) ;

assert_eq!( fls, term::simplify(And, vec![]) ) ;
assert_eq!( tru, term::simplify(Or, vec![]) ) ;
assert_eq!( var_2, term::simplify(And, vec![ var_2.clone() ]) ) ;
assert_eq!( var_1, term::simplify(Or, vec![ var_1.clone() ]) ) ;

let and = term::app(And, vec![ var_2.clone(), var_1.clone() ]) ;
assert_eq!(
  and, term::simplify(And, vec![ var_2.clone(), var_1.clone() ])
) ;
let or = term::app(Or, vec![ var_2.clone(), var_1.clone() ]) ;
assert_eq!(
  or, term::simplify(Or, vec![ var_2.clone(), var_1.clone() ])
) ;
```

# Double negations

```
use hoice_lib::term ;
use hoice_lib::term::Op::* ;

let var_1 = term::var(7) ;
let n_var_1 = term::app( Not, vec![ var_1.clone() ] ) ;
assert_eq!( var_1, term::simplify(Not, vec![ n_var_1 ]) ) ;

let var_1 = term::var(7) ;
let n_var_1 = term::app( Not, vec![ var_1.clone() ] ) ;
assert_eq!( n_var_1, term::simplify(Not, vec![ var_1 ]) ) ;
```
"#]
pub fn simplify(
  op: Op, mut args: Vec<Term>
) -> Term {
  let (op, args) = match op {
    Op::And => if args.is_empty() {
      return term::bool(false)
    } else if args.len() == 1 {
      return args.pop().unwrap()
    } else {
      (op, args)
    },
    Op::Or => if args.is_empty() {
      return term::bool(true)
    } else if args.len() == 1 {
      return args.pop().unwrap()
    } else {
      (op, args)
    },
    Op::Not => {
      assert!( args.len() == 1 ) ;
      match * args[0] {
        RTerm::App { op: Op::Not, ref args } => {
          return args[0].clone()
        },
        _ => (),
      }
      (op, args)
    },
    Op::Add => {
      let mut cnt = 0 ;
      let mut zero = None ;
      'remove_zeros: while cnt < args.len() {
        if let Some(int) = args[0].int_val() {
          if int.is_zero() {
            zero = Some( args.swap_remove(cnt) ) ;
            continue 'remove_zeros
          }
        }
        cnt += 1
      }
      if args.len() == 0 {
        return zero.expect("trying to construct an empty application")
      } else if args.len() == 1 {
        return args.pop().unwrap()
      } else {
        (op, args)
      }
    },
    // Op::Gt => if args.len() != 2 {
    //   panic!( "[bug] operator `>` applied to {} operands", args.len() )
    // } else {
    //   if let Some( i ) = args[0].int_val() {
    //     // Checks whether it's zero before decreasing.
    //     if i.is_zero() {
    //       // Args is unchanged, term is equivalent to false anyway.
    //       (Op::Ge, args)
    //     } else {
    //       args[0] = term::int(i - Int::one()) ;
    //       (Op::Ge, args)
    //     }
    //   } else if let Some( i ) = args[1].int_val() {
    //     args[1] = term::int(i + Int::one()) ;
    //     (Op::Ge, args)
    //   } else {
    //     (op, args)
    //   }
    // },
    // Op::Lt => if args.len() != 2 {
    //   panic!( "[bug] operator `<` applied to {} operands", args.len() )
    // } else {
    //   if let Some( i ) = args[0].int_val() {
    //     args[0] = term::int(i + Int::one()) ;
    //     (Op::Le, args)
    //   } else if let Some( i ) = args[1].int_val() {
    //     // Checks whether it's zero before decreasing.
    //     if i.is_zero() {
    //       // Args is unchanged, term is equivalent to false anyway.
    //       (Op::Le, args)
    //     } else {
    //       args[1] = term::int(i - Int::one()) ;
    //       (Op::Le, args)
    //     }
    //   } else {
    //     (op, args)
    //   }
    // },
    _ => (op, args),
  } ;
  factory.mk( RTerm::App { op, args } )
}