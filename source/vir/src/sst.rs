//! VIR-SST (Statement-oriented Syntax Tree)
//!
//! Rust-AST --> Rust-HIR --> VIR-AST --> VIR-SST --> AIR --> Z3-SMT
//!
//! Whereas VIR-AST supports statements inside expressions,
//! SST expressions cannot contain statments.
//! SST is designed to make the translation to AIR as straightforward as possible.

use crate::ast::{
    ArithOp, AssertQueryMode, BinaryOp, BitwiseOp, Constant, Fun, InequalityOp, InvAtomicity, Mode,
    Path, Quant, SpannedTyped, Typ, Typs, UnaryOp, UnaryOpr, VarAt,
};
use crate::def::Spanned;
use crate::interpreter::InterpExp;
use air::ast::{Binders, Ident, Span};
use air::errors::Error;
use std::fmt::{self};
use std::sync::Arc;

pub type Trig = Exps;
pub type Trigs = Arc<Vec<Trig>>;

pub struct BndInfo {
    pub span: Span,
    pub trigs: Trigs,
}

pub type Bnd = Arc<Spanned<BndX>>;
#[derive(Clone, Debug)]
pub enum BndX {
    Let(Binders<Exp>),
    Quant(Quant, Binders<Typ>, Trigs),
    Lambda(Binders<Typ>),
    Choose(Binders<Typ>, Trigs, Exp),
}

#[derive(Debug, Clone, PartialEq, Eq, PartialOrd, Ord, Hash)]
pub struct UniqueIdent {
    pub name: Ident,
    // None for bound vars, Some disambiguating integer for local vars
    pub local: Option<u64>,
}

pub type Exp = Arc<SpannedTyped<ExpX>>;
pub type Exps = Arc<Vec<Exp>>;
#[derive(Debug, Clone)]
pub enum ExpX {
    Const(Constant),
    Var(UniqueIdent),
    VarLoc(UniqueIdent),
    VarAt(UniqueIdent, VarAt),
    Loc(Exp),
    // used only during sst_to_air to generate AIR Old
    Old(Ident, UniqueIdent),
    // call to spec function
    Call(Fun, Typs, Exps),
    CallLambda(Typ, Exp, Exps),
    Ctor(Path, Ident, Binders<Exp>),
    Unary(UnaryOp, Exp),
    UnaryOpr(UnaryOpr, Exp),
    Binary(BinaryOp, Exp, Exp),
    If(Exp, Exp, Exp),
    WithTriggers(Trigs, Exp),
    Bind(Bnd, Exp),
    // only used internally by the interpreter; should never be seen outside it
    Interp(InterpExp),
}

#[derive(Debug, Clone, Copy)]
pub enum ParPurpose {
    MutPre,
    MutPost,
    Regular,
}

/// Function parameter
pub type Par = Arc<Spanned<ParX>>;
pub type Pars = Arc<Vec<Par>>;
#[derive(Debug, Clone)]
pub struct ParX {
    pub name: Ident,
    pub typ: Typ,
    pub mode: Mode,
    pub purpose: ParPurpose,
}

#[derive(Clone, Debug)]
pub struct Dest {
    pub dest: Exp,
    pub is_init: bool,
}

pub type Stm = Arc<Spanned<StmX>>;
pub type Stms = Arc<Vec<Stm>>;

#[derive(Debug)]
pub enum StmX {
    // call to exec/proof function (or spec function for checking_recommends)
    Call(Fun, Mode, Typs, Exps, Option<Dest>),
    // note: failed assertion reports Stm's span, plus an optional additional span
    Assert(Option<Error>, Exp),
    AssertBV(Exp),
    Assume(Exp),
    Assign {
        lhs: Dest,
        rhs: Exp,
    },
    Fuel(Fun, u32),
    DeadEnd(Stm),
    If(Exp, Stm, Option<Stm>),
    While {
        cond_stms: Stms,
        cond_exp: Exp,
        body: Stm,
        invs: Exps,
        typ_inv_vars: Arc<Vec<(UniqueIdent, Typ)>>,
        modified_vars: Arc<Vec<UniqueIdent>>,
    },
    OpenInvariant(Exp, UniqueIdent, Typ, Stm, InvAtomicity),
    Block(Stms),
    AssertQuery {
        mode: AssertQueryMode,
        typ_inv_vars: Arc<Vec<(UniqueIdent, Typ)>>,
        body: Stm,
    },
}

pub type LocalDecl = Arc<LocalDeclX>;
#[derive(Debug)]
pub struct LocalDeclX {
    pub ident: UniqueIdent,
    pub typ: Typ,
    pub mutable: bool,
}
impl ExpX {
    pub(crate) fn fmt(&self, f: &mut fmt::Formatter<'_>, no_encoding: bool) -> fmt::Result {
        use ExpX::*;
        match &self {
            Const(c) => match c {
                Constant::Bool(b) => write!(f, "{}", b),
                Constant::Int(i) => write!(f, "{}", i),
            },
            Var(id) => write!(f, "{}", id.name),
            Call(fun, _, exps) => {
                let args = exps.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", ");
                write!(f, "{}({})", fun.path.segments.last().unwrap(), args)
            }
            Unary(op, exp) => match op {
                UnaryOp::Not => write!(f, "!({})", exp),
                UnaryOp::BitNot => write!(f, "!{}", exp),
                UnaryOp::Trigger(..) => Ok(()),
                UnaryOp::Clip(_range) => {
                    if no_encoding {
                        write!(f, "{}", exp)
                    } else {
                        write!(f, "clip({})", exp)
                    }
                }
                UnaryOp::CoerceMode { .. } => Ok(()),
                UnaryOp::MustBeFinalized => {
                    if no_encoding {
                        // println!("warning: must_be_finalized, {}", exp);
                        write!(f, "{}", exp)
                    } else {
                        Ok(())
                    }
                }
            },
            UnaryOpr(op, exp) => {
                use crate::ast::UnaryOpr::*;
                match op {
                    Box(_) => {
                        if no_encoding {
                            write!(f, "{}", exp)
                        } else {
                            write!(f, "box({})", exp)
                        }
                    }
                    Unbox(_) => {
                        if no_encoding {
                            write!(f, "{}", exp)
                        } else {
                            write!(f, "unbox({})", exp)
                        }
                    }
                    HasType(t) => write!(f, "{}.has_type({:?})", exp, t),
                    IsVariant { datatype: _, variant } => write!(f, "{}.is_type({})", exp, variant),
                    TupleField { tuple_arity: _, field } => write!(f, "{}.{}", exp, field),
                    Field(field) => write!(f, "{}.{}", exp, field.field),
                }
            }
            Binary(op, e1, e2) => {
                use ArithOp::*;
                use BinaryOp::*;
                use BitwiseOp::*;
                use InequalityOp::*;
                match op {
                    And => write!(f, "{} && {}", e1, e2),
                    Or => write!(f, "{} || {}", e1, e2),
                    Xor => write!(f, "{} ^ {}", e1, e2),
                    Implies => write!(f, "{} ==> {}", e1, e2),
                    Eq(_) => write!(f, "{} == {}", e1, e2),
                    Ne => write!(f, "{} != {}", e1, e2),
                    Inequality(o) => match o {
                        Le => write!(f, "{} <= {}", e1, e2),
                        Ge => write!(f, "{} >= {}", e1, e2),
                        Lt => write!(f, "{} < {}", e1, e2),
                        Gt => write!(f, "{} > {}", e1, e2),
                    },
                    Arith(o, _) => match o {
                        Add => write!(f, "{} + {}", e1, e2),
                        Sub => write!(f, "{} - {}", e1, e2),
                        Mul => write!(f, "{} * {}", e1, e2),
                        EuclideanDiv => write!(f, "{} / {}", e1, e2),
                        EuclideanMod => write!(f, "{} % {}", e1, e2),
                    },
                    Bitwise(o) => match o {
                        BitXor => write!(f, "{} ^ {}", e1, e2),
                        BitAnd => write!(f, "{} & {}", e1, e2),
                        BitOr => write!(f, "{} | {}", e1, e2),
                        Shr => write!(f, "{} >> {}", e1, e2),
                        Shl => write!(f, "{} << {}", e1, e2),
                    },
                }
            }
            If(e1, e2, e3) => write!(f, "(if {} then {} else {})", e1, e2, e3),
            Bind(bnd, exp) => match &bnd.x {
                BndX::Let(bnds) => {
                    let assigns = bnds
                        .iter()
                        .map(|b| format!("{} = {}", b.name, b.a))
                        .collect::<Vec<_>>()
                        .join(", ");
                    write!(f, "let {} in {}", assigns, exp)
                }
                BndX::Lambda(bnds) => {
                    let assigns =
                        bnds.iter().map(|b| format!("{}", b.name)).collect::<Vec<_>>().join(", ");
                    write!(f, "(|{}| {})", assigns, exp)
                }
                BndX::Quant(..) | BndX::Choose(..) if !no_encoding => {
                    write!(f, "Unexpected: {:?}", self)
                }
                BndX::Quant(qnt, bndrs, _trigs) if no_encoding => {
                    let mut s: String = match qnt.quant {
                        air::ast::Quant::Forall => "Forall".to_string(),
                        air::ast::Quant::Exists => "Exists".to_string(),
                    };
                    for bnd in &**bndrs {
                        s = s + &format!(" {} ", bnd.name);
                        // s = s + &format!(" {} : {:?} ", bnd.name, bnd.a);
                    }
                    // s = s + "triggers: ";
                    // for trig in &** trigs{
                    //     for t in &**trig {
                    //         s = s + &format!(" {t} ")
                    //     }
                    // }
                    write!(f, "{s}, {exp}")
                }
                BndX::Choose(_bndrs, _trigs, _exp) if no_encoding => {
                    write!(f, "choose {:?}", self)
                }
                _ => unreachable!(),
            },
            Ctor(_path, id, bnds) => {
                let args = bnds.iter().map(|b| b.a.to_string()).collect::<Vec<_>>().join(", ");
                write!(f, "{}({})", id, args)
            }
            CallLambda(_typ, e, args) => {
                let args = args.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", ");
                write!(f, "{}({})", e, args)
            }
            VarLoc(..) | VarAt(..) | Loc(..) | Old(..) | WithTriggers(..) => {
                write!(f, "Unexpected: {:?}", self)
            }
            Interp(e) => {
                use InterpExp::*;
                match e {
                    FreeVar(id) => write!(f, "{}", id.name),
                    Seq(s) => {
                        let v = s.iter().map(|e| e.to_string()).collect::<Vec<_>>().join(", ");
                        write!(f, "[{}]", v)
                    }
                }
            }
        }
    }
}

impl fmt::Display for ExpX {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        self.fmt(f, true) // TODO: change true to false
    }
}
