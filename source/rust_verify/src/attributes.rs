use crate::util::{err_span, vir_err_span_str};
use rustc_ast::token::{Token, TokenKind};
use rustc_ast::tokenstream::{TokenStream, TokenTree};
use rustc_hir::{AttrArgs, Attribute};
use rustc_span::Span;
use vir::ast::{AcceptRecursiveType, Mode, TriggerAnnotation, VirErr, VirErrAs};

#[derive(Debug)]
pub(crate) enum AttrTree {
    Fun(Span, String, Option<Box<[AttrTree]>>),
    //Eq(Span, String, String), // TODO(main_new)
}

pub(crate) fn token_to_string(token: &Token) -> Result<Option<String>, ()> {
    match token.kind {
        TokenKind::Literal(lit) => Ok(Some(lit.symbol.as_str().to_string())),
        TokenKind::Ident(symbol, _) => Ok(Some(symbol.as_str().to_string())),
        TokenKind::Comma => Ok(None),
        _ => Err(()),
    }
}

pub(crate) fn token_stream_to_trees(
    span: Span,
    stream: &TokenStream,
) -> Result<Box<[AttrTree]>, ()> {
    let mut token_trees: Vec<&TokenTree> = Vec::new();
    for x in stream.iter() {
        // TODO(1.83) trees?
        token_trees.push(x);
    }
    let mut i = 0;
    let mut trees: Vec<AttrTree> = Vec::new();
    while i < token_trees.len() {
        match &token_trees[i] {
            TokenTree::Token(token, _spacing) => {
                if let Some(name) = token_to_string(token)? {
                    let fargs = if i + 1 < token_trees.len() {
                        if let TokenTree::Delimited(_, _, _, token_stream) = &token_trees[i + 1] {
                            i += 1;
                            Some(token_stream_to_trees(span, token_stream)?)
                        } else {
                            None
                        }
                    } else {
                        None
                    };
                    trees.push(AttrTree::Fun(span, name, fargs));
                }
                i += 1;
            }
            _ => return Err(()),
        }
    }
    Ok(trees.into_boxed_slice())
}

// TODO(main_new) fn mac_args_to_tree(span: Span, name: String, args: &MacArgs) -> Result<AttrTree, ()> {
// TODO(main_new)     match args {
// TODO(main_new)         MacArgs::Empty => Ok(AttrTree::Fun(span, name, None)),
// TODO(main_new)         MacArgs::Delimited(_, _, token_stream) => {
// TODO(main_new)             Ok(AttrTree::Fun(span, name, Some(token_stream_to_trees(span, token_stream)?)))
// TODO(main_new)         }
// TODO(main_new)         MacArgs::Eq(_, token) => match token_to_string(token)? {
// TODO(main_new)             None => Err(()),
// TODO(main_new)             Some(token) => Ok(AttrTree::Eq(span, name, token)),
// TODO(main_new)         },
// TODO(main_new)     }
// TODO(main_new) }

fn attr_args_to_tree(span: Span, name: String, args: &AttrArgs) -> Result<AttrTree, ()> {
    match args {
        AttrArgs::Empty => Ok(AttrTree::Fun(span, name, None)),
        AttrArgs::Delimited(delim) => {
            Ok(AttrTree::Fun(span, name, Some(token_stream_to_trees(span, &delim.tokens)?)))
        }
        AttrArgs::Eq { eq_span: _, expr } => {
            dbg!(&expr);
            // TODO(main_new) match token_to_string(expr.tokens)? {
            // TODO(main_new)     None => Err(()),
            // TODO(main_new)     Some(token) => Ok(AttrTree::Eq(span, name, token)),
            // TODO(main_new) },
            todo!()
        }
    }
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum VerusPrefix {
    None,
    Internal,
    // Unsafe,
    // Type,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
enum AttrPrefix {
    Verus(VerusPrefix),
    Verifier,
    Rustc,
}

fn attr_to_tree(attr: &Attribute) -> Result<Option<(AttrPrefix, Span, AttrTree)>, VirErr> {
    match attr {
        Attribute::Unparsed(item) => match &item.path.segments[..] {
            [segment] if segment.as_str() == "verifier" => match &item.args {
                // TODO(main_new) MacArgs::Delimited(_, _, token_stream) => {
                // TODO(main_new)     let trees: Box<[AttrTree]> = token_stream_to_trees(attr.span, token_stream)
                // TODO(main_new)         .map_err(|_| vir_err_span_str(attr.span, "invalid verifier attribute"))?;
                // TODO(main_new)     if trees.len() != 1 {
                // TODO(main_new)         return err_span(attr.span, "invalid verifier attribute");
                // TODO(main_new)     }
                // TODO(main_new)     let mut trees = trees.into_vec().into_iter();
                // TODO(main_new)     let tree: AttrTree = trees
                // TODO(main_new)         .next()
                // TODO(main_new)         .ok_or(vir_err_span_str(attr.span, "invalid verifier attribute"))?;
                // TODO(main_new)     Ok(Some((AttrPrefix::Verifier, attr.span, tree)))
                // TODO(main_new) }
                _ => return err_span(attr.span(), "invalid verifier attribute"),
            },
            [prefix_segment, segment] if prefix_segment.as_str() == "verifier" => {
                attr_args_to_tree(attr.span(), segment.to_string(), &item.args)
                    .map(|tree| Some((AttrPrefix::Verifier, attr.span(), tree)))
                    .map_err(|_| vir_err_span_str(attr.span(), "invalid verifier attribute"))
            }
            [prefix_segment, segment] if prefix_segment.as_str() == "verus" => {
                let name = segment.to_string();
                match &*name {
                    "internal" => match &item.args {
                        AttrArgs::Delimited(delim) => {
                            let trees: Box<[AttrTree]> =
                                token_stream_to_trees(attr.span(), &delim.tokens).map_err(
                                    |_| vir_err_span_str(attr.span(), "invalid verus attribute"),
                                )?;
                            if trees.len() != 1 {
                                return err_span(attr.span(), "invalid verus attribute");
                            }
                            let mut trees = trees.into_vec().into_iter();
                            let tree: AttrTree = trees.next().ok_or_else(|| {
                                vir_err_span_str(attr.span(), "invalid verus attribute")
                            })?;
                            Ok(Some((AttrPrefix::Verus(VerusPrefix::Internal), attr.span(), tree)))
                        }
                        _ => return err_span(attr.span(), "invalid verus attribute"),
                    },
                    _ => attr_args_to_tree(attr.span(), name, &item.args)
                        .map(|tree| Some((AttrPrefix::Verus(VerusPrefix::None), attr.span(), tree)))
                        .map_err(|_| vir_err_span_str(attr.span(), "invalid verifier attribute")),
                }
            }
            [segment]
                if segment.as_str() == "spec"
                    || segment.as_str() == "proof"
                    || segment.as_str() == "exec" =>
            {
                return err_span(
                    attr.span(),
                    "attributes spec, proof, exec are not supported anymore; use the verus! macro instead",
                );
            }
            [segment] if segment.as_str().starts_with("rustc_") => {
                if !RUSTC_ATTRS_OK_TO_IGNORE.contains(&segment.as_str()) {
                    Ok(Some((
                        AttrPrefix::Rustc,
                        attr.span(),
                        AttrTree::Fun(attr.span(), segment.as_str().into(), None),
                    )))
                } else {
                    Ok(None)
                }
            }
            _ => Ok(None),
        },
        _ => Ok(None),
    }
}

fn attrs_to_trees(attrs: &[Attribute]) -> Result<Vec<(AttrPrefix, Span, AttrTree)>, VirErr> {
    let mut attr_trees = Vec::new();
    for attr in attrs {
        if let Some(tree) = attr_to_tree(attr)? {
            attr_trees.push(tree);
        }
    }
    Ok(attr_trees)
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub(crate) enum GhostBlockAttr {
    Proof,
    GhostWrapped,
    TrackedWrapped,
    Tracked,
    Wrapper,
}

#[derive(Debug, PartialEq, Clone, Copy)]
pub(crate) enum AttrPublish {
    Open,
    Closed,
    Uninterp,
}

#[derive(Debug, PartialEq)]
pub(crate) enum Attr {
    // specify mode (spec, proof, exec)
    Mode(Mode),
    // special case in modes.rs
    InferMode,
    // function return mode (spec, proof, exec)
    ReturnMode(Mode),
    // generated by verus! macro
    VerusMacro,
    // parse function to get header, but don't verify body
    ExternalBody,
    // don't parse function; function can't be called directly from verified code
    External,
    // opposite of External; verify item even if it's declared without VerusMacro
    Verify,
    // hide body (from all modules) until revealed
    Opaque,
    // publish body?
    Publish(AttrPublish),
    // publish body with zero fuel
    OpaqueOutsideModule,
    // inline spec function in SMT query
    Inline,
    // generate ext_equal lemmas for datatype
    ExtEqual,
    // Rust ghost block
    GhostBlock(GhostBlockAttr),
    // proof block inside spec-mode code
    ProofInSpec,
    // Header to unwrap Tracked<T> and Ghost<T> parameters
    UnwrapParameter,
    // type parameter is not necessarily used in strictly positive positions
    RejectRecursiveTypes(Option<String>),
    // type parameter is used in strictly positive positions
    RejectGroundRecursiveTypes(Option<String>),
    // type parameter is used in strictly positive positions
    // and is not used by the ground variant
    AcceptRecursiveTypes(Option<String>),
    // export function's require/ensure as global forall
    BroadcastForall,
    // group together other BroadcastForall or RevealGroup
    RevealGroup,
    // this reveal_group is revealed by default when the group's crate is imported
    RevealedByDefaultWhenThisCrateIsImported,
    // accept the trigger chosen by triggers_auto without printing any diagnostics
    AutoTrigger,
    // accept all possible triggers chosen by triggers_auto without printing any diagnostics
    AllTriggers,
    // exclude a particular function from being chosen in a trigger by triggers_auto
    NoAutoTrigger,
    // when used in a ghost context, redirect to a specified spec method
    Autospec(String),
    // when used in a ghost context, redirect to the 'returns' clause
    AllowInSpec,
    // specify list of places where == is promoted to =~=
    AutoExtEqual(vir::ast::AutoExtEqual),
    // add manual trigger to expression inside quantifier
    Trigger(Option<Vec<u64>>),
    // custom error string to report for precondition failures
    CustomReqErr(String),
    // Add custom error message for expanded diagnostics (split expressions)
    CustomErr(String),
    // verify using bitvector theory
    BitVector,
    // for 'atomic' operations (e.g., CAS)
    Atomic,
    // specifies an invariant block
    InvariantBlock,
    // mark that a loop was desugared from a for-loop in the syntax macro
    ForLoop,
    // mark the syntax macro inserted a synthetic decreases into a desugared for-loop
    AutoDecreases,
    // this proof function is a termination proof
    DecreasesBy,
    // in a spec function, check the body for violations of recommends
    CheckRecommends,
    // set smt.arith.nl=true
    NonLinear,
    // verify non linear arithmetic using Singular
    IntegerRing,
    // Use a new dedicated Z3 process just for this query
    SpinoffProver,
    // Use a new dedicated Z3 process for loops
    LoopIsolation(bool),
    // Memoize function call results during interpretation
    Memoize,
    // Override default rlimit
    RLimit(f32),
    // Suppress the recommends check for narrowing casts that may truncate
    Truncate,
    // In order to apply a specification to a method externally
    ExternalFnSpecification,
    // In order to apply a specification to a datatype externally
    ExternalTypeSpecification,
    // In order to apply a specification to a trait externally
    // (the string is the name of the associated type pointing to the specified trait)
    ExternalTraitSpecification(String),
    // A trait or impl of a trait that extends an external_type_specification trait with ghost items
    ExternalTraitExtension(String, String),
    // Mark the blanket trait impl for the external_type_specification trait
    // (needed so that trait_conflicts.rs knows to ignore it.)
    ExternalTraitBlanket,
    // Any auto-derives for this type should be treated external
    ExternalAutoDerives(Option<std::collections::HashSet<String>>),
    // Marks a variable that's spec or ghost mode in exec code
    UnwrappedBinding,
    // Marks the auxiliary function constructed by reveal/hide
    InternalRevealFn,
    // Marks the auxiliary function constructed by spec const
    InternalConstBody,
    // Marks the auxiliary function constructed to wrap the ensures of a const
    InternalEnsuresWrapper,
    // Marks trusted code
    Trusted,
    // global size_of
    SizeOfGlobal,
    // reveal item
    ItemBroadcastUse,
    // reveal item in a broadcast use
    BroadcastUseReveal,
    // Marks generated -> functions that are unsupported because a field appears in multiple variants
    InternalGetFieldManyVariants,
    // Marks a trait as "sealed", i.e. not implementable in Verus code
    // requires it to also be marked `unsafe`
    Sealed,
    // Marks spec functions that depend on resolved prophecies
    ProphecyDependent,
    // Unrecognized attribute that starts with 'rustc_', internal to the stdlib
    UnsupportedRustcAttr(String, Span),
    // Broadcast proof for size_of global
    SizeOfBroadcastProof,
    // Is this a type_invariant spec function
    TypeInvariantFn,
    // Used for the encoding of `open([visibility qualified])`
    OpenVisibilityQualifier,
    // Allow the function to not have decreases clauses
    ExecAllowNoDecreasesClause,
    // Assume that the function terminates
    AssumeTermination,
    // Proxy containing unerased code
    UnerasedProxy,
    UsesUnerasedProxy,
    EncodedConst,
    EncodedStatic,
}

fn get_trigger_arg(span: Span, attr_tree: &AttrTree) -> Result<u64, VirErr> {
    let i = match attr_tree {
        AttrTree::Fun(_, name, None) => match name.parse::<u64>() {
            Ok(i) => Some(i),
            _ => None,
        },
        _ => None,
    };
    match i {
        Some(i) => Ok(i),
        None => err_span(span, format!("expected integer constant, found {:?}", &attr_tree)),
    }
}

pub(crate) fn parse_attrs(
    attrs: &[Attribute],
    mut diagnostics: Option<&mut Vec<VirErrAs>>,
) -> Result<Vec<Attr>, VirErr> {
    let diagnostics = &mut diagnostics;
    let mut v: Vec<Attr> = Vec::new();
    for (prefix, span, attr) in attrs_to_trees(attrs)? {
        let mut report_deprecated = |attr_name: &str, msg: &str| {
            if let Some(diagnostics) = diagnostics {
                diagnostics.push(VirErrAs::Warning(crate::util::err_span_bare(
                    span,
                    format!("#[verifier({attr_name})] is deprecated, {msg}"),
                )));
            }
        };

        match prefix {
            AttrPrefix::Verifier => match &attr {
                AttrTree::Fun(_, name, None) if name == "spec" => v.push(Attr::Mode(Mode::Spec)),
                AttrTree::Fun(_, name, Some(box [AttrTree::Fun(_, arg, None)]))
                    if name == "spec" && arg == "checked" =>
                {
                    v.push(Attr::Mode(Mode::Spec));
                    v.push(Attr::CheckRecommends);
                }
                AttrTree::Fun(_, name, None) if name == "proof" => v.push(Attr::Mode(Mode::Proof)),
                AttrTree::Fun(_, name, None) if name == "exec" => v.push(Attr::Mode(Mode::Exec)),
                AttrTree::Fun(_, name, None) if name == "trigger" => v.push(Attr::Trigger(None)),
                AttrTree::Fun(span, name, Some(args)) if name == "trigger" => {
                    let mut groups: Vec<u64> = Vec::new();
                    for arg in args.iter() {
                        groups.push(get_trigger_arg(*span, arg)?);
                    }
                    if groups.len() == 0 {
                        return err_span(
                            *span,
                            "expected either #[trigger] or non-empty #[trigger(...)]",
                        );
                    }
                    v.push(Attr::Trigger(Some(groups)));
                }
                AttrTree::Fun(_, name, None) if name == "auto_trigger" => v.push(Attr::AutoTrigger),
                AttrTree::Fun(_, name, None) if name == "all_triggers" => v.push(Attr::AllTriggers),
                AttrTree::Fun(_, arg, None) if arg == "verus_macro" => v.push(Attr::VerusMacro),
                AttrTree::Fun(_, arg, None) if arg == "external_body" => v.push(Attr::ExternalBody),
                AttrTree::Fun(_, arg, None) if arg == "external" => v.push(Attr::External),
                AttrTree::Fun(_, arg, None) if arg == "verify" => v.push(Attr::Verify),
                AttrTree::Fun(_, arg, None) if arg == "opaque" => v.push(Attr::Opaque),
                AttrTree::Fun(_, arg, None) if arg == "opaque_outside_module" => {
                    v.push(Attr::OpaqueOutsideModule)
                }
                AttrTree::Fun(_, arg, None) if arg == "inline" => v.push(Attr::Inline),
                AttrTree::Fun(_, arg, None) if arg == "ext_equal" => v.push(Attr::ExtEqual),
                AttrTree::Fun(_, arg, None) if arg == "proof_block" => {
                    v.push(Attr::GhostBlock(GhostBlockAttr::Proof))
                }
                AttrTree::Fun(_, arg, None) if arg == "ghost_block_wrapped" => {
                    v.push(Attr::GhostBlock(GhostBlockAttr::GhostWrapped))
                }
                AttrTree::Fun(_, arg, None) if arg == "tracked_block_wrapped" => {
                    v.push(Attr::GhostBlock(GhostBlockAttr::TrackedWrapped))
                }
                AttrTree::Fun(_, arg, None) if arg == "tracked_block" => {
                    v.push(Attr::GhostBlock(GhostBlockAttr::Tracked))
                }
                AttrTree::Fun(_, arg, None) if arg == "ghost_wrapper" => {
                    v.push(Attr::GhostBlock(GhostBlockAttr::Wrapper))
                }
                AttrTree::Fun(_, arg, None) if arg == "proof_in_spec" => v.push(Attr::ProofInSpec),
                // TODO: remove maybe_negative, strictly_positive
                AttrTree::Fun(_, arg, None)
                    if arg == "maybe_negative" || arg == "reject_recursive_types" =>
                {
                    v.push(Attr::RejectRecursiveTypes(None))
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, ident, None)]))
                    if arg == "reject_recursive_types" =>
                {
                    v.push(Attr::RejectRecursiveTypes(Some(ident.clone())))
                }
                AttrTree::Fun(_, arg, None)
                    if arg == "reject_recursive_types_in_ground_variants" =>
                {
                    v.push(Attr::RejectGroundRecursiveTypes(None))
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, ident, None)]))
                    if arg == "reject_recursive_types_in_ground_variants" =>
                {
                    v.push(Attr::RejectGroundRecursiveTypes(Some(ident.clone())))
                }
                AttrTree::Fun(_, arg, None)
                    if arg == "strictly_positive" || arg == "accept_recursive_types" =>
                {
                    v.push(Attr::AcceptRecursiveTypes(None))
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, ident, None)]))
                    if arg == "accept_recursive_types" =>
                {
                    v.push(Attr::AcceptRecursiveTypes(Some(ident.clone())))
                }
                AttrTree::Fun(_, arg, None) if arg == "broadcast_forall" => {
                    report_deprecated("broadcast_forall", "use `broadcast proof fn` instead");
                    v.push(Attr::BroadcastForall)
                }
                AttrTree::Fun(_, arg, None) if arg == "prune_unless_this_module_is_used" => {
                    report_deprecated("prune_unless_this_module_is_used", "this has no effect");
                }
                AttrTree::Fun(_, arg, None)
                    if arg == "broadcast_use_by_default_when_this_crate_is_imported" =>
                {
                    v.push(Attr::RevealedByDefaultWhenThisCrateIsImported)
                }
                AttrTree::Fun(_, arg, None) if arg == "no_auto_trigger" => {
                    v.push(Attr::NoAutoTrigger)
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, ident, None)]))
                    if arg == "when_used_as_spec" =>
                {
                    v.push(Attr::Autospec(ident.clone()))
                }
                AttrTree::Fun(_, arg, None) if arg == "allow_in_spec" => v.push(Attr::AllowInSpec),
                AttrTree::Fun(_, arg, None) if arg == "atomic" => v.push(Attr::Atomic),
                AttrTree::Fun(_, arg, None) if arg == "invariant_block" => {
                    v.push(Attr::InvariantBlock)
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, msg, None)]))
                    if arg == "custom_req_err" =>
                {
                    v.push(Attr::CustomReqErr(msg.clone()))
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, msg, None)]))
                    if arg == "custom_err" =>
                {
                    v.push(Attr::CustomErr(msg.clone()))
                }
                AttrTree::Fun(_, arg, None) if arg == "bit_vector" => v.push(Attr::BitVector),
                AttrTree::Fun(_, arg, None) if arg == "decreases_by" || arg == "recommends_by" => {
                    v.push(Attr::DecreasesBy)
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, name, None)]))
                    if arg == "returns" && name == "spec" =>
                {
                    v.push(Attr::ReturnMode(Mode::Spec))
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, name, None)]))
                    if arg == "returns" && name == "proof" =>
                {
                    v.push(Attr::ReturnMode(Mode::Proof))
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, name, None)]))
                    if arg == "returns" && name == "exec" =>
                {
                    v.push(Attr::ReturnMode(Mode::Exec))
                }
                AttrTree::Fun(_, arg, None) if arg == "integer_ring" => v.push(Attr::IntegerRing),
                AttrTree::Fun(_, arg, None) if arg == "nonlinear" => v.push(Attr::NonLinear),
                AttrTree::Fun(_, arg, None) if arg == "spinoff_prover" => {
                    v.push(Attr::SpinoffProver)
                }
                AttrTree::Fun(_, arg, None) if arg == "loop_isolation" => {
                    v.push(Attr::LoopIsolation(true))
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, r, None)]))
                    if arg == "loop_isolation" && r == "true" =>
                {
                    v.push(Attr::LoopIsolation(true))
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, r, None)]))
                    if arg == "loop_isolation" && r == "false" =>
                {
                    v.push(Attr::LoopIsolation(false))
                }
                AttrTree::Fun(span, arg, Some(places)) if arg == "auto_ext_equal" => {
                    let mut auto_ext_equal = vir::ast::AutoExtEqual {
                        assert: false,
                        assert_by: false,
                        ensures: false,
                        invariant: false,
                    };
                    for place in places.into_iter() {
                        if let AttrTree::Fun(_, r, None) = place {
                            match &**r {
                                "assert" => {
                                    auto_ext_equal.assert = true;
                                    continue;
                                }
                                "assert_by" => {
                                    auto_ext_equal.assert_by = true;
                                    continue;
                                }
                                "ensures" => {
                                    auto_ext_equal.ensures = true;
                                    continue;
                                }
                                "invariant" => {
                                    auto_ext_equal.invariant = true;
                                    continue;
                                }
                                _ => {}
                            }
                        }
                        return err_span(
                            *span,
                            "expected `assert`, `assert_by`, and/or `ensures` for auto_ext_equal",
                        );
                    }
                    v.push(Attr::AutoExtEqual(auto_ext_equal))
                }
                AttrTree::Fun(_, arg, None) if arg == "memoize" => v.push(Attr::Memoize),
                AttrTree::Fun(span, name, Some(box [AttrTree::Fun(_, r, None)]))
                    if name == "rlimit" =>
                {
                    let Some(rlimit) = r
                        .parse::<f32>()
                        .ok()
                        .or_else(|| if r == "infinity" { Some(f32::INFINITY) } else { None })
                    else {
                        return err_span(*span, "expected number, or `infinity` for rlimit");
                    };
                    v.push(Attr::RLimit(rlimit));
                }
                AttrTree::Fun(_, arg, None) if arg == "truncate" => v.push(Attr::Truncate),
                AttrTree::Fun(_, arg, None) if arg == "external_fn_specification" => {
                    v.push(Attr::ExternalFnSpecification)
                }
                AttrTree::Fun(_, arg, None) if arg == "external_type_specification" => {
                    v.push(Attr::ExternalTypeSpecification)
                }
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, r, None)]))
                    if arg == "external_derive" =>
                {
                    v.push(Attr::ExternalAutoDerives(Some(
                        r.split(",").map(|x| x.trim().to_owned()).collect(),
                    )));
                }
                AttrTree::Fun(_, arg, None) if arg == "external_derive" => {
                    v.push(Attr::ExternalAutoDerives(None));
                }
                AttrTree::Fun(_, arg, None) if arg == "external_trait_specification" => v.push(
                    Attr::ExternalTraitSpecification("ExternalTraitSpecificationFor".to_string()),
                ),
                AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, r, None)]))
                    if arg == "external_trait_specification" =>
                {
                    v.push(Attr::ExternalTraitSpecification(r.clone()))
                }
                AttrTree::Fun(
                    _,
                    arg,
                    Some(
                        box [
                            AttrTree::Fun(_, s, None),
                            AttrTree::Fun(_, via, None),
                            AttrTree::Fun(_, i, None),
                        ],
                    ),
                ) if arg == "external_trait_extension" && via == "via" => {
                    v.push(Attr::ExternalTraitExtension(s.clone(), i.clone()))
                }
                AttrTree::Fun(_, arg, None) if arg == "sealed" => v.push(Attr::Sealed),
                AttrTree::Fun(_, arg, None) if arg == "prophetic" => {
                    v.push(Attr::ProphecyDependent)
                }
                AttrTree::Fun(_, arg, None) if arg == "type_invariant" => {
                    v.push(Attr::TypeInvariantFn)
                }
                AttrTree::Fun(_, arg, None) if arg == "invalid_trigger_attribute" => {
                    return err_span(
                        span,
                        "invalid trigger attribute: to provide a trigger expression, use the #![trigger <expr>] attribute",
                    );
                }
                AttrTree::Fun(_, arg, None) if arg == "assume_termination" => {
                    v.push(Attr::AssumeTermination);
                }
                AttrTree::Fun(_, arg, None) if arg == "exec_allows_no_decreases_clause" => {
                    v.push(Attr::ExecAllowNoDecreasesClause);
                }
                _ => return err_span(span, "unrecognized verifier attribute"),
            },
            AttrPrefix::Verus(verus_prefix) => match verus_prefix {
                VerusPrefix::Internal => match &attr {
                    AttrTree::Fun(_, name, None) if name == "spec" => {
                        v.push(Attr::Mode(Mode::Spec))
                    }
                    AttrTree::Fun(_, name, Some(box [AttrTree::Fun(_, arg, None)]))
                        if name == "spec" && arg == "checked" =>
                    {
                        v.push(Attr::Mode(Mode::Spec));
                        v.push(Attr::CheckRecommends);
                    }
                    AttrTree::Fun(_, name, None) if name == "proof" => {
                        v.push(Attr::Mode(Mode::Proof))
                    }
                    AttrTree::Fun(_, name, None) if name == "exec" => {
                        v.push(Attr::Mode(Mode::Exec))
                    }
                    AttrTree::Fun(_, name, None) if name == "infer_mode" => v.push(Attr::InferMode),
                    AttrTree::Fun(_, name, None) if name == "trigger" => {
                        v.push(Attr::Trigger(None))
                    }
                    AttrTree::Fun(span, name, Some(args)) if name == "trigger" => {
                        let mut groups: Vec<u64> = Vec::new();
                        for arg in args.iter() {
                            groups.push(get_trigger_arg(*span, arg)?);
                        }
                        if groups.len() == 0 {
                            return err_span(
                                *span,
                                "expected either #[trigger] or non-empty #[trigger(...)]",
                            );
                        }
                        v.push(Attr::Trigger(Some(groups)));
                    }
                    AttrTree::Fun(_, name, None) if name == "auto_trigger" => {
                        v.push(Attr::AutoTrigger)
                    }
                    AttrTree::Fun(_, name, None) if name == "all_triggers" => {
                        v.push(Attr::AllTriggers)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "verus_macro" => v.push(Attr::VerusMacro),
                    AttrTree::Fun(_, arg, None) if arg == "proof_block" => {
                        v.push(Attr::GhostBlock(GhostBlockAttr::Proof))
                    }
                    AttrTree::Fun(_, arg, None) if arg == "external_body" => {
                        v.push(Attr::ExternalBody)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "external_trait_blanket" => {
                        v.push(Attr::ExternalTraitBlanket)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "open" => {
                        v.push(Attr::Publish(AttrPublish::Open))
                    }
                    AttrTree::Fun(_, arg, None) if arg == "closed" => {
                        v.push(Attr::Publish(AttrPublish::Closed))
                    }
                    AttrTree::Fun(_, arg, None) if arg == "uninterp" => {
                        v.push(Attr::Publish(AttrPublish::Uninterp))
                    }
                    AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, name, None)]))
                        if arg == "returns" && name == "spec" =>
                    {
                        v.push(Attr::ReturnMode(Mode::Spec))
                    }
                    AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, name, None)]))
                        if arg == "returns" && name == "proof" =>
                    {
                        v.push(Attr::ReturnMode(Mode::Proof))
                    }
                    AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, name, None)]))
                        if arg == "returns" && name == "exec" =>
                    {
                        v.push(Attr::ReturnMode(Mode::Exec))
                    }
                    AttrTree::Fun(_, arg, None) if arg == "reveal_group" => {
                        v.push(Attr::RevealGroup)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "header_unwrap_parameter" => {
                        v.push(Attr::UnwrapParameter)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "reveal_fn" => {
                        v.push(Attr::InternalRevealFn)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "const_body" => {
                        v.push(Attr::InternalConstBody)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "const_header_wrapper" => {
                        v.push(Attr::InternalEnsuresWrapper)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "broadcast_use_reveal" => {
                        v.push(Attr::BroadcastUseReveal)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "broadcast_forall" => {
                        v.push(Attr::BroadcastForall)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "for_loop" => v.push(Attr::ForLoop),
                    AttrTree::Fun(_, arg, None) if arg == "auto_decreases" => {
                        v.push(Attr::AutoDecreases)
                    }
                    AttrTree::Fun(_, arg, Some(box [AttrTree::Fun(_, ident, None)]))
                        if arg == "prover" =>
                    {
                        match &**ident {
                            "nonlinear_arith" => v.push(Attr::NonLinear),
                            "bit_vector" => v.push(Attr::BitVector),
                            "integer_ring" => v.push(Attr::IntegerRing),
                            _ => return err_span(span, "invalid prover"),
                        }
                    }
                    AttrTree::Fun(_, arg, None) if arg == "via" => v.push(Attr::DecreasesBy),
                    AttrTree::Fun(_, arg, None) if arg == "unwrapped_binding" => {
                        v.push(Attr::UnwrappedBinding)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "size_of" => v.push(Attr::SizeOfGlobal),
                    AttrTree::Fun(_, arg, None) if arg == "item_broadcast_use" => {
                        v.push(Attr::ItemBroadcastUse)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "get_field_many_variants" => {
                        v.push(Attr::InternalGetFieldManyVariants)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "size_of_broadcast_proof" => {
                        v.push(Attr::SizeOfBroadcastProof)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "external_fn_specification" => {
                        v.push(Attr::ExternalFnSpecification)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "open_visibility_qualifier" => {
                        v.push(Attr::OpenVisibilityQualifier)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "unerased_proxy" => {
                        v.push(Attr::UnerasedProxy)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "uses_unerased_proxy" => {
                        v.push(Attr::UsesUnerasedProxy)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "encoded_const" => {
                        v.push(Attr::EncodedConst)
                    }
                    AttrTree::Fun(_, arg, None) if arg == "encoded_static" => {
                        v.push(Attr::EncodedStatic)
                    }
                    _ => {
                        return err_span(span, "unrecognized internal attribute");
                    }
                },
                VerusPrefix::None => match &attr {
                    AttrTree::Fun(_, name, None) if name == "trusted" => v.push(Attr::Trusted),
                    _ => {
                        return err_span(span, "unrecognized internal attribute");
                    }
                },
            },
            AttrPrefix::Rustc => {
                let AttrTree::Fun(span, name, _) = &attr;
                v.push(Attr::UnsupportedRustcAttr(name.clone(), *span));
            }
        }
    }
    Ok(v)
}

pub(crate) fn parse_attrs_opt(
    attrs: &[Attribute],
    diagnostics: Option<&mut Vec<VirErrAs>>,
) -> Vec<Attr> {
    match parse_attrs(attrs, diagnostics) {
        Ok(attrs) => attrs,
        Err(_) => vec![],
    }
}

pub(crate) fn parse_attrs_walk_parents<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    mut def_id: rustc_span::def_id::DefId,
) -> Vec<Attr> {
    let mut vattrs: Vec<Attr> = Vec::new();
    loop {
        if let Some(did) = def_id.as_local() {
            let hir_id = tcx.local_def_id_to_hir_id(did);
            let attrs = tcx.hir_attrs(hir_id);
            vattrs.extend(parse_attrs_opt(attrs, None));
        }
        if let Some(id) = tcx.opt_parent(def_id) {
            def_id = id;
        } else {
            return vattrs;
        }
    }
}

pub(crate) fn get_loop_isolation_walk_parents<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    def_id: rustc_span::def_id::DefId,
) -> Option<bool> {
    for attr in parse_attrs_walk_parents(tcx, def_id) {
        if let Attr::LoopIsolation(flag) = attr {
            return Some(flag);
        }
    }
    None
}

pub(crate) fn get_auto_ext_equal_walk_parents<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    def_id: rustc_span::def_id::DefId,
) -> vir::ast::AutoExtEqual {
    for attr in parse_attrs_walk_parents(tcx, def_id) {
        if let Attr::AutoExtEqual(auto_ext_equal) = attr {
            return auto_ext_equal;
        }
    }
    vir::ast::AutoExtEqual::default()
}

pub(crate) fn get_allow_exec_allows_no_decreases_clause_walk_parents<'tcx>(
    tcx: rustc_middle::ty::TyCtxt<'tcx>,
    def_id: rustc_span::def_id::DefId,
) -> bool {
    for attr in parse_attrs_walk_parents(tcx, def_id) {
        if let Attr::ExecAllowNoDecreasesClause = attr {
            return true;
        }
    }
    false
}

pub(crate) fn get_ghost_block_opt(attrs: &[Attribute]) -> Option<GhostBlockAttr> {
    for attr in parse_attrs_opt(attrs, None) {
        match attr {
            Attr::GhostBlock(g) => return Some(g),
            _ => {}
        }
    }
    None
}

pub(crate) fn is_proof_in_spec(attrs: &[Attribute]) -> bool {
    for attr in parse_attrs_opt(attrs, None) {
        match attr {
            Attr::ProofInSpec => return true,
            _ => {}
        }
    }
    false
}

pub(crate) fn get_mode_opt(attrs: &[Attribute]) -> Option<Mode> {
    for attr in parse_attrs_opt(attrs, None) {
        match attr {
            Attr::Mode(m) => return Some(m),
            _ => {}
        }
    }
    None
}

pub(crate) fn get_mode(default_mode: Mode, attrs: &[Attribute]) -> Mode {
    get_mode_opt(attrs).unwrap_or(default_mode)
}

pub(crate) fn get_var_mode(function_mode: Mode, attrs: &[Attribute]) -> Mode {
    let default_mode = if function_mode == Mode::Proof { Mode::Spec } else { function_mode };
    get_mode(default_mode, attrs)
}

pub(crate) fn get_ret_mode(function_mode: Mode, attrs: &[Attribute]) -> Mode {
    let mut mode = get_var_mode(function_mode, &[]);
    for attr in parse_attrs_opt(attrs, None) {
        match attr {
            Attr::ReturnMode(m) => mode = m,
            _ => {}
        }
    }
    mode
}

pub(crate) fn get_trigger(attrs: &[Attribute]) -> Result<Vec<TriggerAnnotation>, VirErr> {
    let mut groups: Vec<TriggerAnnotation> = Vec::new();
    for attr in parse_attrs(attrs, None)? {
        match attr {
            Attr::AutoTrigger => groups.push(TriggerAnnotation::AutoTrigger),
            Attr::AllTriggers => groups.push(TriggerAnnotation::AllTriggers),
            Attr::Trigger(None) => groups.push(TriggerAnnotation::Trigger(None)),
            Attr::Trigger(Some(group_ids)) => {
                groups.extend(group_ids.into_iter().map(|id| TriggerAnnotation::Trigger(Some(id))));
            }
            _ => {}
        }
    }
    Ok(groups)
}

pub(crate) fn get_custom_err_annotations(attrs: &[Attribute]) -> Result<Vec<String>, VirErr> {
    let mut v = Vec::new();
    for attr in parse_attrs(attrs, None)? {
        match attr {
            Attr::CustomErr(s) => v.push(s),
            _ => {}
        }
    }
    Ok(v)
}

#[derive(Debug, Clone)]
pub(crate) enum AutoDerivesAttr {
    Regular,
    AllExternal,
    SomeExternal(std::collections::HashSet<String>),
}

// Only those relevant to classifying an item as external / not external
// (external_body is relevant because it means anything on the inside of the item should
// be external)
#[derive(Debug, Clone)]
pub(crate) struct ExternalAttrs {
    pub(crate) external: bool,
    pub(crate) external_body: bool,
    pub(crate) external_fn_specification: bool,
    pub(crate) external_type_specification: bool,
    pub(crate) external_trait_specification: bool,
    pub(crate) external_trait_blanket: bool,
    pub(crate) sets_mode: bool,
    pub(crate) verify: bool,
    pub(crate) verus_macro: bool,
    pub(crate) size_of_global: bool,
    pub(crate) any_other_verus_specific_attribute: bool,
    pub(crate) internal_get_field_many_variants: bool,
    pub(crate) external_auto_derives: AutoDerivesAttr,
    pub(crate) uses_unerased_proxy: bool,
}

#[derive(Debug)]
pub(crate) struct VerifierAttrs {
    pub(crate) verus_macro: bool,
    pub(crate) external_body: bool,
    pub(crate) opaque: bool,
    pub(crate) publish: Option<AttrPublish>,
    pub(crate) opaque_outside_module: bool,
    pub(crate) inline: bool,
    pub(crate) ext_equal: bool,
    // TODO: get rid of *_recursive_types: bool
    pub(crate) reject_recursive_types_in_ground_variants: bool,
    pub(crate) reject_recursive_types: bool,
    pub(crate) accept_recursive_types: bool,
    pub(crate) accept_recursive_type_list: Vec<(String, AcceptRecursiveType)>,
    pub(crate) broadcast_forall: bool,
    pub(crate) reveal_group: bool,
    pub(crate) broadcast_use_by_default_when_this_crate_is_imported: bool,
    pub(crate) no_auto_trigger: bool,
    pub(crate) autospec: Option<String>,
    pub(crate) allow_in_spec: bool,
    pub(crate) custom_req_err: Option<String>,
    pub(crate) bit_vector: bool,
    pub(crate) for_loop: bool,
    pub(crate) auto_decreases: bool,
    pub(crate) atomic: bool,
    pub(crate) integer_ring: bool,
    pub(crate) decreases_by: bool,
    pub(crate) check_recommends: bool,
    pub(crate) nonlinear: bool,
    pub(crate) spinoff_prover: bool,
    pub(crate) loop_isolation: Option<bool>,
    pub(crate) memoize: bool,
    pub(crate) rlimit: Option<f32>,
    pub(crate) truncate: bool,
    pub(crate) external_fn_specification: bool,
    pub(crate) external_type_specification: bool,
    pub(crate) external_trait_specification: Option<String>,
    pub(crate) external_trait_extension: Option<(String, String)>,
    pub(crate) external_trait_blanket: bool,
    pub(crate) unwrapped_binding: bool,
    pub(crate) sets_mode: bool,
    pub(crate) internal_reveal_fn: bool,
    pub(crate) internal_const_body: bool,
    pub(crate) internal_const_header_wrapper: bool,
    pub(crate) broadcast_use_reveal: bool,
    pub(crate) trusted: bool,
    pub(crate) internal_get_field_many_variants: bool,
    pub(crate) size_of_global: bool,
    pub(crate) sealed: bool,
    pub(crate) prophecy_dependent: bool,
    pub(crate) item_broadcast_use: bool,
    pub(crate) size_of_broadcast_proof: bool,
    pub(crate) type_invariant_fn: bool,
    pub(crate) open_visibility_qualifier: bool,
    pub(crate) assume_termination: bool,
    pub(crate) exec_allows_no_decreases_clause: bool,
    pub(crate) unerased_proxy: bool,
    pub(crate) encoded_const: bool,
    pub(crate) encoded_static: bool,
}

// Check for the `get_field_many_variants` attribute
// Skips additional checks that are meant to be applied only during the 'main' processing
// of an item.
pub(crate) fn is_get_field_many_variants(
    attrs: &[Attribute],
    diagnostics: Option<&mut Vec<VirErrAs>>,
) -> Result<bool, VirErr> {
    for attr in parse_attrs(attrs, diagnostics)? {
        match attr {
            Attr::InternalGetFieldManyVariants => {
                return Ok(true);
            }
            _ => {}
        }
    }
    Ok(false)
}

// Check for the `sealed` attribute
// Skips additional checks that are meant to be applied only during the 'main' processing
// of an item.
pub(crate) fn is_sealed(
    attrs: &[Attribute],
    diagnostics: Option<&mut Vec<VirErrAs>>,
) -> Result<bool, VirErr> {
    for attr in parse_attrs(attrs, diagnostics)? {
        match attr {
            Attr::Sealed => {
                return Ok(true);
            }
            _ => {}
        }
    }
    Ok(false)
}

/// Get the attributes needed to determine if the item is external.
/// or needed to determine properties of external items.
pub(crate) fn get_external_attrs(
    attrs: &[Attribute],
    diagnostics: Option<&mut Vec<VirErrAs>>,
) -> Result<ExternalAttrs, VirErr> {
    let mut es = ExternalAttrs {
        external_body: false,
        external_fn_specification: false,
        external_type_specification: false,
        external_trait_specification: false,
        external_trait_blanket: false,
        external: false,
        verify: false,
        sets_mode: false,
        verus_macro: false,
        size_of_global: false,
        any_other_verus_specific_attribute: false,
        internal_get_field_many_variants: false,
        external_auto_derives: AutoDerivesAttr::Regular,
        uses_unerased_proxy: false,
    };

    for attr in parse_attrs(attrs, diagnostics)? {
        match attr {
            Attr::ExternalBody => es.external_body = true,
            Attr::ExternalFnSpecification => es.external_fn_specification = true,
            Attr::ExternalTypeSpecification => es.external_type_specification = true,
            Attr::ExternalTraitSpecification(_) => es.external_trait_specification = true,
            Attr::External => es.external = true,
            Attr::Verify => es.verify = true,
            Attr::Mode(_) => es.sets_mode = true,
            Attr::VerusMacro => es.verus_macro = true,
            Attr::SizeOfGlobal => es.size_of_global = true,
            Attr::InternalGetFieldManyVariants => es.internal_get_field_many_variants = true,
            Attr::Trusted => {}
            Attr::ExternalTraitBlanket => es.external_trait_blanket = true,
            Attr::ExternalAutoDerives(None) => {
                es.external_auto_derives = AutoDerivesAttr::AllExternal
            }
            Attr::ExternalAutoDerives(Some(external_auto_derives)) => {
                es.external_auto_derives = AutoDerivesAttr::SomeExternal(external_auto_derives)
            }
            Attr::UsesUnerasedProxy => es.uses_unerased_proxy = true,
            Attr::UnsupportedRustcAttr(..) => {}
            _ => {
                es.any_other_verus_specific_attribute = true;
            }
        }
    }

    return Ok(es);
}

pub(crate) fn get_verifier_attrs(
    attrs: &[Attribute],
    diagnostics: Option<&mut Vec<VirErrAs>>,
) -> Result<VerifierAttrs, VirErr> {
    get_verifier_attrs_maybe_check(attrs, diagnostics, true)
}

pub(crate) fn get_verifier_attrs_no_check(
    attrs: &[Attribute],
    diagnostics: Option<&mut Vec<VirErrAs>>,
) -> Result<VerifierAttrs, VirErr> {
    get_verifier_attrs_maybe_check(attrs, diagnostics, false)
}

pub(crate) fn get_verifier_attrs_maybe_check(
    attrs: &[Attribute],
    diagnostics: Option<&mut Vec<VirErrAs>>,
    do_check: bool,
) -> Result<VerifierAttrs, VirErr> {
    let mut vs = VerifierAttrs {
        verus_macro: false,
        external_body: false,
        opaque: false,
        publish: None,
        opaque_outside_module: false,
        inline: false,
        ext_equal: false,
        reject_recursive_types: false,
        reject_recursive_types_in_ground_variants: false,
        accept_recursive_types: false,
        accept_recursive_type_list: vec![],
        broadcast_forall: false,
        reveal_group: false,
        broadcast_use_by_default_when_this_crate_is_imported: false,
        no_auto_trigger: false,
        autospec: None,
        allow_in_spec: false,
        custom_req_err: None,
        bit_vector: false,
        for_loop: false,
        auto_decreases: false,
        atomic: false,
        integer_ring: false,
        decreases_by: false,
        check_recommends: false,
        nonlinear: false,
        spinoff_prover: false,
        loop_isolation: None,
        memoize: false,
        rlimit: None,
        truncate: false,
        external_fn_specification: false,
        external_type_specification: false,
        external_trait_specification: None,
        external_trait_extension: None,
        external_trait_blanket: false,
        unwrapped_binding: false,
        sets_mode: false,
        internal_reveal_fn: false,
        internal_const_body: false,
        internal_const_header_wrapper: false,
        broadcast_use_reveal: false,
        trusted: false,
        size_of_global: false,
        internal_get_field_many_variants: false,
        sealed: false,
        prophecy_dependent: false,
        item_broadcast_use: false,
        size_of_broadcast_proof: false,
        type_invariant_fn: false,
        open_visibility_qualifier: false,
        assume_termination: false,
        exec_allows_no_decreases_clause: false,
        unerased_proxy: false,
        encoded_const: false,
        encoded_static: false,
    };
    let mut unsupported_rustc_attr: Option<(String, Span)> = None;
    for attr in parse_attrs(attrs, diagnostics)? {
        match attr {
            Attr::VerusMacro => vs.verus_macro = true,
            Attr::ExternalBody => vs.external_body = true,
            Attr::ExternalFnSpecification => vs.external_fn_specification = true,
            Attr::ExternalTypeSpecification => vs.external_type_specification = true,
            Attr::ExternalTraitSpecification(assoc) => {
                vs.external_trait_specification = Some(assoc.clone())
            }
            Attr::ExternalTraitExtension(s, i) => vs.external_trait_extension = Some((s, i)),
            Attr::ExternalTraitBlanket => vs.external_trait_blanket = true,
            Attr::Opaque => vs.opaque = true,
            Attr::Publish(open) => vs.publish = Some(open),
            Attr::OpaqueOutsideModule => vs.opaque_outside_module = true,
            Attr::Inline => vs.inline = true,
            Attr::ExtEqual => vs.ext_equal = true,
            Attr::RejectRecursiveTypes(None) => vs.reject_recursive_types = true,
            Attr::RejectRecursiveTypes(Some(s)) => {
                vs.accept_recursive_type_list.push((s, AcceptRecursiveType::Reject))
            }
            Attr::RejectGroundRecursiveTypes(None) => {
                vs.reject_recursive_types_in_ground_variants = true
            }
            Attr::RejectGroundRecursiveTypes(Some(s)) => {
                vs.accept_recursive_type_list.push((s, AcceptRecursiveType::RejectInGround))
            }
            Attr::AcceptRecursiveTypes(None) => vs.accept_recursive_types = true,
            Attr::AcceptRecursiveTypes(Some(s)) => {
                vs.accept_recursive_type_list.push((s, AcceptRecursiveType::Accept))
            }
            Attr::BroadcastForall => vs.broadcast_forall = true,
            Attr::RevealGroup => vs.reveal_group = true,
            Attr::RevealedByDefaultWhenThisCrateIsImported => {
                vs.broadcast_use_by_default_when_this_crate_is_imported = true
            }
            Attr::NoAutoTrigger => vs.no_auto_trigger = true,
            Attr::Autospec(method_ident) => vs.autospec = Some(method_ident),
            Attr::AllowInSpec => vs.allow_in_spec = true,
            Attr::CustomReqErr(s) => vs.custom_req_err = Some(s.clone()),
            Attr::BitVector => vs.bit_vector = true,
            Attr::ForLoop => vs.for_loop = true,
            Attr::AutoDecreases => vs.auto_decreases = true,
            Attr::Atomic => vs.atomic = true,
            Attr::IntegerRing => vs.integer_ring = true,
            Attr::DecreasesBy => vs.decreases_by = true,
            Attr::CheckRecommends => vs.check_recommends = true,
            Attr::NonLinear => vs.nonlinear = true,
            Attr::SpinoffProver => vs.spinoff_prover = true,
            Attr::LoopIsolation(flag) => vs.loop_isolation = Some(flag),
            Attr::Memoize => vs.memoize = true,
            Attr::RLimit(rlimit) => vs.rlimit = Some(rlimit),
            Attr::Truncate => vs.truncate = true,
            Attr::UnwrappedBinding => vs.unwrapped_binding = true,
            Attr::Mode(_) => vs.sets_mode = true,
            Attr::InternalRevealFn => vs.internal_reveal_fn = true,
            Attr::InternalConstBody => vs.internal_const_body = true,
            Attr::InternalEnsuresWrapper => vs.internal_const_header_wrapper = true,
            Attr::BroadcastUseReveal => vs.broadcast_use_reveal = true,
            Attr::Trusted => vs.trusted = true,
            Attr::SizeOfGlobal => vs.size_of_global = true,
            Attr::ItemBroadcastUse => vs.item_broadcast_use = true,
            Attr::InternalGetFieldManyVariants => vs.internal_get_field_many_variants = true,
            Attr::Sealed => vs.sealed = true,
            Attr::ProphecyDependent => vs.prophecy_dependent = true,
            Attr::UnsupportedRustcAttr(name, span) => {
                unsupported_rustc_attr = Some((name.clone(), span))
            }
            Attr::SizeOfBroadcastProof => vs.size_of_broadcast_proof = true,
            Attr::TypeInvariantFn => vs.type_invariant_fn = true,
            Attr::OpenVisibilityQualifier => vs.open_visibility_qualifier = true,
            Attr::AssumeTermination => vs.assume_termination = true,
            Attr::ExecAllowNoDecreasesClause => vs.exec_allows_no_decreases_clause = true,
            Attr::UnerasedProxy => vs.unerased_proxy = true,
            Attr::EncodedConst => vs.encoded_const = true,
            Attr::EncodedStatic => vs.encoded_static = true,
            Attr::UsesUnerasedProxy => {}
            _ => {}
        }
    }
    if do_check {
        if let Some((rustc_attr, span)) = unsupported_rustc_attr {
            return err_span(span, format!("The attribute `{rustc_attr:}` is not supported"));
        }
    }
    Ok(vs)
}

// Rust has a bunch of internal attributes it uses for the standard library,
// all of which start with "rustc_". They greatly vary in how interesting they
// are to Verus. Some are effectively 'unsafe', while others have to do with
// versioning or diagnostics and have nothing to do with semantics.
//
// Therefore, if we encounter any "rustc_" attribute, we will always error, unless either:
//  - It is explicitly allowed, in the RUSTC_ATTRS_OK_TO_IGNORE list, or
//  - We have carefully considered what it does and made sure Verus has relevant support.
//
// Here are some attributes not in the OK list, which require additional consideration
// or investigation:
//
// rustc_deny_explicit_impl: given to marker traits, which probably should be kept 'external' anyway
// rustc_coinductive
// rustc_nounwind
// rustc_promotable (see https://github.com/rust-lang/const-eval/blob/master/promotion.md)
// rustc_reservation_impl (see https://github.com/rust-lang/rust/issues/64631)
// rustc_never_returns_null_ptr
// rustc_nonnull_optimization_guaranteed
// rustc_safe_intrinsic
// rustc_const_panic_str
// rustc_do_not_const_check
// rustc_has_incoherent_inherent_impls
// rustc_inherit_overflow_checks
// rustc_layout_scalar_valid_range_end
// rustc_layout_scalar_valid_range_start
// rustc_skip_array_during_method_dispatch
// rustc_specialization_trait
// rustc_unsafe_specialization_marker
//
// More complete list of rustc attrs:
// https://doc.rust-lang.org/stable/nightly-rustc/src/rustc_feature/builtin_attrs.rs.html#539

pub const RUSTC_ATTRS_OK_TO_IGNORE: &[&str] = &[
    // Related to stability:
    // https://rustc-dev-guide.rust-lang.org/stability.html
    "rustc_allow_const_fn_unstable",
    "rustc_const_stable",
    "rustc_const_unstable",
    "rustc_allowed_through_unstable_modules",
    // Macros
    "rustc_builtin_macro",
    "rustc_macro_transparency",
    // This is a crate-level attribute on the stdlib
    "rustc_coherence_is_core",
    // Diagnostics
    "rustc_diagnostic_item",
    "rustc_on_unimplemented",
    "rustc_trivial_field_reads",
    // Docs
    "rustc_doc_primitive",
    // Syntax-related
    "rustc_paren_sugar",
    // This has to do with the an edition migration, so not really in scope
    // for verification.
    // https://rust-lang.github.io/rfcs/2229-capture-disjoint-fields.html
    "rustc_insignificant_dtor",
    // Boxes
    "rustc_box",
];
