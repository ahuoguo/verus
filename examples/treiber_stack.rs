#![verifier::exec_allows_no_decreases_clause]
#![verifier::loop_isolation(false)]

use vstd::prelude::*;
use vstd::atomic::*;
use vstd::invariant::*;
use vstd::simple_pptr::*;
use vstd::modes::tracked_swap;
use vstd::resource::*;
use vstd::resource::pcm::*;
use vstd::resource::map::*;
use vstd::resource::exclusive::*;
use vstd::resource::auth::*;
use vstd::resource::relations::*;
use vstd::resource::algebra::ResourceAlgebra;
use vstd::shared::*;

verus! {

// ============================================================================
// Ghsot State Construction for Trieber Stack
//
//   ● Excl' xs  (authoritative, in the invariant)  = StackAuth
//   ◯ Excl' xs  (fragment, the client's token)     = StackFrag
//
// with the two POPL'18-tutorial lemmas reproved from the combinators:
//   auth_agree  : ● xs ∗ ◯ ys ⊢ ⌜xs = ys⌝
//   auth_update : ● xs ∗ ◯ ys ==∗ ● zs ∗ ◯ zs
// ============================================================================

// optionUR (exclR (listO valO))
pub type Inner = Option<ExclusiveRA<Seq<u64>>>;
// authR (optionUR (exclR (listO valO)))
pub type StackGS = AuthRA< Option<ExclusiveRA<Seq<u64>>>>;

pub open spec fn auth_val(xs: Seq<u64>) -> StackGS {
    AuthRA { auth: Some(ExclusiveRA::Exclusive(Some(ExclusiveRA::Exclusive(xs)))), frac: None }
}

pub open spec fn frag_val(xs: Seq<u64>) -> StackGS {
    AuthRA { auth: None, frac: Some(ExclusiveRA::Exclusive(xs)) }
}

// `● xs ⋅ ◯ ys` — proved (by computation) equal to the composition below, so we
// define it that way and let the two helper lemmas do all the algebra once.
pub open spec fn both_val(xs: Seq<u64>, ys: Seq<u64>) -> StackGS {
    StackGS::op(auth_val(xs), frag_val(ys))
}

// `● xs ⋅ ◯ xs` is valid: the fragment `Some(Excl xs)` is (trivially) included in
// the authority's `Some(Excl xs)` via the unit witness.
pub proof fn both_valid(xs: Seq<u64>)
    ensures both_val(xs, xs).valid(),
{
    Some(ExclusiveRA::<Seq<u64>>::Exclusive(xs)).op_unit();
}

// `● xs ⋅ ◯ ys` valid ==> xs == ys.
pub proof fn both_valid_implies_eq(xs: Seq<u64>, ys: Seq<u64>)
    requires both_val(xs, ys).valid(),
    ensures xs == ys,
{
    let c = choose|c: Inner| Inner::op(Some(ExclusiveRA::Exclusive(ys)), c) == Some(ExclusiveRA::Exclusive(xs));
    Some(ExclusiveRA::<Seq<u64>>::Exclusive(ys)).op_unit();  // handles c == None
}

pub tracked struct StackAuth {
    tracked r: Resource<StackGS>,
    ghost val: Seq<u64>,
}

pub tracked struct StackFrag {
    tracked r: Resource<StackGS>,
    ghost val: Seq<u64>,
}

impl StackAuth {
    #[verifier::type_invariant]
    closed spec fn wf(self) -> bool { self.r.value() == auth_val(self.val) }
    pub closed spec fn id(self) -> Loc { self.r.loc() }
    pub closed spec fn view(self) -> Seq<u64> { self.val }
}
impl StackFrag {
    #[verifier::type_invariant]
    closed spec fn wf(self) -> bool { self.r.value() == frag_val(self.val) }
    pub closed spec fn id(self) -> Loc { self.r.loc() }
    pub closed spec fn view(self) -> Seq<u64> { self.val }
}

// own_alloc (● Excl' xs ⋅ ◯ Excl' xs)  (treiber2.v line 218)
pub proof fn auth_frag_new(xs: Seq<u64>) -> (tracked out: (StackAuth, StackFrag))
    ensures out.0.id() == out.1.id(), out.0.view() == xs, out.1.view() == xs,
{
    both_valid(xs);
    let tracked r = Resource::<StackGS>::alloc(both_val(xs, xs));
    let tracked (ra, rf) = r.split(auth_val(xs), frag_val(xs));
    (StackAuth { r: ra, val: xs }, StackFrag { r: rf, val: xs })
}

// auth_agree (treiber2.v lines 150-155)
pub proof fn auth_agree(tracked a: &mut StackAuth, tracked f: &StackFrag)
    requires old(a).id() == f.id(),
    ensures *final(a) == *old(a), old(a).view() == f.view(),
{
    use_type_invariant(&*a);
    use_type_invariant(f);
    a.r.validate_2(&f.r);
    both_valid_implies_eq(a.val, f.val);
}

// exclusive_local_update: `● xs ⋅ ◯ ys ⇝ ● zs ⋅ ◯ zs`.
// A valid frame `c` must be the unit on both components (any real `Excl` frame
// composes to `Invalid`), so the update preserves any frame.
pub proof fn both_frame_preserving(xs: Seq<u64>, ys: Seq<u64>, zs: Seq<u64>)
    ensures frame_preserving_update::<StackGS>(both_val(xs, ys), both_val(zs, zs)),
{
    both_valid(zs);
    assert forall|c: StackGS|
        #![trigger StackGS::op(both_val(xs, ys), c), StackGS::op(both_val(zs, zs), c)]
        StackGS::op(both_val(xs, ys), c).valid()
        implies StackGS::op(both_val(zs, zs), c).valid() by {
        // c.auth == None (else auth-component is Some(Invalid)); c.frac == None likewise.
        assert(c.auth is None && c.frac is None);
        StackGS::op(both_val(zs, zs), c).op_unit();
    }
}

// auth_update (treiber2.v lines 158-167)
pub proof fn auth_update(tracked a: &mut StackAuth, tracked f: &mut StackFrag, zs: Seq<u64>)
    requires old(a).id() == old(f).id(),
    ensures
        final(a).id() == old(a).id(), final(f).id() == old(f).id(),
        final(a).view() == zs, final(f).view() == zs,
{
    use_type_invariant(&*a);
    use_type_invariant(&*f);
    // Swap out originals behind fresh VALID placeholders (mirrors GhostVarAuth::update).
    let tracked (mut ra, mut rf) = auth_frag_new(a.val);
    tracked_swap(a, &mut ra);
    tracked_swap(f, &mut rf);
    use_type_invariant(&ra);
    use_type_invariant(&rf);
    ra.r.validate_2(&rf.r);
    both_valid_implies_eq(ra.val, rf.val);
    let tracked joined = ra.r.join(rf.r);
    both_frame_preserving(ra.val, rf.val, zs);
    let tracked updated = joined.update(both_val(zs, zs));
    let tracked (na, nf) = updated.split(auth_val(zs), frag_val(zs));
    tracked_swap(a, &mut StackAuth { r: na, val: zs });
    tracked_swap(f, &mut StackFrag { r: nf, val: zs });
}

// TODO: we treat address 0 as None, it doesn't seem like I can get `Option<usize>` to work
pub struct Node {
    pub val: u64,
    pub next: usize,
}

// TODO: Verus's size_of is uninterpreted for user structs
// https://github.com/verus-lang/verus/issues/2633
global layout Node is size == 16;

/// ghost linked-list predicate
pub open spec fn is_stack_list(
    head: usize, xs: Seq<u64>, nodes: Map<usize, Node>,
) -> bool
    decreases xs.len(),
{
    if xs.len() == 0 { head == 0 }
    else {
        &&& head != 0
        &&& nodes.dom().contains(head)
        &&& nodes[head].val == xs[0]
        &&& is_stack_list(nodes[head].next, xs.subrange(1, xs.len() as int), nodes)
    }
}

proof fn lemma_is_stack_list_mono(
    head: usize, xs: Seq<u64>,
    nodes: Map<usize, Node>, nodes2: Map<usize, Node>,
)
    requires
        is_stack_list(head, xs, nodes),
        forall|k: usize| #[trigger] nodes.dom().contains(k)
            ==> nodes2.dom().contains(k) && nodes2[k] == nodes[k],
    ensures is_stack_list(head, xs, nodes2),
    decreases xs.len(),
{
    if xs.len() > 0 {
        assert(nodes.dom().contains(head));
        assert(nodes2.dom().contains(head) && nodes2[head] == nodes[head]);
        lemma_is_stack_list_mono(nodes[head].next, xs.subrange(1, xs.len() as int), nodes, nodes2);
    }
}

proof fn lemma_is_stack_list_push(
    old_head: usize, new_head: usize, val: u64,
    xs: Seq<u64>, nodes: Map<usize, Node>, ni: Node,
)
    requires
        new_head != 0, !nodes.dom().contains(new_head),
        is_stack_list(old_head, xs, nodes),
        ni.val == val, ni.next == old_head,
    ensures is_stack_list(new_head, seq![val].add(xs), nodes.insert(new_head, ni)),
{
    let new_nodes = nodes.insert(new_head, ni);
    assert forall|k: usize| #[trigger] nodes.dom().contains(k)
        implies new_nodes.dom().contains(k) && new_nodes[k] == nodes[k] by {}
    lemma_is_stack_list_mono(old_head, xs, nodes, new_nodes);
    assert(seq![val].add(xs).subrange(1, seq![val].add(xs).len() as int) =~= xs);
}

proof fn lemma_is_stack_list_pop(
    head: usize, xs: Seq<u64>, nodes: Map<usize, Node>,
)
    requires is_stack_list(head, xs, nodes), xs.len() > 0,
    ensures
        is_stack_list(nodes[head].next, xs.subrange(1, xs.len() as int), nodes),
        nodes[head].val == xs[0],
{}

// Well-formedness of one merged node token at address `addr`, against node map `m`.
// encoding `ℓ ↦□ (x, to_val r)`
pub open spec fn node_tok_wf(
    addr: usize,
    tok: Shared<(PointsTo<Node>, GhostPersistentPointsTo<usize, Node>)>,
    node_map_id: Loc,
    m: Map<usize, Node>,
) -> bool {
    &&& tok@.0.pptr().addr() == addr           // read token points at `addr`
    &&& tok@.0.is_init()
    &&& tok@.0.value() == m[addr]              // read token holds the node's contents
    &&& tok@.1.id() == node_map_id
    &&& tok@.1@ == (addr, m[addr])             // tok has same context as node_map
}

// Definition phys_stack (ℓ : loc) (xs : list val) : iProp :=
//   (∃ r, ℓ ↦ to_val r ∗ phys_list r xs)%I.

// Definition stack_inv (ℓ : loc) (γ : gname) : iProp :=
//   (∃ xs, phys_stack ℓ xs ∗ own γ (● (Some ((Excl xs)))))%I.

/// One duplicable per-node token,
/// `Shared<(PointsTo<Node>, GhostPersistentPointsTo<usize, Node>)>`,
/// bundles the physical read permission (↦□) with the persistent value fragment
/// (pointsto_agree).
pub struct StackInv {
    pub head_perm: PermissionUsize,
    // own γ (● Excl xs)
    pub auth: StackAuth,
    // The following two together encode the list of persistent cells
    // `ℓ ↦□ (x, to_val r)` that `phys_list` owns (treiber2.v line 93).
    // TODO: explain why `node_map` is not duplicate information since there's also `toks`
    pub node_map: GhostMapAuth<usize, Node>,
    // One duplicable token per node = the Verus reconstruction of `ℓ ↦□ (x, r)`:
    //   .0 : PointsTo<Node>                    -- physical read capability (the ↦ part)
    //   .1 : GhostPersistentPointsTo<...>      -- persistent value fragment of node_map (the □ part)
    // `Shared<_>` gives the duplicability that `↦□`'s persistence provides.
    pub toks: Map<usize, Shared<(PointsTo<Node>, GhostPersistentPointsTo<usize, Node>)>>,
}

// patomic_id <-> (ℓ : loc) 
// Loc <-> (γ : gname) 
pub struct StackConst {
    pub patomic_id: int,
    // gname for StackAuth/StackFrag, for the abstract state
    pub ghost_var_id: Loc,
    // gname for node_map/toks
    pub node_map_id: Loc,
}

// The setack invariant mask
pub open spec const STACK_NS: int = 1234;

// final wrapping to connect ℓ and γ to the invariant
pub struct StackInvPred;
impl InvariantPredicate<StackConst, StackInv> for StackInvPred {
    open spec fn inv(k: StackConst, v: StackInv) -> bool {
        let StackConst { patomic_id, ghost_var_id, node_map_id } = k;
        let StackInv { head_perm, auth, node_map, toks } = v;
        &&& head_perm@.patomic == patomic_id
        &&& auth.id() == ghost_var_id
        &&& node_map.id() == node_map_id
        &&& is_stack_list(head_perm@.value, auth.view(), node_map@)
        &&& toks.dom() =~= node_map@.dom()
        &&& forall|addr: usize| #[trigger] node_map@.dom().contains(addr)
            ==> node_tok_wf(addr, toks[addr], node_map_id, node_map@)
    }
}

// a stack is just a pointer
pub struct TreiberStack {
    pub head: PAtomicUsize,
    // same as `is_stack` in treiber2.v
    pub inv: Tracked<AtomicInvariant<StackConst, StackInv, StackInvPred>>,
}

// Definition stack_cont (γ : gname) (xs : list val) : iProp :=
//     (own γ (◯ (Some ((Excl xs)))))%I.
pub tracked struct StackContent {
    pub cont: StackFrag,
}

impl StackContent {
    pub open spec fn id(self) -> Loc { self.cont.id() }
    pub open spec fn view(self) -> Seq<u64> { self.cont.view() }
    pub open spec fn is_for(self, s: TreiberStack) -> bool { self.id() == s.ghost_var_id() }
}

impl TreiberStack {
    pub open spec fn wf(self) -> bool {
        &&& self.head.id() == self.inv@.constant().patomic_id
        &&& self.inv@.namespace() == STACK_NS
    }
    pub open spec fn ghost_var_id(self) -> Loc { self.inv@.constant().ghost_var_id }
}

type PushAU = AtomicUpdate<StackContent, Result<Commit<StackContent>, (StackContent, OpenInvariantCredit)>, PushAtomicUpdatePredicate>;
type PopAU = AtomicUpdate<StackContent, Result<Commit<StackContent>, (StackContent, OpenInvariantCredit)>, PopAtomicUpdatePredicate>;

impl TreiberStack {
    // {{{ True }}}
    //   new_stack #()
    // {{{ ℓ γ, RET #ℓ; is_stack ℓ γ ∗ stack_cont γ [] }}}.
    pub fn new() -> (out: (TreiberStack, Tracked<StackContent>))
        ensures 
            // is_stack ℓ γ
            out.0.wf(), 
            out.1@.is_for(out.0), 
            out.1@@ =~= Seq::<u64>::empty(),
    {
        // we treat address 0 as None
        let (head, Tracked(head_perm)) = PAtomicUsize::new(0);
        let tracked (gv_a, gv_f) = auth_frag_new(Seq::empty());
        let tracked (node_map, _submap) = GhostMapAuth::<usize, Node>::new(Map::empty());
        let ghost k = StackConst {
            patomic_id: head.id(),
            ghost_var_id: gv_a.id(),
            node_map_id: node_map.id(),
        };
        let tracked state = StackInv {
            head_perm, 
            auth: gv_a, 
            node_map, 
            toks: Map::tracked_empty(),
        };
        let tracked inv = AtomicInvariant::<StackConst, StackInv, StackInvPred>::new(k, state, STACK_NS);
        (TreiberStack { head, inv: Tracked(inv) }, Tracked(StackContent { cont: gv_f }))
    }
}

impl TreiberStack {
    pub fn push(&self, val: u64)
        atomically (atomic_update) {
            (token: StackContent)
                -> (res: Result<Commit<StackContent>, (StackContent, OpenInvariantCredit)>),
            requires token.id() == self.ghost_var_id(),
            ensures match res {
                Err((t, _)) => t == token,
                Ok(commit) => commit@.id() == token.id() && commit@@ =~= seq![val].add(token@),
            },
            outer_mask any / [STACK_NS],
            inner_mask none,
        },
        requires self.wf(),
    {
        let tracked mut au = atomic_update;
        let mut head: usize;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked StackInv { head_perm, auth, node_map, toks } = v;
            // let: "old_head" := !"stack" in
            head = self.head.load(Tracked(&head_perm));
            proof { v = StackInv { head_perm, auth, node_map, toks } }
        });

        loop invariant au == atomic_update, self.wf() {
            let node = Node { val, next: head };
            let (node_ptr, Tracked(node_perm)) = PPtr::<Node>::new(node);
            let new_head = node_ptr.addr();
            proof { node_perm.is_nonnull(); }
            assert(new_head != 0);

            let tracked mut maybe_au = Some(au);
            let tracked mut maybe_perm: Option<PointsTo<Node>> = Some(node_perm);
            let res;
            open_atomic_invariant!(self.inv.borrow() => v => {
                let tracked StackInv { mut head_perm, mut auth, mut node_map, mut toks } = v;
                res = self.head.compare_exchange_weak(Tracked(&mut head_perm), head, new_head);
                proof {
                    if res is Ok {
                        let tracked au = maybe_au.tracked_take();
                        let tracked mut np = maybe_perm.tracked_take();
                        try_open_atomic_update!(au, mut token => {
                            // authority and the client fragment agree (● xs ∗ ◯ ys ⊢ xs = ys)
                            auth_agree(&mut auth, &token.cont);
                            let old_seq = auth.view();
                            let old_nodes = node_map@;

                            // FRESHNESS via is_distinct against the existing read token.
                            if old_nodes.dom().contains(new_head) {
                                assert(toks.dom().contains(new_head));
                                let tracked pair = toks.tracked_borrow(new_head).borrow();
                                np.is_distinct(&pair.0);
                                assert(false);
                            }
                            assert(!old_nodes.dom().contains(new_head));

                            // abstract update (● / ◯ together)
                            let new_seq = seq![val].add(old_seq);
                            auth_update(&mut auth, &mut token.cont, new_seq);

                            // extend authority, mint a persistent value fragment
                            let ni = Node { val, next: head };
                            let tracked pts = node_map.insert(new_head, ni);
                            let tracked ppts = pts.persist();

                            // bundle read token + value fragment into ONE duplicable token
                            let tracked shared = Shared::new((np, ppts));
                            toks.tracked_insert(new_head, shared);

                            lemma_is_stack_list_push(head, new_head, val, old_seq, old_nodes, ni);
                            Tracked(Ok(Commit(token)))
                        });
                    }
                    v = StackInv { head_perm, auth, node_map, toks };
                }
            });

            match res {
                Ok(_) => { assert(atomic_update.resolves()); return; }
                Err(actual) => {
                    proof { au = maybe_au.tracked_take() };
                    head = actual;
                }
            }
        }
    }

    pub fn pop(&self) -> (out: Option<u64>)
        atomically (atomic_update) {
            (token: StackContent)
                -> (res: Result<Commit<StackContent>, (StackContent, OpenInvariantCredit)>),
            requires token.id() == self.ghost_var_id(),
            ensures match res {
                Err((t, _)) => t == token,
                Ok(commit) => commit@.id() == token.id()
                    && if token@.len() == 0 { commit@@ =~= token@ }
                       else { commit@@ =~= token@.subrange(1, token@.len() as int) },
            },
            outer_mask any / [STACK_NS],
            inner_mask none,
        },
        requires self.wf(),
    {
        let tracked mut au = atomic_update;

        loop invariant au == atomic_update, self.wf() {
            let mut head: usize;
            let tracked mut maybe_au = Some(au);
            let tracked mut maybe_tok: Option<Shared<(PointsTo<Node>, GhostPersistentPointsTo<usize, Node>)>> = None;

            let empty;
            open_atomic_invariant!(self.inv.borrow() => v => {
                let tracked StackInv { head_perm, mut auth, node_map, toks } = v;
                head = self.head.load(Tracked(&head_perm));
                empty = head == 0;
                proof {
                    if head == 0 {
                        let tracked au = maybe_au.tracked_take();
                        try_open_atomic_update!(au, token => {
                            auth_agree(&mut auth, &token.cont);
                            Tracked(Ok(Commit(token)))
                        });
                    } else {
                        assert(node_map@.dom().contains(head));
                        // ONE clone gives both the read capability and the value fragment.
                        maybe_tok = Some(toks.tracked_borrow(head).clone());
                    }
                    v = StackInv { head_perm, auth, node_map, toks };
                }
            });

            if empty {
                assert(atomic_update.resolves());
                return None;
            }
            proof { au = maybe_au.tracked_take(); }

            // Read the node THROUGH the cloned token's read permission (↦□ read).
            let tracked head_tok = maybe_tok.tracked_take();
            let head_ptr = PPtr::<Node>::from_addr(head);
            let node_val;
            let next;
            {
                let tracked pair = head_tok.borrow();
                let node_ref = head_ptr.borrow(Tracked(&pair.0));
                node_val = node_ref.val;
                next = node_ref.next;
            }
            assert(node_val == head_tok@.0.value().val);
            assert(next == head_tok@.0.value().next);

            let tracked mut maybe_au = Some(au);
            let res;
            open_atomic_invariant!(self.inv.borrow() => v => {
                let tracked StackInv { mut head_perm, mut auth, node_map, toks } = v;
                let ghost pre_head = head_perm@.value;
                res = self.head.compare_exchange_weak(Tracked(&mut head_perm), head, next);
                proof {
                    if res is Ok {
                        assert(pre_head == head);
                        assert(node_map@.dom().contains(head));
                        let tracked pair = head_tok.borrow();
                        pair.1.agree(&node_map);
                        assert(node_map@[head] == head_tok@.0.value());
                        assert(node_map@[head].next == next);
                        assert(node_map@[head].val == node_val);

                        let tracked au = maybe_au.tracked_take();
                        try_open_atomic_update!(au, mut token => {
                            auth_agree(&mut auth, &token.cont);
                            let old_seq = auth.view();
                            lemma_is_stack_list_pop(head, old_seq, node_map@);
                            let new_seq = old_seq.subrange(1, old_seq.len() as int);
                            auth_update(&mut auth, &mut token.cont, new_seq);
                            Tracked(Ok(Commit(token)))
                        });
                    }
                    v = StackInv { head_perm, auth, node_map, toks };
                }
            });

            match res {
                Ok(_) => {
                    assert(atomic_update.resolves());
                    return Some(node_val);
                }
                Err(_) => {
                    proof { au = maybe_au.tracked_take() };
                }
            }
        }
    }
}

fn client_sync() {
    let (stack, Tracked(mut token)) = TreiberStack::new();
    stack.push(42u64) atomically loop |update|
        invariant token.is_for(stack),
    {
        let tracked r: Result<Commit<StackContent>, (StackContent, OpenInvariantCredit)> = update(token);
        match r {
            Err((t, _)) => token = t,
            Ok(commit) => { token = commit.get(); break }
        }
    };
}

fn main() { client_sync(); }

} // verus!
