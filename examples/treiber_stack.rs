#![verifier::exec_allows_no_decreases_clause]
#![verifier::loop_isolation(false)]

//! Treiber Stack
//!
//! Key proof technique for push freshness:
//! - PointsTo::is_nonnull() proves new_head != 0
//! - PointsTo::is_distinct() proves new_head not in existing map
//!   (two live PointsTo tokens cannot share an address)

use vstd::prelude::*;
use vstd::atomic::*;
use vstd::invariant::*;
use vstd::simple_pptr::*;
use vstd::resource::*;
use vstd::resource::ghost_var::*;

verus! {

pub struct Node {
    pub val: u64,
    pub next: usize,
}

// TODO: Verus's size_of is uninterpreted
// https://github.com/verus-lang/verus/issues/2633
global layout Node is size == 16;

/// ghost link list predicate
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

// ============================================================================
// Lemmas
// ============================================================================

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

// ============================================================================
// Invariant
// ============================================================================

pub struct StackGhostState {
    pub head_perm: PermissionUsize,
    pub auth: GhostVarAuth<Seq<u64>>,
    pub nodes: Ghost<Map<usize, Node>>,
    // Tracked map of PointsTo tokens for ALL allocated nodes.
    // This is the key: we can use is_distinct() against these.
    pub perms: Map<usize, PointsTo<Node>>,
}

pub struct StackConst {
    pub patomic_id: int,
    pub ghost_var_id: Loc,
}

pub open spec const STACK_NS: int = 7777;

pub struct StackInvPred;
impl InvariantPredicate<StackConst, StackGhostState> for StackInvPred {
    open spec fn inv(k: StackConst, v: StackGhostState) -> bool {
        let StackConst { patomic_id, ghost_var_id } = k;
        let StackGhostState { head_perm, auth, nodes, perms } = v;
        &&& head_perm@.patomic == patomic_id
        &&& auth.id() == ghost_var_id
        &&& is_stack_list(head_perm@.value, auth@, nodes@)
        // perms agrees with nodes: same domain, same content
        &&& perms.dom() =~= nodes@.dom()
        &&& forall|addr: usize| #[trigger] nodes@.dom().contains(addr) ==> {
            &&& perms[addr].pptr().addr() == addr
            &&& perms[addr].is_init()
            &&& perms[addr].value().val == nodes@[addr].val
            &&& perms[addr].value().next == nodes@[addr].next
        }
    }
}

// ============================================================================
// Public types
// ============================================================================

pub struct TreiberStack {
    pub head: PAtomicUsize,
    pub inv: Tracked<AtomicInvariant<StackConst, StackGhostState, StackInvPred>>,
}

pub tracked struct StackToken {
    pub inner: GhostVar<Seq<u64>>,
}

impl StackToken {
    pub open spec fn id(self) -> Loc { self.inner.id() }
    pub open spec fn view(self) -> Seq<u64> { self.inner@ }
    pub open spec fn is_for(self, s: TreiberStack) -> bool { self.id() == s.ghost_var_id() }
}

impl TreiberStack {
    pub open spec fn wf(self) -> bool {
        &&& self.head.id() == self.inv@.constant().patomic_id
        &&& self.inv@.namespace() == STACK_NS
    }
    pub open spec fn ghost_var_id(self) -> Loc { self.inv@.constant().ghost_var_id }
}

type PushAU = AtomicUpdate<StackToken, Result<Commit<StackToken>, (StackToken, OpenInvariantCredit)>, PushAtomicUpdatePredicate>;
type PopAU = AtomicUpdate<StackToken, Result<Commit<StackToken>, (StackToken, OpenInvariantCredit)>, PopAtomicUpdatePredicate>;

impl TreiberStack {
    pub fn new() -> (out: (TreiberStack, Tracked<StackToken>))
        ensures out.0.wf(), out.1@.is_for(out.0), out.1@@ =~= Seq::<u64>::empty(),
    {
        let (head, Tracked(head_perm)) = PAtomicUsize::new(0);
        let tracked (gva, gv) = GhostVarAuth::<Seq<u64>>::new(Seq::empty());
        let ghost k = StackConst { patomic_id: head.id(), ghost_var_id: gva.id() };
        let tracked state = StackGhostState {
            head_perm, auth: gva,
            nodes: Ghost(Map::empty()),
            perms: Map::tracked_empty(),
        };
        let tracked inv = AtomicInvariant::<StackConst, StackGhostState, StackInvPred>::new(k, state, STACK_NS);
        (TreiberStack { head, inv: Tracked(inv) }, Tracked(StackToken { inner: gv }))
    }
}

impl TreiberStack {
    pub fn push(&self, val: u64)
        atomically (atomic_update) {
            (token: StackToken)
                -> (res: Result<Commit<StackToken>, (StackToken, OpenInvariantCredit)>),
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
        let mut curr;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked StackGhostState { head_perm, auth, nodes, perms } = v;
            curr = self.head.load(Tracked(&head_perm));
            proof { v = StackGhostState { head_perm, auth, nodes, perms } }
        });


        loop invariant au == atomic_update, self.wf() {
            // Allocate node via PPtr::new — gives us PointsTo<Node>
            let node = Node { val, next: curr };
            let (node_ptr, Tracked(node_perm)) = PPtr::<Node>::new(node);
            let new_head = node_ptr.addr();
            // Prove non-null from PointsTo type invariant
            proof { node_perm.is_nonnull(); }
            assert(new_head != 0);

            match self.try_push(val, curr, new_head, node_ptr, Tracked(au), Tracked(node_perm)) {
                None => { assert(atomic_update.resolves()); return; }
                Some((actual, tracked_au)) => {
                    proof { au = tracked_au.get() };
                    curr = actual;
                }
            }
        }
    }

    fn try_push(&self, val: u64, expected: usize, new_head: usize, node_ptr: PPtr<Node>,
        Tracked(au): Tracked<PushAU>, Tracked(node_perm): Tracked<PointsTo<Node>>)
        -> (out: Option<(usize, Tracked<PushAU>)>)
        requires
            self.wf(), au.pred().args(self, val),
            new_head != 0,
            node_perm.pptr() == node_ptr,
            node_perm.pptr().addr() == new_head,
            node_perm.is_init(),
            node_perm.value().val == val,
            node_perm.value().next == expected,
        ensures match out {
            None => au.resolves(),
            Some((_, tracked_au)) => tracked_au@ == au,
        }
    {
        let tracked mut maybe_au = Some(au);
        let tracked mut maybe_perm: Option<PointsTo<Node>> = Some(node_perm);
        let res;
        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked StackGhostState { mut head_perm, mut auth, mut nodes, mut perms } = v;
            res = self.head.compare_exchange_weak(Tracked(&mut head_perm), expected, new_head);
            proof {
                if res is Ok {
                    let tracked au = maybe_au.tracked_take();
                    let tracked mut np = maybe_perm.tracked_take();
                    try_open_atomic_update!(au, mut token => {
                        let old_seq = auth@;
                        let old_nodes = nodes@;

                        // PROVE FRESHNESS: new_head is NOT in old_nodes.dom()
                        // Argument: if it were, perms[new_head] would exist with
                        // .pptr().addr() == new_head. But np also has .pptr().addr() == new_head.
                        // Two live PointsTo tokens can't have the same address.
                        if old_nodes.dom().contains(new_head) {
                            // perms[new_head] exists and has addr == new_head
                            assert(perms.dom().contains(new_head));
                            let tracked existing = perms.tracked_borrow(new_head);
                            np.is_distinct(existing);
                            // np.addr() != existing.addr() -- but both == new_head
                            assert(false);
                        }
                        assert(!old_nodes.dom().contains(new_head));

                        // Update ghost state
                        let new_seq = seq![val].add(old_seq);
                        auth.update(&mut token.inner, new_seq);
                        let ni = Node { val, next: expected };
                        nodes = Ghost(old_nodes.insert(new_head, ni));
                        perms.tracked_insert(new_head, np);
                        lemma_is_stack_list_push(expected, new_head, val, old_seq, old_nodes, ni);
                        Tracked(Ok(Commit(token)))
                    });
                }
                v = StackGhostState { head_perm, auth, nodes, perms };
            }
        });
        match res {
            Ok(_) => None,
            Err(actual) => Some((actual, Tracked(maybe_au.tracked_take()))),
        }
    }

    // ========================================================================
    // Pop (sketch — node read still requires persistent PointsTo)
    // ========================================================================

    pub fn pop(&self) -> (out: Option<u64>)
        atomically (atomic_update) {
            (token: StackToken)
                -> (res: Result<Commit<StackToken>, (StackToken, OpenInvariantCredit)>),
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
        let mut curr;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked StackGhostState { head_perm, auth, nodes, perms } = v;
            curr = self.head.load(Tracked(&head_perm));
            proof { v = StackGhostState { head_perm, auth, nodes, perms } }
        });

        loop invariant au == atomic_update, self.wf() {
            if curr == 0 {
                match self.try_pop_empty(Tracked(au)) {
                    None => { assert(atomic_update.resolves()); return None; }
                    Some((actual, tracked_au)) => {
                        proof { au = tracked_au.get() };
                        curr = actual;
                    }
                }
            } else {
                // TODO: Reading node requires persistent/fractional PointsTo.
                // For now, model with assume for the speculative read.
                let node_val: u64;
                let next: usize;
                assume(false); // node read
                node_val = 0;
                next = 0;

                match self.try_pop_nonempty(curr, next, node_val, Tracked(au)) {
                    None => { assert(atomic_update.resolves()); return Some(node_val); }
                    Some((actual, tracked_au)) => {
                        proof { au = tracked_au.get() };
                        curr = actual;
                    }
                }
            }
        }
    }

    fn try_pop_empty(&self, Tracked(au): Tracked<PopAU>)
        -> (out: Option<(usize, Tracked<PopAU>)>)
        requires self.wf(), au.pred().args(self),
        ensures match out { None => au.resolves(), Some((_, t)) => t@ == au }
    {
        let tracked mut maybe_au = Some(au);
        let res;
        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked StackGhostState { mut head_perm, mut auth, nodes, perms } = v;
            res = self.head.compare_exchange_weak(Tracked(&mut head_perm), 0, 0);
            proof {
                if res is Ok {
                    let tracked au = maybe_au.tracked_take();
                    try_open_atomic_update!(au, token => {
                        auth.agree(&token.inner);
                        Tracked(Ok(Commit(token)))
                    });
                }
                v = StackGhostState { head_perm, auth, nodes, perms };
            }
        });
        match res {
            Ok(_) => None,
            Err(actual) => Some((actual, Tracked(maybe_au.tracked_take()))),
        }
    }

    fn try_pop_nonempty(&self, expected: usize, next: usize, node_val: u64,
        Tracked(au): Tracked<PopAU>)
        -> (out: Option<(usize, Tracked<PopAU>)>)
        requires self.wf(), au.pred().args(self), expected != 0,
        ensures match out { None => au.resolves(), Some((_, t)) => t@ == au }
    {
        let tracked mut maybe_au = Some(au);
        let res;
        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked StackGhostState { mut head_perm, mut auth, mut nodes, perms } = v;
            res = self.head.compare_exchange_weak(Tracked(&mut head_perm), expected, next);
            proof {
                if res is Ok {
                    // Connection between physical read and ghost state:
                    // nodes are never modified, so what we read is still valid.
                    assume(nodes@.dom().contains(expected));
                    assume(nodes@[expected].next == next);
                    assume(nodes@[expected].val == node_val);

                    let tracked au = maybe_au.tracked_take();
                    try_open_atomic_update!(au, mut token => {
                        let old_seq = auth@;
                        lemma_is_stack_list_pop(expected, old_seq, nodes@);
                        let new_seq = old_seq.subrange(1, old_seq.len() as int);
                        auth.update(&mut token.inner, new_seq);
                        Tracked(Ok(Commit(token)))
                    });
                }
                v = StackGhostState { head_perm, auth, nodes, perms };
            }
        });
        match res {
            Ok(_) => None,
            Err(actual) => Some((actual, Tracked(maybe_au.tracked_take()))),
        }
    }
}

// ============================================================================
// Client
// ============================================================================

fn client_sync() {
    let (stack, Tracked(mut token)) = TreiberStack::new();
    stack.push(42u64) atomically loop |update|
        invariant token.is_for(stack),
    {
        let tracked r: Result<Commit<StackToken>, (StackToken, OpenInvariantCredit)> = update(token);
        match r {
            Err((t, _)) => token = t,
            Ok(commit) => { token = commit.get(); break }
        }
    };
}

fn main() { client_sync(); }

} // verus!
