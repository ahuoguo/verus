#![verifier::exec_allows_no_decreases_clause]
#![verifier::loop_isolation(false)]

use vstd::prelude::*;
use vstd::atomic::*;
use vstd::invariant::*;
use vstd::simple_pptr::*;
use vstd::resource::*;
use vstd::resource::ghost_var::*;
use vstd::resource::map::*;
use vstd::shared::*;

verus! {

pub struct Node {
    pub val: u64,
    pub next: usize,
}

// TODO: Verus's size_of is uninterpreted for user structs
// https://github.com/verus-lang/verus/issues/2633
global layout Node is size == 16;

/// ghost linked-list predicate — the analog of `phys_list` (treiber2.v lines 88-94).
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

// ============================================================================
// Invariant
// ============================================================================

pub struct StackGhostState {
    pub head_perm: PermissionUsize,
    pub auth: GhostVarAuth<Seq<u64>>,
    // Authoritative node contents. Its view (`node_map@`) is the ghost node map.
    pub node_map: GhostMapAuth<usize, Node>,
    // Duplicable heap-read permission per node (the `↦□` read token).
    pub perms: Map<usize, Shared<PointsTo<Node>>>,
    // Duplicable value-agreement fragment per node (the `↦□` value knowledge).
    pub pers: Map<usize, GhostPersistentPointsTo<usize, Node>>,
}

pub struct StackConst {
    pub patomic_id: int,
    pub ghost_var_id: Loc,
    pub node_map_id: Loc,
}

pub open spec const STACK_NS: int = 7777;

pub struct StackInvPred;
impl InvariantPredicate<StackConst, StackGhostState> for StackInvPred {
    open spec fn inv(k: StackConst, v: StackGhostState) -> bool {
        let StackConst { patomic_id, ghost_var_id, node_map_id } = k;
        let StackGhostState { head_perm, auth, node_map, perms, pers } = v;
        &&& head_perm@.patomic == patomic_id
        &&& auth.id() == ghost_var_id
        &&& node_map.id() == node_map_id
        &&& is_stack_list(head_perm@.value, auth@, node_map@)
        &&& perms.dom() =~= node_map@.dom()
        &&& pers.dom() =~= node_map@.dom()
        &&& forall|addr: usize| #[trigger] node_map@.dom().contains(addr) ==> {
            // physical read token agrees with the node map
            &&& perms[addr]@.pptr().addr() == addr
            &&& perms[addr]@.is_init()
            &&& perms[addr]@.value() == node_map@[addr]
            // persistent value fragment agrees with the node map
            &&& pers[addr].id() == node_map_id
            &&& pers[addr]@ == (addr, node_map@[addr])
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

// own γ (● Excl' xs) / own γ (◯ Excl' xs)
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
        let tracked (node_map, _submap) = GhostMapAuth::<usize, Node>::new(Map::empty());
        let ghost k = StackConst {
            patomic_id: head.id(),
            ghost_var_id: gva.id(),
            node_map_id: node_map.id(),
        };
        let tracked state = StackGhostState {
            head_perm, auth: gva, node_map,
            perms: Map::tracked_empty(),
            pers: Map::tracked_empty(),
        };
        let tracked inv = AtomicInvariant::<StackConst, StackGhostState, StackInvPred>::new(k, state, STACK_NS);
        (TreiberStack { head, inv: Tracked(inv) }, Tracked(StackToken { inner: gv }))
    }
}

// ============================================================================
// Push
// ============================================================================

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
        let mut curr: usize;

        open_atomic_invariant!(self.inv.borrow() => v => {
            let tracked StackGhostState { head_perm, auth, node_map, perms, pers } = v;
            curr = self.head.load(Tracked(&head_perm));
            proof { v = StackGhostState { head_perm, auth, node_map, perms, pers } }
        });

        loop invariant au == atomic_update, self.wf() {
            // Allocate + initialize the new node while we still hold its EXCLUSIVE
            // PointsTo. This is the sole write to the node; after the CAS it is frozen.
            let node = Node { val, next: curr };
            let (node_ptr, Tracked(node_perm)) = PPtr::<Node>::new(node);
            let new_head = node_ptr.addr();
            proof { node_perm.is_nonnull(); }
            assert(new_head != 0);

            let tracked mut maybe_au = Some(au);
            let tracked mut maybe_perm: Option<PointsTo<Node>> = Some(node_perm);
            let res;
            open_atomic_invariant!(self.inv.borrow() => v => {
                let tracked StackGhostState { mut head_perm, mut auth, mut node_map, mut perms, mut pers } = v;
                res = self.head.compare_exchange_weak(Tracked(&mut head_perm), curr, new_head);
                proof {
                    if res is Ok {
                        let tracked au = maybe_au.tracked_take();
                        let tracked mut np = maybe_perm.tracked_take();
                        try_open_atomic_update!(au, mut token => {
                            let old_seq = auth@;
                            let old_nodes = node_map@;

                            // FRESHNESS: new_head ∉ old_nodes.dom() via is_distinct against
                            // the (shared) existing perm — two live PointsTo can't share an addr.
                            if old_nodes.dom().contains(new_head) {
                                assert(perms.dom().contains(new_head));
                                let tracked existing = perms.tracked_borrow(new_head).borrow();
                                np.is_distinct(existing);
                                assert(false);
                            }
                            assert(!old_nodes.dom().contains(new_head));

                            // Update the abstract stack (auth ● / token ◯ together).
                            let new_seq = seq![val].add(old_seq);
                            auth.update(&mut token.inner, new_seq);

                            // Extend the authoritative node map and derive a *persistent*,
                            // duplicable value fragment for the new node.
                            let ni = Node { val, next: curr };
                            let tracked pts = node_map.insert(new_head, ni);
                            let tracked ppts = pts.persist();
                            pers.tracked_insert(new_head, ppts);

                            // Freeze the node's PointsTo into a duplicable Shared (↦□ read).
                            let tracked shared = Shared::new(np);
                            perms.tracked_insert(new_head, shared);

                            lemma_is_stack_list_push(curr, new_head, val, old_seq, old_nodes, ni);
                            Tracked(Ok(Commit(token)))
                        });
                    }
                    v = StackGhostState { head_perm, auth, node_map, perms, pers };
                }
            });

            match res {
                Ok(_) => { assert(atomic_update.resolves()); return; }
                Err(actual) => {
                    proof { au = maybe_au.tracked_take() };
                    curr = actual;
                }
            }
        }
    }

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

        loop invariant au == atomic_update, self.wf() {
            let mut curr: usize;
            let tracked mut maybe_au = Some(au);
            // Cloned-out read token and value fragment for the node at `curr`.
            let tracked mut maybe_shared: Option<Shared<PointsTo<Node>>> = None;
            let tracked mut maybe_pers: Option<GhostPersistentPointsTo<usize, Node>> = None;

            let empty;
            open_atomic_invariant!(self.inv.borrow() => v => {
                let tracked StackGhostState { head_perm, mut auth, node_map, perms, pers } = v;
                curr = self.head.load(Tracked(&head_perm));
                empty = curr == 0;
                proof {
                    if curr == 0 {
                        // Empty pop linearizes at the load (treiber2.v lines 343-353):
                        // is_stack_list(0, auth@, _) => auth@.len() == 0.
                        let tracked au = maybe_au.tracked_take();
                        try_open_atomic_update!(au, token => {
                            auth.agree(&token.inner);
                            Tracked(Ok(Commit(token)))
                        });
                    } else {
                        // curr != 0 and is_stack_list(curr, auth@, node_map@) => curr ∈ dom.
                        assert(node_map@.dom().contains(curr));
                        // Clone the duplicable read token and value fragment out of the
                        // invariant — leaving it intact (both are duplicable, i.e. ↦□).
                        maybe_shared = Some(perms.tracked_borrow(curr).clone());
                        maybe_pers = Some(pers.tracked_borrow(curr).duplicate());
                    }
                    v = StackGhostState { head_perm, auth, node_map, perms, pers };
                }
            });

            if empty {
                assert(atomic_update.resolves());
                return None;
            }
            proof { au = maybe_au.tracked_take(); }

            // Read the node THROUGH the cloned Shared perm — outside any invariant,
            // exactly like reading `ℓ ↦□ (x, r)` in Iris (treiber2.v line 310).
            let tracked my_shared = maybe_shared.tracked_take();
            let tracked my_pers = maybe_pers.tracked_take();
            let head_ptr = PPtr::<Node>::from_addr(curr);
            let node_val;
            let next;
            {
                let tracked perm_ref = my_shared.borrow();
                let node_ref = head_ptr.borrow(Tracked(perm_ref));
                node_val = node_ref.val;
                next = node_ref.next;
            }
            // The value fragment we carry pins the node contents we just read.
            let ghost expected = my_pers@.1;
            assert(my_pers.key() == curr);
            assert(node_val == expected.val);
            assert(next == expected.next);

            let tracked mut maybe_au = Some(au);
            let res;
            open_atomic_invariant!(self.inv.borrow() => v => {
                let tracked StackGhostState { mut head_perm, mut auth, node_map, perms, pers } = v;
                let ghost pre_head = head_perm@.value;
                res = self.head.compare_exchange_weak(Tracked(&mut head_perm), curr, next);
                proof {
                    if res is Ok {
                        // CAS success => head was curr (!= 0), so curr ∈ dom(node_map@).
                        assert(pre_head == curr);
                        assert(node_map@.dom().contains(curr));
                        // pointsto_agree (treiber2.v line 330): the persistent value
                        // fragment agrees with the CURRENT authoritative node map, so the
                        // values we read equal node_map@[curr] — no immutability axiom.
                        my_pers.agree(&node_map);
                        assert(node_map@[curr] == expected);
                        assert(node_map@[curr].next == next);
                        assert(node_map@[curr].val == node_val);

                        let tracked au = maybe_au.tracked_take();
                        try_open_atomic_update!(au, mut token => {
                            let old_seq = auth@;
                            lemma_is_stack_list_pop(curr, old_seq, node_map@);
                            let new_seq = old_seq.subrange(1, old_seq.len() as int);
                            auth.update(&mut token.inner, new_seq);
                            Tracked(Ok(Commit(token)))
                        });
                    }
                    v = StackGhostState { head_perm, auth, node_map, perms, pers };
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
