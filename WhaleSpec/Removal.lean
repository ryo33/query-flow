/-
  Whale V3: Removal and Reverse-Edge Maintenance
  ==============================================

  This file formalises `Runtime::remove` and `Runtime::remove_if_unused`
  together with the reverse-edge unlinking they perform
  (`unlink_from_dependencies` in `crates/whale/src/runtime.rs`).

  # Why this file exists

  Before the unlinking was added, removing a node left its key in the
  `dependents` list of every node it depended on, forever. Those
  dependencies could then never be reclaimed by `remove_if_unused`, which
  refuses to remove anything whose `dependents` is non-empty: a GC leak.

  The existing `dependentsConsistent` does **not** detect this. It only
  constrains the dependencies of nodes that still exist, and a stale reverse
  edge points at a node that no longer exists, so the offending state
  satisfies it vacuously. The property that catches the leak is the converse
  inclusion, `dependentsMinimal` below.

  # Relationship to `dependentsConsistent`

  `dependentsConsistent` bundles two separable properties: that every
  dependency reference resolves to an existing node (this is `depsExist`),
  and that the reverse edge is present. `Runtime.remove` deliberately breaks
  the first -- it is documented to remove a node even when others depend on
  it, leaving them to recompute -- while preserving the second. So rather
  than weakening `dependentsConsistent`, this file introduces the weaker
  `dependentsSound`, proves `dependentsConsistent` implies it, and states the
  removal theorems in terms of the weaker form.
-/

import WhaleSpec.Basic

set_option linter.style.longLine false
set_option linter.flexible false

namespace Whale

/-! ## Invariants -/

/-- Reverse edges are present, *when the dependency still exists*.

    This is `dependentsConsistent` with the `none` case relaxed from `False`
    to `True`. Unlike `dependentsConsistent` it survives `Runtime.remove`,
    which may delete a node that others still depend on. -/
def dependentsSound {N : Nat} (nodes : QueryId → Option (Node N)) : Prop :=
  ∀ qid node,
    nodes qid = some node →
      ∀ dep ∈ node.dependencies,
        match nodes dep.queryId with
        | some depNode => qid ∈ depNode.dependents
        | none => True

/-- The strong invariant implies the weak one. -/
theorem dependentsConsistent_imp_dependentsSound {N : Nat}
    (nodes : QueryId → Option (Node N)) (h : dependentsConsistent nodes) :
    dependentsSound nodes := by
  intro qid node hnode dep hdep
  have hc := h qid node hnode dep hdep
  cases hd : nodes dep.queryId with
  | none => simp [hd]
  | some depNode =>
    rw [hd] at hc
    simpa [hd] using hc

/-- No *stale* reverse edges: everything listed as a dependent must still
    exist and must still declare the dependency.

    This is the converse of `dependentsSound`, and it is the property the
    reverse-edge unlinking exists to maintain. -/
def dependentsMinimal {N : Nat} (nodes : QueryId → Option (Node N)) : Prop :=
  ∀ depId depNode,
    nodes depId = some depNode →
      ∀ qid ∈ depNode.dependents,
        ∃ node, nodes qid = some node ∧ ∃ dep ∈ node.dependencies, dep.queryId = depId

/-! ## Unlinking reverse edges -/

/-- One step of the unlinking fold: drop `qid` from `dep.queryId`'s
    dependents.

    Rust's `Dependents::remove` short-circuits when `qid` is absent, but that
    is a copy-on-write optimisation; the resulting list is the same either
    way, so the model filters unconditionally. -/
def unlinkStep {N : Nat} (qid : QueryId) (ns : QueryId → Option (Node N)) (dep : Dep) :
    QueryId → Option (Node N) :=
  match ns dep.queryId with
  | none => ns
  | some depNode =>
    fun q =>
      if q = dep.queryId then
        some { depNode with dependents := depNode.dependents.filter (· ≠ qid) }
      else ns q

/-- Remove `qid` from the dependents list of every node it depended on.

    Matches Rust: `unlink_from_dependencies` in `runtime.rs`. -/
def unlinkFromDependencies {N : Nat} (nodes : QueryId → Option (Node N)) (qid : QueryId)
    (deps : List Dep) : QueryId → Option (Node N) :=
  deps.foldl (unlinkStep qid) nodes

/-! ### Pointwise facts about one step -/

theorem unlinkStep_isNone {N : Nat} (qid : QueryId) (ns : QueryId → Option (Node N))
    (dep : Dep) (k : QueryId) :
    unlinkStep qid ns dep k = none ↔ ns k = none := by
  unfold unlinkStep
  cases hd : ns dep.queryId with
  | none => simp
  | some depNode =>
    by_cases hk : k = dep.queryId
    · subst hk; simp [hd]
    · simp [hk]

/-- A step never changes any node's dependency list, and never grows a
    dependents list. -/
theorem unlinkStep_spec {N : Nat} (qid : QueryId) (ns : QueryId → Option (Node N))
    (dep : Dep) (k : QueryId) (node' : Node N) (h : unlinkStep qid ns dep k = some node') :
    ∃ node, ns k = some node ∧ node'.dependencies = node.dependencies ∧
      node'.dependents ⊆ node.dependents := by
  cases hd : ns dep.queryId with
  | none =>
    simp only [unlinkStep, hd] at h
    exact ⟨node', h, rfl, fun _ hq => hq⟩
  | some depNode =>
    simp only [unlinkStep, hd] at h
    by_cases hk : k = dep.queryId
    · subst hk
      simp only [if_true, Option.some.injEq] at h
      subst h
      refine ⟨depNode, hd, rfl, ?_⟩
      intro q hq
      simp only [List.mem_filter] at hq
      exact hq.1
    · rw [if_neg hk] at h
      exact ⟨node', h, rfl, fun _ hq => hq⟩

/-- After a step, `qid` is gone from the dependents of the node that step
    targeted. -/
theorem unlinkStep_removes {N : Nat} (qid : QueryId) (ns : QueryId → Option (Node N))
    (dep : Dep) (node' : Node N) (h : unlinkStep qid ns dep dep.queryId = some node') :
    qid ∉ node'.dependents := by
  cases hd : ns dep.queryId with
  | none => simp [unlinkStep, hd] at h
  | some depNode =>
    simp only [unlinkStep, hd, if_true, Option.some.injEq] at h
    subst h
    simp

/-! ### Facts about the whole fold -/

theorem unlink_isNone {N : Nat} (qid : QueryId) (deps : List Dep) :
    ∀ (ns : QueryId → Option (Node N)) (k : QueryId),
      unlinkFromDependencies ns qid deps k = none ↔ ns k = none := by
  unfold unlinkFromDependencies
  induction deps with
  | nil => intro ns k; simp
  | cons dep rest ih =>
    intro ns k
    simp only [List.foldl_cons]
    rw [ih (unlinkStep qid ns dep) k, unlinkStep_isNone]

theorem unlink_isSome {N : Nat} (qid : QueryId) (deps : List Dep)
    (ns : QueryId → Option (Node N)) (k : QueryId) (node : Node N) (h : ns k = some node) :
    ∃ node', unlinkFromDependencies ns qid deps k = some node' := by
  cases h' : unlinkFromDependencies ns qid deps k with
  | none => rw [unlink_isNone qid deps ns k, h] at h'; exact absurd h' (by simp)
  | some node' => exact ⟨node', rfl⟩

/-- The fold preserves dependency lists and only ever shrinks dependents. -/
theorem unlink_spec {N : Nat} (qid : QueryId) (deps : List Dep) :
    ∀ (ns : QueryId → Option (Node N)) (k : QueryId) (node' : Node N),
      unlinkFromDependencies ns qid deps k = some node' →
        ∃ node, ns k = some node ∧ node'.dependencies = node.dependencies ∧
          node'.dependents ⊆ node.dependents := by
  unfold unlinkFromDependencies
  induction deps with
  | nil => intro ns k node' h; exact ⟨node', h, rfl, fun _ hq => hq⟩
  | cons dep rest ih =>
    intro ns k node' h
    simp only [List.foldl_cons] at h
    obtain ⟨mid, hmid, hdeps, hsub⟩ := ih (unlinkStep qid ns dep) k node' h
    obtain ⟨node, hnode, hdeps', hsub'⟩ := unlinkStep_spec qid ns dep k mid hmid
    exact ⟨node, hnode, by rw [hdeps, hdeps'], fun _ hq => hsub' (hsub hq)⟩

/-- Whatever depended on `qid` through `deps` no longer lists `qid`.

    This is the property the fix establishes: after unlinking, `qid` is gone
    from the dependents of every node in `deps`. -/
theorem unlink_removes {N : Nat} (qid : QueryId) (deps : List Dep) :
    ∀ (ns : QueryId → Option (Node N)) (dep : Dep), dep ∈ deps →
      ∀ node', unlinkFromDependencies ns qid deps dep.queryId = some node' →
        qid ∉ node'.dependents := by
  unfold unlinkFromDependencies
  induction deps with
  | nil => intro _ _ hmem; simp at hmem
  | cons d rest ih =>
    intro ns dep hmem node' h
    simp only [List.foldl_cons] at h
    rcases List.mem_cons.mp hmem with rfl | hrest
    · -- `dep` is handled by this step; later steps only shrink further.
      obtain ⟨mid, hmid, _, hsub⟩ := unlink_spec qid rest (unlinkStep qid ns dep) dep.queryId node' h
      exact fun hq => unlinkStep_removes qid ns dep mid hmid (hsub hq)
    · exact ih (unlinkStep qid ns d) dep hrest node' h

/-- One step keeps every dependent other than `qid`. -/
theorem unlinkStep_preserves_mem_ne {N : Nat} (qid : QueryId) (ns : QueryId → Option (Node N))
    (dep : Dep) (k : QueryId) (node node' : Node N) (hns : ns k = some node)
    (h : unlinkStep qid ns dep k = some node') (q : QueryId) (hq : q ≠ qid)
    (hmem : q ∈ node.dependents) : q ∈ node'.dependents := by
  cases hd : ns dep.queryId with
  | none =>
    simp only [unlinkStep, hd] at h
    rw [hns] at h
    injection h with h
    subst h
    exact hmem
  | some depNode =>
    simp only [unlinkStep, hd] at h
    by_cases hk : k = dep.queryId
    · subst hk
      simp only [if_true, Option.some.injEq] at h
      subst h
      rw [hns] at hd
      injection hd with hd
      subst hd
      simpa [List.mem_filter] using ⟨hmem, hq⟩
    · rw [if_neg hk, hns] at h
      injection h with h
      subst h
      exact hmem

/-- The whole fold keeps every dependent other than `qid`. -/
theorem unlink_preserves_mem_ne {N : Nat} (qid : QueryId) (deps : List Dep) :
    ∀ (ns : QueryId → Option (Node N)) (k : QueryId) (node node' : Node N),
      ns k = some node → unlinkFromDependencies ns qid deps k = some node' →
        ∀ q, q ≠ qid → q ∈ node.dependents → q ∈ node'.dependents := by
  unfold unlinkFromDependencies
  induction deps with
  | nil =>
    intro ns k node node' hns h q hq hmem
    simp only [List.foldl_nil] at h
    rw [hns] at h
    injection h with h
    subst h
    exact hmem
  | cons dep rest ih =>
    intro ns k node node' hns h q hq hmem
    simp only [List.foldl_cons] at h
    obtain ⟨mid, hmid⟩ : ∃ mid, unlinkStep qid ns dep k = some mid := by
      cases hm : unlinkStep qid ns dep k with
      | none => rw [unlinkStep_isNone, hns] at hm; exact absurd hm (by simp)
      | some mid => exact ⟨mid, rfl⟩
    exact ih (unlinkStep qid ns dep) k mid node' hmid h q hq
      (unlinkStep_preserves_mem_ne qid ns dep k node mid hns hmid q hq hmem)

/-! ## Removal operations -/

/-- Remove a node and unlink it from its dependencies' reverse edges.

    Matches Rust: `Runtime::remove`. The node is taken out of the map first,
    then unlinked, mirroring the fact that the unlinking runs outside the
    shard lock. -/
def Runtime.remove {N : Nat} (rt : Runtime N) (qid : QueryId) : Runtime N × Option (Node N) :=
  match h : rt.nodes qid with
  | none => (rt, none)
  | some node =>
    let detached : QueryId → Option (Node N) := fun q => if q = qid then none else rt.nodes q
    ({ rt with nodes := unlinkFromDependencies detached qid node.dependencies }, some node)

/-- Remove a node only if nothing depends on it.

    Matches Rust: `Runtime::remove_if_unused`. -/
def Runtime.removeIfUnused {N : Nat} (rt : Runtime N) (qid : QueryId) :
    Runtime N × Option (Node N) :=
  match rt.nodes qid with
  | none => (rt, none)
  | some node => if node.dependents.isEmpty then rt.remove qid else (rt, none)

/-! ## The removed node is gone -/

theorem remove_gone {N : Nat} (rt : Runtime N) (qid : QueryId) :
    (rt.remove qid).1.nodes qid = none := by
  unfold Runtime.remove
  cases h : rt.nodes qid with
  | none => simpa using h
  | some node =>
    simp only
    rw [unlink_isNone qid node.dependencies]
    simp

/-! ## Invariant preservation -/

/-- Removal never introduces a stale reverse edge.

    This is the theorem that fails for the unfixed implementation: without
    `unlinkFromDependencies`, the removed node stays in its dependencies'
    `dependents` lists while no longer existing, so the witness demanded by
    `dependentsMinimal` cannot be produced. -/
theorem remove_preserves_dependentsMinimal {N : Nat} (rt : Runtime N) (qid : QueryId)
    (h : dependentsMinimal rt.nodes) :
    dependentsMinimal (rt.remove qid).1.nodes := by
  unfold Runtime.remove
  cases hq : rt.nodes qid with
  | none => simpa [hq] using h
  | some rnode =>
    simp only
    set detached : QueryId → Option (Node N) := fun q => if q = qid then none else rt.nodes q with hdet
    intro depId depNode' hdepNode' q hq'
    -- The dependency node still exists before unlinking.
    obtain ⟨depNode, hdepNode, _, hsub⟩ :=
      unlink_spec qid rnode.dependencies detached depId depNode' hdepNode'
    -- `depId` survived detaching, so it is not the removed node.
    have hdepId_ne : depId ≠ qid := by
      intro hcontra
      rw [hcontra] at hdepNode
      simp [hdet] at hdepNode
    have hdepNode_orig : rt.nodes depId = some depNode := by
      have := hdepNode
      simp only [hdet, if_neg hdepId_ne] at this
      exact this
    -- `q` was already a dependent before unlinking.
    have hq_orig : q ∈ depNode.dependents := hsub hq'
    obtain ⟨node, hnode, dep, hdep, hdepEq⟩ := h depId depNode hdepNode_orig q hq_orig
    -- `q` cannot be the removed node: if it were, `depId` would be one of its
    -- dependencies and the unlinking would have dropped it.
    have hq_ne : q ≠ qid := by
      intro hcontra
      rw [hcontra, hq] at hnode
      injection hnode with hnode
      have hdep' : dep ∈ rnode.dependencies := by rw [hnode]; exact hdep
      exact unlink_removes qid rnode.dependencies detached dep hdep' depNode'
        (by rw [hdepEq]; exact hdepNode') (hcontra ▸ hq')
    -- `q` still exists after removal, with the same dependencies.
    have hq_detached : detached q = some node := by simp [hdet, hq_ne, hnode]
    obtain ⟨node', hnode'⟩ := unlink_isSome qid rnode.dependencies detached q node hq_detached
    obtain ⟨node'', hnode'', hdepsEq, _⟩ :=
      unlink_spec qid rnode.dependencies detached q node' hnode'
    rw [hq_detached] at hnode''
    injection hnode'' with hnode''
    subst hnode''
    exact ⟨node', hnode', dep, by rw [hdepsEq]; exact hdep, hdepEq⟩

/-- Removal never drops a reverse edge that is still needed. -/
theorem remove_preserves_dependentsSound {N : Nat} (rt : Runtime N) (qid : QueryId)
    (h : dependentsSound rt.nodes) :
    dependentsSound (rt.remove qid).1.nodes := by
  unfold Runtime.remove
  cases hq : rt.nodes qid with
  | none => simpa [hq] using h
  | some rnode =>
    simp only
    set detached : QueryId → Option (Node N) := fun q => if q = qid then none else rt.nodes q with hdet
    intro k node' hnode' dep hdep
    cases hd : unlinkFromDependencies detached qid rnode.dependencies dep.queryId with
    | none => simp
    | some depNode' =>
      simp only
      -- Recover the pre-unlink nodes.
      obtain ⟨node, hnode, hdepsEq, _⟩ :=
        unlink_spec qid rnode.dependencies detached k node' hnode'
      obtain ⟨depNode, hdepNode, _, _⟩ :=
        unlink_spec qid rnode.dependencies detached dep.queryId depNode' hd
      have hk_ne : k ≠ qid := by
        intro hcontra; rw [hcontra] at hnode; simp [hdet] at hnode
      have hdep_ne : dep.queryId ≠ qid := by
        intro hcontra; rw [hcontra] at hdepNode; simp [hdet] at hdepNode
      have hnode_orig : rt.nodes k = some node := by
        have := hnode; simp only [hdet, if_neg hk_ne] at this; exact this
      have hdepNode_orig : rt.nodes dep.queryId = some depNode := by
        have := hdepNode; simp only [hdet, if_neg hdep_ne] at this; exact this
      -- `k` still declares the dependency, so soundness applies.
      have hdep_orig : dep ∈ node.dependencies := by rw [← hdepsEq]; exact hdep
      have hsound := h k node hnode_orig dep hdep_orig
      rw [hdepNode_orig] at hsound
      -- Unlinking only removes `qid`, and `k ≠ qid`.
      exact unlink_preserves_mem_ne qid rnode.dependencies detached dep.queryId depNode depNode'
        hdepNode hd k hk_ne hsound

/-! ## GC progress

    The point of the unlinking: removing a dependent must actually free the
    node it depended on, so that a garbage-collection sweep makes progress
    instead of stalling on permanently pinned nodes. -/

/-- Removing `b` drops `b` from the dependents of everything `b` depended on. -/
theorem remove_frees_dependency {N : Nat} (rt : Runtime N) (b : QueryId) (bNode : Node N)
    (hb : rt.nodes b = some bNode) (dep : Dep) (hdep : dep ∈ bNode.dependencies)
    (aNode' : Node N) (ha' : (rt.remove b).1.nodes dep.queryId = some aNode') :
    b ∉ aNode'.dependents := by
  unfold Runtime.remove at ha'
  rw [hb] at ha'
  exact unlink_removes b bNode.dependencies _ dep hdep aNode' ha'

/-- If `b` was the only thing depending on `a`, then after removing `b` the
    node `a` has no dependents left, so `removeIfUnused` will reclaim it.

    Without the unlinking this fails: `a.dependents` would still be `[b]`
    even though `b` is gone, and `a` would be pinned forever. -/
theorem remove_enables_reclaim {N : Nat} (rt : Runtime N) (a b : QueryId)
    (aNode bNode : Node N) (hne : a ≠ b)
    (ha : rt.nodes a = some aNode) (haDeps : aNode.dependents = [b])
    (hb : rt.nodes b = some bNode) (dep : Dep) (hdep : dep ∈ bNode.dependencies)
    (hdepEq : dep.queryId = a) :
    ∃ aNode', (rt.remove b).1.nodes a = some aNode' ∧ aNode'.dependents = [] := by
  -- `a` survives the removal of `b`.
  have hdet : (fun q => if q = b then none else rt.nodes q) a = some aNode := by
    simp [hne, ha]
  obtain ⟨aNode', ha'⟩ :=
    unlink_isSome b bNode.dependencies (fun q => if q = b then none else rt.nodes q) a aNode hdet
  have hres : (rt.remove b).1.nodes a = some aNode' := by
    unfold Runtime.remove; rw [hb]; exact ha'
  refine ⟨aNode', hres, ?_⟩
  -- Its dependents shrank from `[b]`, and `b` itself was removed from them.
  obtain ⟨aOrig, hOrig, _, hsub⟩ :=
    unlink_spec b bNode.dependencies (fun q => if q = b then none else rt.nodes q) a aNode' ha'
  simp only [if_neg hne, ha, Option.some.injEq] at hOrig
  subst hOrig
  have hb_not : b ∉ aNode'.dependents :=
    remove_frees_dependency rt b bNode hb dep hdep aNode' (by rw [hdepEq]; exact hres)
  refine List.eq_nil_iff_forall_not_mem.mpr ?_
  intro x hx
  have hx' : x ∈ aNode.dependents := hsub hx
  rw [haDeps, List.mem_singleton] at hx'
  subst hx'
  exact hb_not hx

/-! ## The invariant is not vacuous

    A specification that the buggy implementation also satisfies would be
    worthless. This section models the pre-fix `remove` -- which took the node
    out of the map without touching reverse edges -- and exhibits a concrete
    two-node state where it violates `dependentsMinimal`.

    Note that the same state satisfies `dependentsConsistent` both before and
    after, which is exactly why that invariant did not catch the leak. -/

/-- The unfixed implementation: detach the node, leave reverse edges behind. -/
def Runtime.removeNoUnlink {N : Nat} (rt : Runtime N) (qid : QueryId) :
    Runtime N × Option (Node N) :=
  match rt.nodes qid with
  | none => (rt, none)
  | some node => ({ rt with nodes := fun q => if q = qid then none else rt.nodes q }, some node)

namespace Leak

/-- Node `0`: a leaf that node `1` depends on. -/
def aNode : Node 1 :=
  { durability := 0, verifiedAt := 0, changedAt := 0, level := 0,
    dependencies := [], dependents := [1] }

/-- Node `1`: depends on node `0`. -/
def bNode : Node 1 :=
  { durability := 0, verifiedAt := 0, changedAt := 0, level := 1,
    dependencies := [⟨0, 0⟩], dependents := [] }

def nodes : QueryId → Option (Node 1) :=
  fun q => if q = 0 then some aNode else if q = 1 then some bNode else none

def rt : Runtime 1 := { nodes := nodes, revision := fun _ => 0, numDurabilityLevels := Nat.one_pos }

theorem start_minimal : dependentsMinimal rt.nodes := by
  intro depId depNode hdep q hq
  by_cases h0 : depId = 0
  · subst h0
    simp only [rt, nodes, if_pos rfl, if_true, Option.some.injEq] at hdep
    subst hdep
    simp only [aNode, List.mem_singleton] at hq
    subst hq
    exact ⟨bNode, by simp [rt, nodes], ⟨0, 0⟩, by simp [bNode], rfl⟩
  · by_cases h1 : depId = 1
    · subst h1
      simp only [rt, nodes, if_neg (by decide : (1 : QueryId) ≠ 0), if_pos rfl, if_true,
        Option.some.injEq] at hdep
      subst hdep
      simp [bNode] at hq
    · simp only [rt, nodes, if_neg h0, if_neg h1] at hdep
      exact absurd hdep (by simp)

/-- The pre-fix removal leaves `1` in node `0`'s dependents even though node
    `1` no longer exists, so `dependentsMinimal` fails. -/
theorem removeNoUnlink_breaks_minimal :
    ¬ dependentsMinimal (rt.removeNoUnlink 1).1.nodes := by
  intro hmin
  have hnodes : (rt.removeNoUnlink 1).1.nodes = fun q => if q = 1 then none else rt.nodes q := by
    unfold Runtime.removeNoUnlink
    simp [rt, nodes, bNode]
  have h0 : (rt.removeNoUnlink 1).1.nodes 0 = some aNode := by
    rw [hnodes]; simp [rt, nodes]
  obtain ⟨node, hnode, _⟩ := hmin 0 aNode h0 1 (by simp [aNode])
  rw [hnodes] at hnode
  simp at hnode

/-- The fixed removal keeps the invariant on the very same state. -/
theorem remove_keeps_minimal : dependentsMinimal (rt.remove 1).1.nodes :=
  remove_preserves_dependentsMinimal rt 1 start_minimal

end Leak

end Whale
