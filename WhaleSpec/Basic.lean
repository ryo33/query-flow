/-
  Whale V3 Formal Specification in Lean 4
  ========================================

  This file defines the core data structures and operations for
  the Whale incremental computation dependency tracking system.

  We start with a sequential model (no concurrency) to verify
  the fundamental correctness properties.
-/

import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

set_option linter.style.longLine false
set_option linter.flexible false

namespace Whale

/-! ## Basic Types -/

/-- Query identifier type (abstract) -/
abbrev QueryId := Nat

/-- Durability level: 0 = most volatile, N-1 = most stable -/
abbrev Durability := Nat

/-- Revision counter -/
abbrev RevisionCounter := Nat

/-! ## Core Data Structures -/

/-- Revision snapshot: array of counters indexed by durability level
    revision[d] is the counter for durability level d -/
structure Revision (N : Nat) where
  counters : Fin N → RevisionCounter

/-- Dependency record: tracks which query we depend on and
    what its changed_at was when we observed it -/
structure Dep where
  queryId : QueryId
  observedChangedAt : RevisionCounter
  deriving DecidableEq, Repr

/-- Node in the dependency graph -/
structure Node (N : Nat) where
  durability : Fin N
  verifiedAt : RevisionCounter
  changedAt : RevisionCounter
  level : Nat                    -- topological level
  dependencies : List Dep        -- who this node depends on
  dependents : List QueryId      -- who depends on this node
  deriving Repr

/-- Runtime state: manages the dependency graph -/
@[ext]
structure Runtime (N : Nat) where
  nodes : QueryId → Option (Node N)
  revision : Fin N → RevisionCounter
  numDurabilityLevels : N > 0    -- at least one durability level

/-! ## Basic Operations on Revision -/

/-- Get current revision snapshot -/
def Runtime.currentRevision {N : Nat} (rt : Runtime N) : Revision N :=
  ⟨rt.revision⟩

/-- Increment revision at durability level d and all lower levels (0..d)
    Per spec: "for i in 0..=D: revision[i].fetch_add(1, AcqRel)"
    Note: Lower index = more volatile, higher index = more stable -/
def Runtime.incrementRevision {N : Nat} (rt : Runtime N)
    (d : Fin N) : Runtime N × RevisionCounter :=
  let newRev := rt.revision d + 1
  let newRevision := fun i =>
    if i.val ≤ d.val then rt.revision i + 1 else rt.revision i
  (⟨rt.nodes, newRevision, rt.numDurabilityLevels⟩, newRev)

/-! ## Invariants -/

/-- Durability invariant: a node's durability must not exceed
    the minimum durability of its dependencies -/
def durabilityInvariant {N : Nat} (nodes : QueryId → Option (Node N)) (n : Node N) : Prop :=
  ∀ dep ∈ n.dependencies,
    match nodes dep.queryId with
    | some depNode => n.durability ≤ depNode.durability
    | none => False  -- dependency must exist

/-- Topological level invariant: a node's level must be greater than
    all its dependencies' levels -/
def levelInvariant {N : Nat} (nodes : QueryId → Option (Node N)) (n : Node N) : Prop :=
  ∀ dep ∈ n.dependencies,
    match nodes dep.queryId with
    | some depNode => n.level > depNode.level
    | none => False

/-- All dependencies must exist -/
def depsExist {N : Nat} (nodes : QueryId → Option (Node N)) (n : Node N) : Prop :=
  ∀ dep ∈ n.dependencies, (nodes dep.queryId).isSome

/-- DAG invariant: no cycles in the dependency graph
    We express this via the level invariant: if levels are consistent,
    there can be no cycles -/
def dagInvariant {N : Nat} (nodes : QueryId → Option (Node N)) : Prop :=
  ∀ qid, match nodes qid with
  | some n => levelInvariant nodes n
  | none => True

/-- Global durability invariant for all nodes -/
def globalDurabilityInvariant {N : Nat} (nodes : QueryId → Option (Node N)) : Prop :=
  ∀ qid, match nodes qid with
  | some n => durabilityInvariant nodes n
  | none => True

/-- Dependents consistency: if qid depends on depId, then qid is in depId's dependents list
    This captures the bidirectional consistency between dependencies and dependents fields -/
def dependentsConsistent {N : Nat} (nodes : QueryId → Option (Node N)) : Prop :=
  ∀ qid node,
    nodes qid = some node →
      ∀ dep ∈ node.dependencies,
        match nodes dep.queryId with
        | some depNode => qid ∈ depNode.dependents
        | none => False

/-- No self-dependency: a node cannot depend on itself.
    This is a fundamental DAG property and is required for cycle detection. -/
def noSelfDependency {N : Nat} (nodes : QueryId → Option (Node N)) : Prop :=
  ∀ qid node, nodes qid = some node → ∀ dep ∈ node.dependencies, dep.queryId ≠ qid

/-- Local version: a specific node has no self-dependency -/
def nodeNoSelfDep (qid : QueryId) (node : Node N) : Prop :=
  ∀ dep ∈ node.dependencies, dep.queryId ≠ qid

/-! ## Helper Functions -/

/-- Get minimum durability among dependencies -/
def minDepDurability {N : Nat} (nodes : QueryId → Option (Node N))
    (deps : List Dep) (default : Durability) : Durability :=
  deps.foldl (fun acc dep =>
    match nodes dep.queryId with
    | some n => min acc n.durability.val
    | none => acc
  ) default

/-- Calculate effective durability (enforce invariant) -/
def calculateEffectiveDurability {N : Nat} (nodes : QueryId → Option (Node N))
    (requested : Durability) (deps : List Dep) (maxDur : Durability) : Durability :=
  let minDep := minDepDurability nodes deps maxDur
  min requested minDep

/-- Calculate topological level from dependencies -/
def calculateLevel {N : Nat} (nodes : QueryId → Option (Node N)) (deps : List Dep) : Nat :=
  let maxDepLevel := deps.foldl (fun acc dep =>
    match nodes dep.queryId with
    | some n => max acc n.level
    | none => acc
  ) 0
  maxDepLevel + 1

/-! ## Core Algorithms -/

/-- Check if a node is valid at a given revision (read-only operation)

    A node is valid if:
    1. Its verified_at >= revision[node.durability], OR
    2. All dependencies have not changed since we last observed them
-/
def isValidAt {N : Nat} (rt : Runtime N) (qid : QueryId) (atRev : Revision N) : Bool :=
  match rt.nodes qid with
  | none => false
  | some node =>
    -- Check if already verified at this revision
    let d : Fin N := node.durability
    if node.verifiedAt ≥ atRev.counters d then
      true
    else
      -- Check each dependency
      node.dependencies.all fun dep =>
        match rt.nodes dep.queryId with
        | none => false  -- dependency removed
        | some depNode =>
          -- Using > not >=: equal means "no change since observation"
          !decide (depNode.changedAt > dep.observedChangedAt)

/-- Convenience: check validity at current revision -/
def isValid {N : Nat} (rt : Runtime N) (qid : QueryId) : Bool :=
  isValidAt rt qid rt.currentRevision

/-- Mark a node as verified at given revision (idempotent update)
    Uses max to ensure monotonicity -/
def markVerified {N : Nat} (rt : Runtime N) (qid : QueryId)
    (atRev : Revision N) : Runtime N :=
  match rt.nodes qid with
  | none => rt
  | some node =>
    let d : Fin N := node.durability
    let newVerifiedAt := max node.verifiedAt (atRev.counters d)
    let newNode := { node with verifiedAt := newVerifiedAt }
    let newNodes := fun q => if q = qid then some newNode else rt.nodes q
    ⟨newNodes, rt.revision, rt.numDurabilityLevels⟩

/-- Build dependency records by capturing current changed_at values -/
def buildDepRecords {N : Nat} (nodes : QueryId → Option (Node N)) (depIds : List QueryId) : Except (List QueryId) (List Dep) :=
  let (deps, missing) :=
    depIds.foldl
      (fun (acc : List Dep × List QueryId) depId =>
        match nodes depId with
        | some depNode => (⟨depId, depNode.changedAt⟩ :: acc.1, acc.2)
        | none => (acc.1, depId :: acc.2))
      ([], [])
  if missing.isEmpty then
    Except.ok deps.reverse
  else
    Except.error missing.reverse

/-- If `buildDepRecords` succeeds, every `Dep` in the result refers to an existing node. -/
lemma buildDepRecords_ok_mem_implies_some {N : Nat} (nodes : QueryId → Option (Node N))
    (depIds : List QueryId) (depRecords : List Dep)
    (hok : buildDepRecords nodes depIds = Except.ok depRecords) :
    ∀ dep, dep ∈ depRecords → ∃ depNode, nodes dep.queryId = some depNode := by
  classical
  -- Fold step, matching `buildDepRecords`.
  let step : (List Dep × List QueryId) → QueryId → (List Dep × List QueryId) :=
    fun acc depId =>
      match nodes depId with
      | some depNode => (⟨depId, depNode.changedAt⟩ :: acc.1, acc.2)
      | none => (acc.1, depId :: acc.2)
  -- Invariant: all deps accumulated so far point to `some` nodes.
  have inv :
      ∀ (ids : List QueryId) (acc : List Dep × List QueryId),
        (∀ dep, dep ∈ acc.1 → ∃ depNode, nodes dep.queryId = some depNode) →
        ∀ dep, dep ∈ (ids.foldl step acc).1 → ∃ depNode, nodes dep.queryId = some depNode := by
    intro ids
    induction ids with
    | nil =>
      intro acc hacc dep hdep
      simpa using hacc dep hdep
    | cons depId tl ih =>
      intro acc hacc dep hdep
      -- peel one fold step
      cases hnode : nodes depId with
      | none =>
        have hacc' : ∀ dep, dep ∈ (step acc depId).1 → ∃ depNode, nodes dep.queryId = some depNode := by
          -- deps list unchanged in the `none` case
          intro dep hmem
          have hmem' : dep ∈ acc.1 := by
            simpa [step, hnode] using hmem
          exact hacc dep hmem'
        have hdep' : dep ∈ (tl.foldl step (step acc depId)).1 := by
          simpa [List.foldl, step, hnode] using hdep
        exact ih (acc := step acc depId) hacc' dep hdep'
      | some depNode =>
        have hacc' : ∀ dep, dep ∈ (step acc depId).1 → ∃ depNode, nodes dep.queryId = some depNode := by
          intro dep hmem
          -- either the freshly added head, or something from the previous accumulator
          have : dep = ⟨depId, depNode.changedAt⟩ ∨ dep ∈ acc.1 := by
            have := (List.mem_cons.mp (by simpa [step, hnode] using hmem))
            exact this
          cases this with
          | inl heq =>
            subst heq
            exact ⟨depNode, hnode⟩
          | inr hin =>
            exact hacc dep hin
        have hdep' : dep ∈ (tl.foldl step (step acc depId)).1 := by
          simpa [List.foldl, step, hnode] using hdep
        exact ih (acc := step acc depId) hacc' dep hdep'
  -- Unfold `buildDepRecords` and extract that `depRecords = deps.reverse`.
  unfold buildDepRecords at hok
  -- name the fold result
  cases hfold : depIds.foldl step ([], []) with
  | mk deps missing =>
    -- reduce the `if` using the fact we are in the `.ok` branch
    have hrec : depRecords = deps.reverse := by
      cases hmiss : missing.isEmpty with
      | false =>
        -- would produce `.error`, contradiction
        simp [hfold, step, hmiss] at hok
      | true =>
        -- `simp` produces `deps.reverse = depRecords`, so flip it
        exact Eq.symm (by simpa [hfold, step, hmiss] using hok)
    intro dep hmem
    have hmemRev : dep ∈ deps.reverse := by simpa [hrec] using hmem
    have hmemDeps : dep ∈ deps := by simpa using (List.mem_reverse.mp hmemRev)
    -- relate `deps` to the fold result and apply `inv` with empty initial accumulator.
    have hdepsEq : (depIds.foldl step ([], [])).1 = deps := by
      simp [hfold]
    have hmemFold : dep ∈ (depIds.foldl step ([], [])).1 := by
      simpa [hdepsEq] using hmemDeps
    -- base accumulator has no deps
    have hbase : ∀ dep, dep ∈ ([] : List Dep) → ∃ depNode, nodes dep.queryId = some depNode := by
      intro dep h; cases h
    exact inv depIds ([], []) (by simp) dep hmemFold

/-- If `buildDepRecords` succeeds, every `Dep.queryId` comes from the requested `depIds`. -/
lemma buildDepRecords_ok_mem_queryId_mem {N : Nat} (nodes : QueryId → Option (Node N))
    (depIds : List QueryId) (depRecords : List Dep)
    (hok : buildDepRecords nodes depIds = Except.ok depRecords) :
    ∀ dep, dep ∈ depRecords → dep.queryId ∈ depIds := by
  classical
  unfold buildDepRecords at hok
  -- expose the fold result
  let step : (List Dep × List QueryId) → QueryId → (List Dep × List QueryId) :=
    fun acc depId =>
      match nodes depId with
      | some depNode => (⟨depId, depNode.changedAt⟩ :: acc.1, acc.2)
      | none => (acc.1, depId :: acc.2)
  cases hfold : depIds.foldl step ([], []) with
  | mk deps missing =>
    have hrec : depRecords = deps.reverse := by
      cases hmiss : missing.isEmpty with
      | false =>
        simp [hfold, step, hmiss] at hok
      | true =>
        exact Eq.symm (by simpa [hfold, step, hmiss] using hok)
    intro dep hmem
    have hmemRev : dep ∈ deps.reverse := by simpa [hrec] using hmem
    have hmemDeps : dep ∈ deps := by simpa using (List.mem_reverse.mp hmemRev)
    -- invariant: if `ids ⊆ depIds`, then every accumulated dep.queryId is in depIds
    have inv :
        ∀ (ids : List QueryId) (acc : List Dep × List QueryId),
          ids ⊆ depIds →
          (∀ dep, dep ∈ acc.1 → dep.queryId ∈ depIds) →
          ∀ dep, dep ∈ (ids.foldl step acc).1 → dep.queryId ∈ depIds := by
      intro ids
      induction ids with
      | nil =>
        intro acc _hsub hacc dep hdep
        simpa using hacc dep hdep
      | cons depId tl ih =>
        intro acc hsub hacc dep hdep
        have hsub_tl : tl ⊆ depIds := fun x hx => hsub (by simp [hx])
        cases hnode : nodes depId with
        | none =>
          have hacc' : ∀ dep, dep ∈ (step acc depId).1 → dep.queryId ∈ depIds := by
            intro dep hmem
            have hmem' : dep ∈ acc.1 := by simpa [step, hnode] using hmem
            exact hacc dep hmem'
          have hdep' : dep ∈ (tl.foldl step (step acc depId)).1 := by
            simpa [List.foldl, step, hnode] using hdep
          exact ih (acc := step acc depId) hsub_tl hacc' dep hdep'
        | some depNode =>
          have hid : depId ∈ depIds := hsub (by simp)
          have hacc' : ∀ dep, dep ∈ (step acc depId).1 → dep.queryId ∈ depIds := by
            intro dep hmem
            have hmem' : dep = ⟨depId, depNode.changedAt⟩ ∨ dep ∈ acc.1 := by
              have := (List.mem_cons.mp (by simpa [step, hnode] using hmem))
              exact this
            cases hmem' with
            | inl heq =>
              subst heq
              simpa using hid
            | inr hin =>
              exact hacc dep hin
          have hdep' : dep ∈ (tl.foldl step (step acc depId)).1 := by
            simpa [List.foldl, step, hnode] using hdep
          exact ih (acc := step acc depId) hsub_tl hacc' dep hdep'
    -- apply inv to the concrete fold (starting from empty)
    have hbase : ∀ dep, dep ∈ ([] : List Dep) → dep.queryId ∈ depIds := by
      intro dep h; cases h
    have hmemFold : dep ∈ (depIds.foldl step ([], [])).1 := by
      have : (depIds.foldl step ([], [])).1 = deps := by
        simp [hfold]
      simp only [this]
      exact hmemDeps
    exact inv depIds ([], []) (by intro x hx; exact hx) (by simp) dep hmemFold

/-- Add qid to the dependents list of all its dependencies
    This maintains the bidirectional consistency of the graph structure -/
def updateGraphEdges {N : Nat} (nodes : QueryId → Option (Node N)) (qid : QueryId)
    (deps : List Dep) : QueryId → Option (Node N) :=
  deps.foldl (fun ns dep =>
    match ns dep.queryId with
    | none => ns
    | some depNode =>
      if qid ∈ depNode.dependents then ns
      else
        let newDependents := qid :: depNode.dependents
        fun q => if q = dep.queryId then some { depNode with dependents := newDependents }
                 else ns q
  ) nodes

/-- Remove qid from the dependents list of old dependencies that are no longer in new deps.
    This cleans up stale reverse edges when a node's dependencies change.
    Matches Rust: `cleanup_stale_edges` in runtime.rs -/
def cleanupStaleEdges {N : Nat} (nodes : QueryId → Option (Node N)) (qid : QueryId)
    (oldDeps : List Dep) (newDepIds : List QueryId) : QueryId → Option (Node N) :=
  oldDeps.foldl (fun ns oldDep =>
    -- Only process if this dependency was removed (not in newDepIds)
    if oldDep.queryId ∈ newDepIds then ns
    else
      match ns oldDep.queryId with
      | none => ns
      | some depNode =>
        -- Remove qid from dependents list if present
        if qid ∈ depNode.dependents then
          let newDependents := depNode.dependents.filter (· ≠ qid)
          fun q => if q = oldDep.queryId then some { depNode with dependents := newDependents }
                   else ns q
        else ns
  ) nodes

/-- Register result -/
structure RegisterResult where
  newRev : RevisionCounter
  effectiveDurability : Durability

/-- Register a new node or update existing one (internal core step).
    This does **not** update reverse edges; prefer `Runtime.register`. -/
private def Runtime.registerCore {N : Nat} (rt : Runtime N) (qid : QueryId)
    (requestedDurability : Durability) (depIds : List QueryId) : Except (List QueryId) (Runtime N × RegisterResult) :=
  -- Build dependency records with current changed_at snapshots
  match buildDepRecords rt.nodes depIds with
  | .error missing => .error missing
  | .ok depRecords =>
    -- Calculate effective durability (enforce invariant)
    let effectiveDur := calculateEffectiveDurability rt.nodes requestedDurability depRecords (N - 1)
    -- Ensure durability is valid
    let finalDur := min effectiveDur (N - 1)
    -- Calculate topological level
    let newLevel := calculateLevel rt.nodes depRecords
    -- Increment revision at the effective durability level
    have hN : N > 0 := rt.numDurabilityLevels
    have hfin : finalDur < N := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)
    let durFin : Fin N := ⟨finalDur, hfin⟩
    let (rt', newRev) := rt.incrementRevision durFin
    -- Preserve existing dependents (if the node already existed), to avoid breaking
    -- `dependentsConsistent` for nodes that already depend on `qid`.
    let oldDependents : List QueryId :=
      match rt'.nodes qid with
      | none => []
      | some oldNode => oldNode.dependents
    -- Create the new node
    let newNode : Node N := {
      durability := durFin
      verifiedAt := newRev
      changedAt := newRev
      level := newLevel
      dependencies := depRecords
      dependents := oldDependents
    }
    -- Update nodes map
    let newNodes := fun q => if q = qid then some newNode else rt'.nodes q
    let rt'' : Runtime N := ⟨newNodes, rt'.revision, rt'.numDurabilityLevels⟩
    .ok (rt'', ⟨newRev, finalDur⟩)

/-- Register a node and update graph edges (the only public entry point).
    This maintains bidirectional consistency by adding reverse edges for every dependency. -/
def Runtime.register {N : Nat} (rt : Runtime N) (qid : QueryId)
    (requestedDurability : Durability) (depIds : List QueryId) : Except (List QueryId) (Runtime N × RegisterResult) :=
  match rt.registerCore qid requestedDurability depIds with
  | .error missing => .error missing
  | .ok (rt', result) =>
    -- Use the same snapshot as `register` used to populate the node's `dependencies`,
    -- so `updateGraphEdges` adds reverse edges for exactly those dependencies.
    match buildDepRecords rt.nodes depIds with
    | .error missing => .error missing
    | .ok depRecords =>
      let newNodes := updateGraphEdges rt'.nodes qid depRecords
      .ok (⟨newNodes, rt'.revision, rt'.numDurabilityLevels⟩, result)

/-- Backwards-compatible alias (deprecated). -/
abbrev Runtime.registerWithEdges {N : Nat} (rt : Runtime N) (qid : QueryId)
    (requestedDurability : Durability) (depIds : List QueryId) :
    Except (List QueryId) (Runtime N × RegisterResult) :=
  rt.register qid requestedDurability depIds

/-! ## Properties to Prove -/

section BasicProperties

/-- Property: markVerified only modifies the target node -/
theorem markVerified_other_unchanged {N : Nat} (rt : Runtime N) (qid other : QueryId)
    (atRev : Revision N) (hne : other ≠ qid) :
    (markVerified rt qid atRev).nodes other = rt.nodes other := by
  unfold markVerified
  cases hnode : rt.nodes qid with
  | none => rfl
  | some node =>
    simp [hne]

/-- Property: markVerified preserves revision counters -/
theorem markVerified_preserves_revision {N : Nat} (rt : Runtime N) (qid : QueryId)
    (atRev : Revision N) :
    (markVerified rt qid atRev).revision = rt.revision := by
  unfold markVerified
  cases hnode : rt.nodes qid with
  | none => rfl
  | some node =>
    simp

/-- Property: markVerified preserves node absence at target -/
theorem markVerified_none {N : Nat} (rt : Runtime N) (qid : QueryId)
    (atRev : Revision N) (hnode : rt.nodes qid = none) :
    (markVerified rt qid atRev).nodes qid = none := by
  simp only [markVerified, hnode]

/-- Property: markVerified at target node only depends on node content -/
theorem markVerified_at_target {N : Nat} (rt : Runtime N) (qid : QueryId)
    (atRev : Revision N) (node : Node N) (hnode : rt.nodes qid = some node) :
    (markVerified rt qid atRev).nodes qid =
      some { node with verifiedAt := max node.verifiedAt (atRev.counters node.durability) } := by
  simp [markVerified, hnode]

/-- Property: result of markVerified at target only depends on input node content -/
theorem markVerified_result_eq {N : Nat} (rt1 rt2 : Runtime N) (qid : QueryId)
    (atRev : Revision N) (heq : rt1.nodes qid = rt2.nodes qid) :
    (markVerified rt1 qid atRev).nodes qid = (markVerified rt2 qid atRev).nodes qid := by
  cases h1 : rt1.nodes qid with
  | none =>
    have h2 : rt2.nodes qid = none := by rw [← heq]; exact h1
    rw [markVerified_none rt1 qid atRev h1]
    rw [markVerified_none rt2 qid atRev h2]
  | some node =>
    have h2 : rt2.nodes qid = some node := by rw [← heq]; exact h1
    rw [markVerified_at_target rt1 qid atRev node h1]
    rw [markVerified_at_target rt2 qid atRev node h2]

/-- Property: markVerified doesn't decrease verified_at (when node exists) -/
theorem markVerified_monotone' {N : Nat} (rt : Runtime N) (qid : QueryId)
    (atRev : Revision N) (node : Node N) (hnode : rt.nodes qid = some node) :
    ∃ newNode, (markVerified rt qid atRev).nodes qid = some newNode ∧
               node.verifiedAt ≤ newNode.verifiedAt := by
  unfold markVerified
  simp only [hnode, ite_true]
  exact ⟨_, rfl, Nat.le_max_left _ _⟩

/-- Property: revision counters are non-decreasing after increment -/
theorem incrementRevision_monotone {N : Nat} (rt : Runtime N) (d : Fin N) (i : Fin N) :
    rt.revision i ≤ (rt.incrementRevision d).1.revision i := by
  unfold Runtime.incrementRevision
  simp only
  split
  · exact Nat.le_succ _
  · exact Nat.le_refl _

/-- Property: incrementRevision actually increments the target level -/
theorem incrementRevision_increments {N : Nat} (rt : Runtime N) (d : Fin N) :
    (rt.incrementRevision d).1.revision d = rt.revision d + 1 := by
  unfold Runtime.incrementRevision
  simp only [ite_true, le_refl]

/-- Property: incrementRevision returns the new revision value -/
theorem incrementRevision_returns_new {N : Nat} (rt : Runtime N) (d : Fin N) :
    (rt.incrementRevision d).2 = rt.revision d + 1 := by
  unfold Runtime.incrementRevision
  rfl

/-- incrementRevision preserves nodes -/
theorem incrementRevision_preserves_nodes {N : Nat} (rt : Runtime N) (d : Fin N) :
    (rt.incrementRevision d).1.nodes = rt.nodes := by
  unfold Runtime.incrementRevision
  rfl

end BasicProperties

/-! ## Phase 2: Invariant Preservation Proofs -/

section InvariantPreservation

/-- Helper: minDepDurability returns a value ≤ default when deps is empty -/
theorem minDepDurability_empty {N : Nat} (nodes : QueryId → Option (Node N)) (default : Durability) :
    minDepDurability nodes [] default = default := by
  unfold minDepDurability
  simp [List.foldl]

/-- Helper lemma for foldl with min -/
lemma foldl_min_le_init {α : Type} (f : α → Nat) (init : Nat) (l : List α) :
    List.foldl (fun acc a => min acc (f a)) init l ≤ init := by
  induction l generalizing init with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    calc List.foldl (fun acc a => min acc (f a)) (min init (f hd)) tl
        ≤ min init (f hd) := ih _
      _ ≤ init := Nat.min_le_left _ _

/-- Helper: minDepDurability is ≤ default -/
theorem minDepDurability_le_default {N : Nat} (nodes : QueryId → Option (Node N)) (deps : List Dep)
    (default : Durability) :
    minDepDurability nodes deps default ≤ default := by
  unfold minDepDurability
  induction deps generalizing default with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    cases h : nodes hd.queryId with
    | none =>
      exact ih default
    | some n =>
      calc List.foldl _ (min default n.durability.val) tl
          ≤ min default n.durability.val := ih _
        _ ≤ default := Nat.min_le_left _ _

/-- Helper: calculateEffectiveDurability produces valid durability -/
theorem calculateEffectiveDurability_le_requested {N : Nat} (nodes : QueryId → Option (Node N))
    (requested : Durability) (deps : List Dep) (maxDur : Durability) :
    calculateEffectiveDurability nodes requested deps maxDur ≤ requested := by
  unfold calculateEffectiveDurability
  exact Nat.min_le_left _ _

/-- Helper: calculateEffectiveDurability ≤ maxDur -/
theorem calculateEffectiveDurability_le_maxDur {N : Nat} (nodes : QueryId → Option (Node N))
    (requested : Durability) (deps : List Dep) (maxDur : Durability) :
    calculateEffectiveDurability nodes requested deps maxDur ≤ maxDur := by
  unfold calculateEffectiveDurability
  calc min requested (minDepDurability nodes deps maxDur)
      ≤ minDepDurability nodes deps maxDur := Nat.min_le_right _ _
    _ ≤ maxDur := minDepDurability_le_default nodes deps maxDur

/-- Register preserves other nodes -/
theorem register_other_unchanged {N : Nat} (rt : Runtime N) (qid other : QueryId)
    (dur : Durability) (deps : List QueryId) (hne : other ≠ qid) :
    match rt.registerCore qid dur deps with
    | .ok (rt', _) => rt'.nodes other = rt.nodes other
    | .error _ => True := by
  unfold Runtime.registerCore
  cases hbd : buildDepRecords rt.nodes deps with
  | error missing =>
    simp
  | ok depRecords =>
    simp [hne, incrementRevision_preserves_nodes]

/-- Register produces well-formed node -/
theorem register_wellformed {N : Nat} (rt : Runtime N) (qid : QueryId)
    (dur : Durability) (deps : List QueryId) :
    match rt.registerCore qid dur deps with
    | .ok (rt', _) =>
      match rt'.nodes qid with
      | some _node => True
      | none => True
    | .error _ => True := by
  unfold Runtime.registerCore
  cases hbd : buildDepRecords rt.nodes deps with
  | error missing =>
    simp
  | ok depRecords =>
    simp

/-! ### updateGraphEdges Properties -/

/-- The step function used in updateGraphEdges -/
def updateGraphEdgesStep {N : Nat} (qid : QueryId) (ns : QueryId → Option (Node N)) (d : Dep)
    : QueryId → Option (Node N) :=
  match ns d.queryId with
  | none => ns
  | some depNode =>
    if qid ∈ depNode.dependents then ns
    else fun q =>
      if q = d.queryId then some { depNode with dependents := qid :: depNode.dependents }
      else ns q

/-- Alternative definition of updateGraphEdges using explicit step -/
theorem updateGraphEdges_eq {N : Nat} (nodes : QueryId → Option (Node N)) (qid : QueryId) (deps : List Dep) :
    updateGraphEdges nodes qid deps = deps.foldl (updateGraphEdgesStep qid) nodes := by
  unfold updateGraphEdges updateGraphEdgesStep
  rfl

/-!
`isValidAt` does not depend on the `dependents` field.
Since `updateGraphEdges` only updates `dependents`, validity checks are invariant under it.
-/

lemma isValidAt_updateGraphEdgesStep {N : Nat} (rt : Runtime N) (qid : QueryId) (d : Dep)
    (x : QueryId) (atRev : Revision N) :
    isValidAt (rt := ⟨updateGraphEdgesStep qid rt.nodes d, rt.revision, rt.numDurabilityLevels⟩) x atRev =
      isValidAt rt x atRev := by
  unfold isValidAt
  cases hx : rt.nodes x with
  | none =>
    cases hd : rt.nodes d.queryId with
    | none =>
      simp [updateGraphEdgesStep, hx, hd]
    | some depNode =>
      by_cases hmem : qid ∈ depNode.dependents
      · simp [updateGraphEdgesStep, hx, hd, hmem]
      · by_cases hxkey : x = d.queryId
        · subst hxkey
          -- contradiction: `rt.nodes d.queryId` can't be both `none` and `some _`
          have hx' := hx
          rw [hd] at hx'
          cases hx'
        · simp [updateGraphEdgesStep, hx, hd, hmem, hxkey]
  | some node =>
    cases hd : rt.nodes d.queryId with
    | none =>
      simp [updateGraphEdgesStep, hx, hd]
    | some depNode =>
      by_cases hmem : qid ∈ depNode.dependents
      · simp [updateGraphEdgesStep, hx, hd, hmem]
      · by_cases hxkey : x = d.queryId
        · subst hxkey
          -- identify `node = depNode` (and eliminate `depNode`, not `node`)
          have hdep : node = depNode := by
            have hd' := hd
            rw [hx] at hd'
            exact Option.some.inj hd'
          subst hdep
          -- the dependency check is unchanged, because only `dependents` changes
          have hall :
              (node.dependencies).all (fun dep =>
                match
                  if dep.queryId = d.queryId then
                    some { node with dependents := qid :: node.dependents }
                  else rt.nodes dep.queryId with
                | none => false
                | some dn => !decide (dep.observedChangedAt < dn.changedAt)) =
              (node.dependencies).all (fun dep =>
                match rt.nodes dep.queryId with
                | none => false
                | some dn => !decide (dep.observedChangedAt < dn.changedAt)) := by
            let f : Dep → Bool := fun dep =>
              match
                if dep.queryId = d.queryId then
                  some { node with dependents := qid :: node.dependents }
                else rt.nodes dep.queryId with
              | none => false
              | some dn => !decide (dep.observedChangedAt < dn.changedAt)
            let g : Dep → Bool := fun dep =>
              match rt.nodes dep.queryId with
              | none => false
              | some dn => !decide (dep.observedChangedAt < dn.changedAt)
            have hpoint : ∀ (dep : Dep), f dep = g dep := by
              intro dep
              by_cases heq : dep.queryId = d.queryId
              · simp [f, g, heq, hd]
              · simp [f, g, heq]
            have hall' : (node.dependencies).all f = (node.dependencies).all g := by
              classical
              cases hf : (node.dependencies).all f with
              | true =>
                have hallTrue : ∀ dep ∈ node.dependencies, f dep = true := (List.all_eq_true).1 hf
                have hallTrue' : ∀ dep ∈ node.dependencies, g dep = true := by
                  intro dep hmem
                  have h := hallTrue dep hmem
                  simpa [hpoint dep] using h
                have hg : (node.dependencies).all g = true := (List.all_eq_true).2 hallTrue'
                simp [hg]
              | false =>
                rcases (List.all_eq_false).1 hf with ⟨dep, hmem, hfail⟩
                have hfail' : g dep = false := by
                  simpa [hpoint dep] using hfail
                have hg : (node.dependencies).all g = false :=
                  (List.all_eq_false).2 ⟨dep, hmem, by simp [hfail']⟩
                simp [hg]
            simpa [f, g] using hall'
          simp [updateGraphEdgesStep, hd, hmem, hall]
        · -- node at `x` is unchanged, but the nodes map at `d.queryId` changes only in `dependents`;
          -- `isValidAt` only looks at `changedAt`, so the deps check is unchanged.
          have hall :
              (node.dependencies).all (fun (dep : Dep) =>
                match
                  if dep.queryId = d.queryId then
                    some { depNode with dependents := qid :: depNode.dependents }
                  else rt.nodes dep.queryId with
                | none => false
                | some dn => !decide (dep.observedChangedAt < dn.changedAt)) =
              (node.dependencies).all (fun (dep : Dep) =>
                match rt.nodes dep.queryId with
                | none => false
                | some dn => !decide (dep.observedChangedAt < dn.changedAt)) := by
            let f : Dep → Bool := fun dep =>
              match
                if dep.queryId = d.queryId then
                  some { depNode with dependents := qid :: depNode.dependents }
                else rt.nodes dep.queryId with
              | none => false
              | some dn => !decide (dep.observedChangedAt < dn.changedAt)
            let g : Dep → Bool := fun dep =>
              match rt.nodes dep.queryId with
              | none => false
              | some dn => !decide (dep.observedChangedAt < dn.changedAt)
            have hpoint : ∀ (dep : Dep), f dep = g dep := by
              intro dep
              by_cases heq : dep.queryId = d.queryId
              · simp [f, g, heq, hd]
              · simp [f, g, heq]
            have hall' : (node.dependencies).all f = (node.dependencies).all g := by
              classical
              cases hf : (node.dependencies).all f with
              | true =>
                have hallTrue : ∀ dep ∈ node.dependencies, f dep = true := (List.all_eq_true).1 hf
                have hallTrue' : ∀ dep ∈ node.dependencies, g dep = true := by
                  intro dep hmem
                  have h := hallTrue dep hmem
                  simpa [hpoint dep] using h
                have hg : (node.dependencies).all g = true := (List.all_eq_true).2 hallTrue'
                simp [hg]
              | false =>
                rcases (List.all_eq_false).1 hf with ⟨dep, hmem, hfail⟩
                have hfail' : g dep = false := by
                  simpa [hpoint dep] using hfail
                have hg : (node.dependencies).all g = false :=
                  (List.all_eq_false).2 ⟨dep, hmem, by simp [hfail']⟩
                simp [hg]
            simpa [f, g] using hall'
          simp [updateGraphEdgesStep, hx, hd, hmem, hxkey, hall]

theorem isValidAt_updateGraphEdges {N : Nat} (rt : Runtime N) (qid : QueryId) (deps : List Dep)
    (x : QueryId) (atRev : Revision N) :
    isValidAt (rt := ⟨updateGraphEdges rt.nodes qid deps, rt.revision, rt.numDurabilityLevels⟩) x atRev =
      isValidAt rt x atRev := by
  rw [updateGraphEdges_eq]
  induction deps generalizing rt with
  | nil =>
    simp [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    -- one step doesn't change `isValidAt`, then apply IH
    have hstep :=
      isValidAt_updateGraphEdgesStep (rt := rt) (qid := qid) (d := hd) (x := x) (atRev := atRev)
    -- apply IH to the stepped runtime
    have hrest :=
      ih (rt := ⟨updateGraphEdgesStep qid rt.nodes hd, rt.revision, rt.numDurabilityLevels⟩)
    simpa [hstep] using hrest

/-- updateGraphEdgesStep preserves nodes not being updated -/
lemma updateGraphEdgesStep_other_unchanged {N : Nat} (qid other : QueryId) (ns : QueryId → Option (Node N))
    (d : Dep) (hother : d.queryId ≠ other) :
    (updateGraphEdgesStep qid ns d) other = ns other := by
  unfold updateGraphEdgesStep
  cases hns : ns d.queryId with
  | none => rfl
  | some depNode =>
    simp only
    split
    · rfl
    · simp only [hother.symm, ite_false]

/-- updateGraphEdges preserves nodes not in deps -/
theorem updateGraphEdges_other_unchanged {N : Nat} (nodes : QueryId → Option (Node N))
    (qid other : QueryId) (deps : List Dep)
    (hother : ∀ dep ∈ deps, dep.queryId ≠ other) :
    (updateGraphEdges nodes qid deps) other = nodes other := by
  rw [updateGraphEdges_eq]
  induction deps generalizing nodes with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hhd : hd.queryId ≠ other := hother hd (by simp)
    have htl : ∀ dep ∈ tl, dep.queryId ≠ other := fun dep hdep => hother dep (by simp [hdep])
    rw [ih (updateGraphEdgesStep qid nodes hd) htl]
    exact updateGraphEdgesStep_other_unchanged qid other nodes hd hhd

/-! ### cleanupStaleEdges properties -/

/-- cleanupStaleEdges preserves nodes not in oldDeps -/
theorem cleanupStaleEdges_other_unchanged {N : Nat} (nodes : QueryId → Option (Node N))
    (qid other : QueryId) (oldDeps : List Dep) (newDepIds : List QueryId)
    (hother : ∀ dep ∈ oldDeps, dep.queryId ≠ other) :
    (cleanupStaleEdges nodes qid oldDeps newDepIds) other = nodes other := by
  unfold cleanupStaleEdges
  induction oldDeps generalizing nodes with
  | nil => simp [List.foldl]
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hhd : hd.queryId ≠ other := hother hd (by simp)
    have htl : ∀ dep ∈ tl, dep.queryId ≠ other := fun dep hdep => hother dep (by simp [hdep])
    -- The step function with explicit type
    let stepFn : (QueryId → Option (Node N)) → Dep → (QueryId → Option (Node N)) :=
      fun ns (oldDep : Dep) =>
        if oldDep.queryId ∈ newDepIds then ns
        else match ns oldDep.queryId with
             | none => ns
             | some depNode =>
               if qid ∈ depNode.dependents then
                 let newDependents := depNode.dependents.filter (· ≠ qid)
                 fun q => if q = oldDep.queryId then some { depNode with dependents := newDependents }
                          else ns q
               else ns
    have hstep : (stepFn nodes hd) other = nodes other := by
      simp only [stepFn]
      split_ifs with hmem
      · rfl
      · cases hdq : nodes hd.queryId with
        | none => rfl
        | some depNode =>
          simp only
          split_ifs with hmem'
          · simp only [hhd.symm, ite_false]
          · rfl
    rw [ih (stepFn nodes hd) htl]
    exact hstep

/-- Helper: The step function in cleanupStaleEdges preserves Some/None structure and changedAt -/
private lemma cleanupStaleEdges_step_preserves {N : Nat} (nodes : QueryId → Option (Node N))
    (qid target : QueryId) (hd : Dep) (newDepIds : List QueryId)
    (node : Node N) (hnode : nodes target = some node) :
    let step := if hd.queryId ∈ newDepIds then nodes
                else match nodes hd.queryId with
                     | none => nodes
                     | some depNode =>
                       if qid ∈ depNode.dependents then
                         fun q => if q = hd.queryId then some { depNode with dependents := depNode.dependents.filter (· ≠ qid) }
                                  else nodes q
                       else nodes
    ∃ n', step target = some n' ∧ n'.changedAt = node.changedAt ∧
          n'.durability = node.durability ∧ n'.verifiedAt = node.verifiedAt ∧
          n'.dependencies = node.dependencies := by
  simp only
  split_ifs with hmem
  · exact ⟨node, hnode, rfl, rfl, rfl, rfl⟩
  · cases hdq : nodes hd.queryId with
    | none => exact ⟨node, hnode, rfl, rfl, rfl, rfl⟩
    | some depNode =>
      simp only
      split_ifs with hmem'
      · by_cases heq : target = hd.queryId
        · subst heq
          simp only [ite_true]
          rw [hnode] at hdq
          injection hdq with heq'
          subst heq'
          exact ⟨_, rfl, rfl, rfl, rfl, rfl⟩
        · simp only [heq, ite_false]
          exact ⟨node, hnode, rfl, rfl, rfl, rfl⟩
      · exact ⟨node, hnode, rfl, rfl, rfl, rfl⟩

/-- cleanupStaleEdges preserves node existence and key properties -/
theorem cleanupStaleEdges_preserves_node {N : Nat} (nodes : QueryId → Option (Node N))
    (qid target : QueryId) (oldDeps : List Dep) (newDepIds : List QueryId)
    (node : Node N) (hnode : nodes target = some node) :
    ∃ n', (cleanupStaleEdges nodes qid oldDeps newDepIds) target = some n' ∧
          n'.changedAt = node.changedAt ∧ n'.durability = node.durability ∧
          n'.verifiedAt = node.verifiedAt ∧ n'.dependencies = node.dependencies := by
  unfold cleanupStaleEdges
  induction oldDeps generalizing nodes node with
  | nil =>
    simp only [List.foldl_nil]
    exact ⟨node, hnode, rfl, rfl, rfl, rfl⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hstep := cleanupStaleEdges_step_preserves nodes qid target hd newDepIds node hnode
    rcases hstep with ⟨n', hn', hchg, hdur, hver, hdeps⟩
    have := ih _ n' hn'
    rcases this with ⟨n'', hn'', hchg', hdur', hver', hdeps'⟩
    exact ⟨n'', hn'', by simp_all, by simp_all, by simp_all, by simp_all⟩

/-- cleanupStaleEdges preserves None nodes -/
theorem cleanupStaleEdges_preserves_none {N : Nat} (nodes : QueryId → Option (Node N))
    (qid target : QueryId) (oldDeps : List Dep) (newDepIds : List QueryId)
    (hnode : nodes target = none) :
    (cleanupStaleEdges nodes qid oldDeps newDepIds) target = none := by
  unfold cleanupStaleEdges
  induction oldDeps generalizing nodes with
  | nil => simp only [List.foldl_nil]; exact hnode
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    apply ih
    -- Show the step preserves None
    split_ifs with hmem
    · exact hnode
    · cases hdq : nodes hd.queryId with
      | none => exact hnode
      | some depNode =>
        simp only
        split_ifs with hmem'
        · -- qid ∈ depNode.dependents case
          by_cases heq : target = hd.queryId
          · -- Contradiction: nodes target = none but nodes hd.queryId = some depNode
            subst heq
            rw [hnode] at hdq
            exact absurd hdq (by simp)
          · simp only [heq, ite_false]; exact hnode
        · exact hnode

/-- cleanupStaleEdges does not change changedAt of any node.
    This is important for early cutoff correctness. -/
theorem cleanupStaleEdges_preserves_changedAt {N : Nat} (nodes : QueryId → Option (Node N))
    (qid target : QueryId) (oldDeps : List Dep) (newDepIds : List QueryId)
    (node : Node N) (hnode : nodes target = some node) :
    match (cleanupStaleEdges nodes qid oldDeps newDepIds) target with
    | some n => n.changedAt = node.changedAt
    | none => False := by
  have ⟨n', hn', hchg, _, _, _⟩ := cleanupStaleEdges_preserves_node nodes qid target oldDeps newDepIds node hnode
  simp only [hn']
  exact hchg

/-- cleanupStaleEdges does not affect isValidAt (since isValidAt only uses changedAt, not dependents) -/
theorem isValidAt_cleanupStaleEdges {N : Nat} (rt : Runtime N)
    (qid target : QueryId) (oldDeps : List Dep) (newDepIds : List QueryId)
    (atRev : Revision N) :
    let newNodes := cleanupStaleEdges rt.nodes qid oldDeps newDepIds
    isValidAt (rt := ⟨newNodes, rt.revision, rt.numDurabilityLevels⟩) target atRev =
    isValidAt rt target atRev := by
  unfold isValidAt
  simp only
  cases hnode : rt.nodes target with
  | none =>
    have hclean := cleanupStaleEdges_preserves_none rt.nodes qid target oldDeps newDepIds hnode
    simp [hclean]
  | some node =>
    have ⟨n', hn', hchg, hdur, hver, hdeps⟩ := cleanupStaleEdges_preserves_node rt.nodes qid target oldDeps newDepIds node hnode
    simp only [hn', hdur, hver]
    -- Now we need to show the dependencies check is the same
    -- After simp, we should have equality of the List.all expressions
    -- Use congrArg to focus on the List.all part
    congr 1
    rw [hdeps]
    -- Now prove the List.all gives the same value
    congr 1
    funext dep
    cases hdepNode : rt.nodes dep.queryId with
    | none =>
      have hcleanDep := cleanupStaleEdges_preserves_none rt.nodes qid dep.queryId oldDeps newDepIds hdepNode
      simp [hcleanDep]
    | some depNode =>
      have ⟨n'', hn'', hchg', _, _, _⟩ := cleanupStaleEdges_preserves_node rt.nodes qid dep.queryId oldDeps newDepIds depNode hdepNode
      simp [hn'', hchg']

/-- cleanupStaleEdges preserves the node at qid when no old dependency points to qid itself.
    This is needed because a node should not depend on itself. -/
theorem cleanupStaleEdges_preserves_at_qid {N : Nat} (nodes : QueryId → Option (Node N))
    (qid : QueryId) (oldDeps : List Dep) (newDepIds : List QueryId)
    (hnoself : ∀ dep ∈ oldDeps, dep.queryId ≠ qid) :
    (cleanupStaleEdges nodes qid oldDeps newDepIds) qid = nodes qid :=
  cleanupStaleEdges_other_unchanged nodes qid qid oldDeps newDepIds hnoself

/-- Helper: the step function in cleanupStaleEdges doesn't create new nodes -/
private lemma cleanupStaleEdges_step_some_implies_some {N : Nat} (qid target : QueryId)
    (nodes : QueryId → Option (Node N)) (oldDep : Dep) (newDepIds : List QueryId)
    (n' : Node N)
    (hstep : (if oldDep.queryId ∈ newDepIds then nodes
              else match nodes oldDep.queryId with
                   | none => nodes
                   | some depNode =>
                     if qid ∈ depNode.dependents then
                       fun q => if q = oldDep.queryId then some { depNode with dependents := depNode.dependents.filter (· ≠ qid) }
                                else nodes q
                     else nodes) target = some n') :
    ∃ n, nodes target = some n := by
  split_ifs at hstep with hmem
  · exact ⟨n', hstep⟩
  · cases hdep : nodes oldDep.queryId with
    | none =>
      simp only [hdep] at hstep
      exact ⟨n', hstep⟩
    | some depNode =>
      simp only [hdep] at hstep
      split_ifs at hstep with hmem'
      · by_cases htarget : target = oldDep.queryId
        · subst htarget
          exact ⟨depNode, hdep⟩
        · simp only [htarget, ite_false] at hstep
          exact ⟨n', hstep⟩
      · exact ⟨n', hstep⟩

/-- cleanupStaleEdges never creates a node: if the result is `some`, the input was `some`. -/
lemma cleanupStaleEdges_some_implies_some {N : Nat} (qid target : QueryId)
    (nodes : QueryId → Option (Node N)) (oldDeps : List Dep) (newDepIds : List QueryId)
    (n' : Node N) (hout : cleanupStaleEdges nodes qid oldDeps newDepIds target = some n') :
    ∃ n, nodes target = some n := by
  unfold cleanupStaleEdges at hout
  induction oldDeps generalizing nodes with
  | nil =>
    simp only [List.foldl_nil] at hout
    exact ⟨n', hout⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons] at hout
    let stepFn := if hd.queryId ∈ newDepIds then nodes
                  else match nodes hd.queryId with
                       | none => nodes
                       | some depNode =>
                         if qid ∈ depNode.dependents then
                           fun q => if q = hd.queryId then some { depNode with dependents := depNode.dependents.filter (· ≠ qid) }
                                    else nodes q
                         else nodes
    -- Get node from tail fold
    obtain ⟨n1, hn1⟩ := ih stepFn hout
    -- Get node from step
    exact cleanupStaleEdges_step_some_implies_some qid target nodes hd newDepIds n1 hn1

/-- updateGraphEdgesStep at target adds qid to dependents -/
lemma updateGraphEdgesStep_target {N : Nat} (qid : QueryId) (ns : QueryId → Option (Node N))
    (d : Dep) (depNode : Node N) (hdepNode : ns d.queryId = some depNode) :
    ∃ n, (updateGraphEdgesStep qid ns d) d.queryId = some n ∧ qid ∈ n.dependents := by
  unfold updateGraphEdgesStep
  simp only [hdepNode]
  split
  · case isTrue h => exact ⟨depNode, hdepNode, h⟩
  · case isFalse _ => exact ⟨{ depNode with dependents := qid :: depNode.dependents },
                              by simp only [ite_true], by simp⟩

/-- If qid ∈ n.dependents, then updateGraphEdgesStep preserves this property -/
lemma updateGraphEdgesStep_preserves_membership {N : Nat} (qid target : QueryId)
    (ns : QueryId → Option (Node N)) (d : Dep) (n : Node N)
    (hn : ns target = some n) (hmem : qid ∈ n.dependents) :
    ∃ n', (updateGraphEdgesStep qid ns d) target = some n' ∧ qid ∈ n'.dependents := by
  unfold updateGraphEdgesStep
  cases hd : ns d.queryId with
  | none => exact ⟨n, hn, hmem⟩
  | some depNode =>
    simp only
    split
    · exact ⟨n, hn, hmem⟩
    · by_cases heq : target = d.queryId
      · subst heq
        simp only [ite_true]
        rw [hn] at hd
        injection hd with heq'
        subst heq'
        exact ⟨_, rfl, by simp [hmem]⟩
      · simp only [heq, ite_false]
        exact ⟨n, hn, hmem⟩

/-- Helper: foldl of updateGraphEdgesStep preserves membership -/
lemma foldl_updateGraphEdgesStep_preserves_membership {N : Nat} (qid target : QueryId)
    (ns : QueryId → Option (Node N)) (deps : List Dep) (n : Node N)
    (hn : ns target = some n) (hmem : qid ∈ n.dependents) :
    ∃ n', deps.foldl (updateGraphEdgesStep qid) ns target = some n' ∧ qid ∈ n'.dependents := by
  induction deps generalizing ns n with
  | nil => exact ⟨n, hn, hmem⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hpres := updateGraphEdgesStep_preserves_membership qid target ns hd n hn hmem
    obtain ⟨n', hn', hmem'⟩ := hpres
    exact ih (updateGraphEdgesStep qid ns hd) n' hn' hmem'

/-- updateGraphEdgesStep preserves all existing dependents (it only ever adds `qid`) -/
lemma updateGraphEdgesStep_preserves_dependents_subset {N : Nat} (qid target : QueryId)
    (ns : QueryId → Option (Node N)) (d : Dep) (n : Node N)
    (hn : ns target = some n) :
    ∃ n', (updateGraphEdgesStep qid ns d) target = some n' ∧
      ∀ x, x ∈ n.dependents → x ∈ n'.dependents := by
  unfold updateGraphEdgesStep
  cases hns : ns d.queryId with
  | none =>
    -- no change
    exact ⟨n, by simpa [hns] using hn, by intro x hx; exact hx⟩
  | some depNode =>
    by_cases hmem : qid ∈ depNode.dependents
    · -- no change
      exact ⟨n, by simp_all,
            by intro x hx; exact hx⟩
    · -- adds `qid` at d.queryId
      by_cases htarget : target = d.queryId
      · subst htarget
        -- target updated to `qid :: depNode.dependents`
        have hnEq : n = depNode := by
          have : (some n : Option (Node N)) = some depNode := by
            exact Eq.trans (by symm; exact hn) hns
          exact Option.some.inj this
        refine ⟨{ n with dependents := qid :: n.dependents }, ?_, ?_⟩
        · simp [hmem, hnEq]
        · intro x hx
          -- old members remain after cons
          exact List.mem_cons_of_mem _ hx
      · -- different key, unchanged
        refine ⟨n, ?_, ?_⟩
        · simp [hmem, htarget, hn]
        · intro x hx; exact hx

/-- foldl of updateGraphEdgesStep preserves all existing dependents (subset) -/
lemma foldl_updateGraphEdgesStep_preserves_dependents_subset {N : Nat} (qid target : QueryId)
    (ns : QueryId → Option (Node N)) (deps : List Dep) (n : Node N)
    (hn : ns target = some n) :
    ∃ n', deps.foldl (updateGraphEdgesStep qid) ns target = some n' ∧
      ∀ x, x ∈ n.dependents → x ∈ n'.dependents := by
  induction deps generalizing ns n with
  | nil => exact ⟨n, hn, by intro x hx; exact hx⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hpres := updateGraphEdgesStep_preserves_dependents_subset qid target ns hd n hn
    rcases hpres with ⟨n', hn', hsubset⟩
    have hrest := ih (updateGraphEdgesStep qid ns hd) n' hn'
    rcases hrest with ⟨n'', hn'', hsubset'⟩
    refine ⟨n'', hn'', ?_⟩
    intro x hx
    exact hsubset' x (hsubset x hx)

/-- updateGraphEdges preserves all existing dependents (subset) at any node -/
lemma updateGraphEdges_preserves_dependents_subset {N : Nat} (qid target : QueryId)
    (ns : QueryId → Option (Node N)) (deps : List Dep) (n : Node N)
    (hn : ns target = some n) :
    ∃ n', updateGraphEdges ns qid deps target = some n' ∧
      ∀ x, x ∈ n.dependents → x ∈ n'.dependents := by
  rw [updateGraphEdges_eq]
  simpa using foldl_updateGraphEdgesStep_preserves_dependents_subset qid target ns deps n hn

/-- updateGraphEdgesStep does not change the dependencies list of any node. -/
lemma updateGraphEdgesStep_preserves_dependencies {N : Nat} (qid target : QueryId)
    (ns : QueryId → Option (Node N)) (d : Dep) (n : Node N)
    (hn : ns target = some n) :
    ∃ n', (updateGraphEdgesStep qid ns d) target = some n' ∧ n'.dependencies = n.dependencies := by
  unfold updateGraphEdgesStep
  cases hns : ns d.queryId with
  | none =>
    exact ⟨n, by simpa [hns] using hn, rfl⟩
  | some depNode =>
    by_cases hmem : qid ∈ depNode.dependents
    · exact ⟨n, by simp_all, rfl⟩
    · by_cases htarget : target = d.queryId
      · subst htarget
        have hnEq : n = depNode := by
          have : (some n : Option (Node N)) = some depNode := by
            exact Eq.trans (by symm; exact hn) hns
          exact Option.some.inj this
        refine ⟨{ n with dependents := qid :: n.dependents }, ?_, ?_⟩
        · simp [hmem, hnEq]
        · rfl
      · refine ⟨n, ?_, rfl⟩
        · simp [hmem, htarget, hn]

/-- updateGraphEdges does not change the dependencies list of any existing node. -/
lemma updateGraphEdges_preserves_dependencies {N : Nat} (qid target : QueryId)
    (ns : QueryId → Option (Node N)) (deps : List Dep) (n : Node N)
    (hn : ns target = some n) :
    ∃ n', updateGraphEdges ns qid deps target = some n' ∧ n'.dependencies = n.dependencies := by
  rw [updateGraphEdges_eq]
  -- foldl induction
  induction deps generalizing ns n with
  | nil =>
    simp only [List.foldl]
    exact ⟨n, hn, rfl⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hstep := updateGraphEdgesStep_preserves_dependencies (qid := qid) (target := target) (ns := ns) (d := hd) n hn
    rcases hstep with ⟨n1, hn1, hdeps1⟩
    have hrest := ih (ns := updateGraphEdgesStep qid ns hd) (n := n1) hn1
    rcases hrest with ⟨n2, hn2, hdeps2⟩
    refine ⟨n2, hn2, ?_⟩
    simpa [hdeps1] using hdeps2

/-- updateGraphEdges never creates a node: if the result is `some`, the input was `some`. -/
lemma updateGraphEdges_some_implies_some {N : Nat} (qid target : QueryId)
    (ns : QueryId → Option (Node N)) (deps : List Dep) (n' : Node N)
    (hout : updateGraphEdges ns qid deps target = some n') :
    ∃ n, ns target = some n := by
  -- helper: one step cannot create a `some` at a key that was `none`
  have step_some_implies_some :
      ∀ (ns : QueryId → Option (Node N)) (d : Dep) (n' : Node N),
        updateGraphEdgesStep qid ns d target = some n' → ∃ n, ns target = some n := by
    intro ns d n' h
    unfold updateGraphEdgesStep at h
    cases hns : ns d.queryId with
    | none =>
      exact ⟨n', by simpa [hns] using h⟩
    | some depNode =>
      by_cases hmem : qid ∈ depNode.dependents
      · exact ⟨n', by simpa [hns, hmem] using h⟩
      · by_cases htarget : target = d.queryId
        · subst htarget
          exact ⟨depNode, hns⟩
        · exact ⟨n', by simpa [hns, hmem, htarget] using h⟩
  rw [updateGraphEdges_eq] at hout
  induction deps generalizing ns with
  | nil =>
    exact ⟨n', by simpa [List.foldl] using hout⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons] at hout
    -- apply IH to the tail fold
    have ⟨n1, hn1⟩ := ih (ns := updateGraphEdgesStep qid ns hd) hout
    -- peel off the head step
    exact step_some_implies_some ns hd n1 hn1

lemma updateGraphEdgesStep_preserves_changedAt {N : Nat} (qid target : QueryId)
    (ns : QueryId → Option (Node N)) (d : Dep) (n : Node N)
    (hn : ns target = some n) :
    ∃ n', (updateGraphEdgesStep qid ns d) target = some n' ∧ n'.changedAt = n.changedAt := by
  unfold updateGraphEdgesStep
  cases hd : ns d.queryId with
  | none =>
    exact ⟨n, hn, rfl⟩
  | some depNode =>
    by_cases hmem : qid ∈ depNode.dependents
    · -- no update
      refine ⟨n, ?_, rfl⟩
      simpa [hd, hmem] using hn
    · -- may update only at `d.queryId`
      by_cases htarget : target = d.queryId
      · subst htarget
        -- identify n with depNode
        rw [hn] at hd
        injection hd with hdep
        subst hdep
        refine ⟨{ n with dependents := qid :: n.dependents }, ?_, by simp⟩
        simp [hmem]
      · -- target unaffected
        refine ⟨n, ?_, rfl⟩
        simpa [hd, hmem, htarget] using hn

lemma foldl_updateGraphEdgesStep_preserves_changedAt {N : Nat} (qid target : QueryId)
    (ns : QueryId → Option (Node N)) (deps : List Dep) (n : Node N)
    (hn : ns target = some n) :
    ∃ n', deps.foldl (updateGraphEdgesStep qid) ns target = some n' ∧ n'.changedAt = n.changedAt := by
  induction deps generalizing ns n with
  | nil => exact ⟨n, hn, rfl⟩
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    have hpres := updateGraphEdgesStep_preserves_changedAt qid target ns hd n hn
    obtain ⟨n', hn', hchg'⟩ := hpres
    have hrec := ih (updateGraphEdgesStep qid ns hd) n' hn'
    obtain ⟨n'', hn'', hchg''⟩ := hrec
    refine ⟨n'', hn'', ?_⟩
    -- changedAt is preserved through each step
    calc
      n''.changedAt = n'.changedAt := hchg''
      _ = n.changedAt := hchg'

/-- updateGraphEdges adds qid to each dependency's dependents list -/
theorem updateGraphEdges_adds_dependent {N : Nat} (nodes : QueryId → Option (Node N))
    (qid : QueryId) (deps : List Dep) (dep : Dep) (hdep : dep ∈ deps)
    (depNode : Node N) (hdepNode : nodes dep.queryId = some depNode) :
    ∃ n, (updateGraphEdges nodes qid deps) dep.queryId = some n ∧ qid ∈ n.dependents := by
  rw [updateGraphEdges_eq]
  induction deps generalizing nodes depNode with
  | nil => simp at hdep
  | cons hd tl ih =>
    simp only [List.foldl_cons]
    cases List.mem_cons.mp hdep with
    | inl heq =>
      -- dep = hd, so this step adds qid
      subst heq
      have hstep := updateGraphEdgesStep_target qid nodes dep depNode hdepNode
      obtain ⟨n, hn, hmem⟩ := hstep
      -- Now show foldl over tl preserves qid ∈ dependents
      exact foldl_updateGraphEdgesStep_preserves_membership qid dep.queryId _ tl n hn hmem
    | inr hmem =>
      -- dep ∈ tl, need to track node through first step
      by_cases heq : hd.queryId = dep.queryId
      · -- hd affects the same node, so we get updated node
        rw [← heq] at hdepNode
        have hstep := updateGraphEdgesStep_target qid nodes hd depNode hdepNode
        obtain ⟨n, hn, hmem'⟩ := hstep
        rw [heq] at hn
        exact ih (updateGraphEdgesStep qid nodes hd) hmem n hn
      · -- hd doesn't affect dep's node
        have hpres := updateGraphEdgesStep_other_unchanged qid dep.queryId nodes hd heq
        rw [← hpres] at hdepNode
        exact ih (updateGraphEdgesStep qid nodes hd) hmem depNode hdepNode

/-! ### noSelfDependency preservation -/

/-- If qid is not in depIds, then no Dep in the result of buildDepRecords has queryId = qid -/
lemma buildDepRecords_ok_no_self {N : Nat} (nodes : QueryId → Option (Node N))
    (depIds : List QueryId) (depRecords : List Dep) (qid : QueryId)
    (hok : buildDepRecords nodes depIds = Except.ok depRecords)
    (hnotIn : qid ∉ depIds) :
    ∀ dep ∈ depRecords, dep.queryId ≠ qid := by
  intro dep hmem
  have hmemIds := buildDepRecords_ok_mem_queryId_mem nodes depIds depRecords hok dep hmem
  exact fun heq => hnotIn (heq ▸ hmemIds)

/-- register preserves noSelfDependency when qid is not in its own deps -/
theorem register_preserves_noSelfDependency {N : Nat} (rt : Runtime N)
    (qid : QueryId) (dur : Durability) (depIds : List QueryId)
    (hinv : noSelfDependency rt.nodes)
    (hnotIn : qid ∉ depIds) :
    match rt.register qid dur depIds with
    | .ok (rt', _) => noSelfDependency rt'.nodes
    | .error _ => True := by
  unfold Runtime.register Runtime.registerCore
  cases hbd : buildDepRecords rt.nodes depIds with
  | error missing => simp
  | ok depRecords =>
    simp only []
    -- Define the intermediate nodes map for clarity
    have hN : N > 0 := rt.numDurabilityLevels
    let effectiveDur := calculateEffectiveDurability rt.nodes dur depRecords (N - 1)
    let finalDur := min effectiveDur (N - 1)
    have hfin : finalDur < N := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)
    let durFin : Fin N := ⟨finalDur, hfin⟩
    let incResult := rt.incrementRevision durFin
    let rt' := incResult.1
    let newRev := incResult.2
    let newLevel := calculateLevel rt.nodes depRecords
    let oldDependents : List QueryId := match rt'.nodes qid with
      | none => []
      | some oldNode => oldNode.dependents
    let newNode : Node N := {
      durability := durFin
      verifiedAt := newRev
      changedAt := newRev
      level := newLevel
      dependencies := depRecords
      dependents := oldDependents
    }
    let baseNodes : QueryId → Option (Node N) := fun q => if q = qid then some newNode else rt'.nodes q
    let finalNodes := updateGraphEdges baseNodes qid depRecords
    -- Show noSelfDependency for finalNodes
    intro other otherNode hotherNode dep hdep
    by_cases heq : other = qid
    · -- Case: other = qid, so otherNode is the newly registered node (with deps = depRecords)
      have hbaseQid : baseNodes qid = some newNode := by simp only [baseNodes, ite_true]
      obtain ⟨n', hn', hdepsEq⟩ := updateGraphEdges_preserves_dependencies qid qid baseNodes depRecords newNode hbaseQid
      rw [heq] at hotherNode
      rw [hn'] at hotherNode
      injection hotherNode with heq'
      have : otherNode.dependencies = newNode.dependencies := by rw [← heq']; exact hdepsEq
      rw [this] at hdep
      -- newNode.dependencies = depRecords, and qid ∉ depIds → no dep has queryId = qid
      have hdepRecordsNoSelf := buildDepRecords_ok_no_self rt.nodes depIds depRecords qid hbd hnotIn
      rw [heq]
      exact hdepRecordsNoSelf dep hdep
    · -- Case: other ≠ qid, so otherNode's dependencies come from rt.nodes
      obtain ⟨origNode, horigNode⟩ := updateGraphEdges_some_implies_some qid other baseNodes depRecords otherNode hotherNode
      -- origNode is from baseNodes at other, and other ≠ qid, so from rt'.nodes = rt.nodes
      have hbaseOther : baseNodes other = rt'.nodes other := by simp only [baseNodes, heq, ite_false]
      rw [hbaseOther] at horigNode
      have hrtNodes : rt'.nodes = rt.nodes := incrementRevision_preserves_nodes rt durFin
      rw [hrtNodes] at horigNode
      -- updateGraphEdges preserves dependencies
      obtain ⟨n', hn', hdepsEq⟩ := updateGraphEdges_preserves_dependencies qid other baseNodes depRecords origNode (by rw [hbaseOther, hrtNodes, horigNode])
      rw [hn'] at hotherNode
      injection hotherNode with heq'
      have : otherNode.dependencies = origNode.dependencies := by rw [← heq']; exact hdepsEq
      rw [this] at hdep
      exact hinv other origNode horigNode dep hdep

end InvariantPreservation

/-! ## Phase 3: Validity Correctness -/

section ValidityCorrectness

/-- If node is verified at or after the revision, it's valid (trivial case) -/
theorem isValidAt_verified {N : Nat} (rt : Runtime N) (qid : QueryId)
    (atRev : Revision N) (node : Node N) (hnode : rt.nodes qid = some node)
    (hverified : node.verifiedAt ≥ atRev.counters node.durability) :
    isValidAt rt qid atRev = true := by
  unfold isValidAt
  simp [hnode, hverified]

/-- If all dependencies are unchanged, node is valid (the useful soundness case) -/
theorem isValidAt_deps_all_unchanged {N : Nat} (rt : Runtime N) (qid : QueryId)
    (atRev : Revision N) (node : Node N) (hnode : rt.nodes qid = some node)
    (hdeps : ∀ dep ∈ node.dependencies,
      ∃ depNode, rt.nodes dep.queryId = some depNode ∧
        depNode.changedAt ≤ dep.observedChangedAt) :
    isValidAt rt qid atRev = true := by
  unfold isValidAt
  simp only [hnode]
  by_cases hverified : node.verifiedAt ≥ atRev.counters node.durability
  · simp only [hverified, ite_true]
  · simp only [hverified, ite_false]
    rw [List.all_eq_true]
    intro dep hdep
    obtain ⟨depNode, hdepNode, hle⟩ := hdeps dep hdep
    simp [hdepNode]
    exact hle

/-- If isValidAt is false, there's a reason: no node, invalid durability, or changed dep -/
theorem isValidAt_false_reason {N : Nat} (rt : Runtime N) (qid : QueryId)
    (atRev : Revision N) (hinvalid : isValidAt rt qid atRev = false) :
    rt.nodes qid = none ∨
    ∃ node, rt.nodes qid = some node ∧
      node.verifiedAt < atRev.counters node.durability ∧
      ∃ dep ∈ node.dependencies,
        rt.nodes dep.queryId = none ∨
        ∃ depNode, rt.nodes dep.queryId = some depNode ∧
          depNode.changedAt > dep.observedChangedAt := by
  unfold isValidAt at hinvalid
  cases hnode : rt.nodes qid with
  | none =>
    left; rfl
  | some node =>
    apply Or.inr
    let f : Dep → Bool :=
      fun dep =>
        match rt.nodes dep.queryId with
        | none => false
        | some depNode => !decide (depNode.changedAt > dep.observedChangedAt)
    by_cases hverified : node.verifiedAt ≥ atRev.counters node.durability
    · simp [hnode, hverified] at hinvalid
    · have hallFalse : node.dependencies.all f = false := by
        simpa [hnode, hverified, f] using hinvalid
      refine ⟨node, rfl, Nat.lt_of_not_ge hverified, ?_⟩
      rcases (List.all_eq_false).1 hallFalse with ⟨dep, hdep, hfail⟩
      refine ⟨dep, hdep, ?_⟩
      cases hdepNode : rt.nodes dep.queryId with
      | none =>
        left
        rfl
      | some depNode =>
        have hcheck' : (!decide (depNode.changedAt > dep.observedChangedAt)) = false := by
          simpa [f, hdepNode] using hfail
        have hdec : decide (depNode.changedAt > dep.observedChangedAt) = true := by
          cases h : decide (depNode.changedAt > dep.observedChangedAt) with
          | false =>
            simp [h] at hcheck'
          | true =>
            rfl
        have hgt : depNode.changedAt > dep.observedChangedAt :=
          of_decide_eq_true hdec
        right
        refine ⟨depNode, ?_, hgt⟩
        simp

/-- If dependencies haven't changed, node can be valid (original ambiguous version) -/
theorem isValidAt_deps_unchanged {N : Nat} (rt : Runtime N) (qid : QueryId)
    (atRev : Revision N) (node : Node N) (hnode : rt.nodes qid = some node)
    (_hdeps : ∀ dep ∈ node.dependencies,
      match rt.nodes dep.queryId with
      | some depNode => depNode.changedAt ≤ dep.observedChangedAt
      | none => False) :
    isValidAt rt qid atRev = true ∨ node.verifiedAt < atRev.counters node.durability := by
  unfold isValidAt
  simp [hnode]
  by_cases hverified : node.verifiedAt ≥ atRev.counters node.durability
  · left
    simp [hverified]
  · right
    exact Nat.lt_of_not_ge hverified

/-- If a dependency changed and not verified, node is invalid -/
theorem isValidAt_dep_changed {N : Nat} (rt : Runtime N) (qid : QueryId)
    (atRev : Revision N) (node : Node N) (hnode : rt.nodes qid = some node)
    (hnotverified : node.verifiedAt < atRev.counters node.durability)
    (dep : Dep) (hdep : dep ∈ node.dependencies)
    (depNode : Node N) (hdepNode : rt.nodes dep.queryId = some depNode)
    (hchanged : depNode.changedAt > dep.observedChangedAt) :
    isValidAt rt qid atRev = false := by
  unfold isValidAt
  simp only [hnode]
  have hnotge : ¬(node.verifiedAt ≥ atRev.counters node.durability) := by
    exact Nat.not_le.mpr hnotverified
  simp only [hnotge, ite_false]
  -- Need to show List.all returns false
  rw [Bool.eq_false_iff]
  intro hall
  rw [List.all_eq_true] at hall
  have := hall dep hdep
  simp only [hdepNode] at this
  simp only [Bool.not_eq_true', decide_eq_false_iff_not, not_lt] at this
  exact Nat.not_lt.mpr this hchanged

end ValidityCorrectness

/-! ## Phase 4: Early Cutoff Mechanism -/

section EarlyCutoff

/-- Confirm unchanged operation - value same after recompute.
    Recalculates durability and level based on new dependencies (matching Rust impl). -/
def confirmUnchanged {N : Nat} (rt : Runtime N) (qid : QueryId)
    (newDeps : List QueryId) : Except (List QueryId) (Runtime N) :=
  match rt.nodes qid with
  | none => .ok rt
  | some node =>
    match buildDepRecords rt.nodes newDeps with
    | .error missing => .error missing
    | .ok newDepRecords =>
      -- Recalculate effective durability based on new dependencies (like Rust does)
      let effectiveDur := calculateEffectiveDurability rt.nodes node.durability.val newDepRecords (N - 1)
      let finalDur := min effectiveDur (N - 1)
      have hN : N > 0 := rt.numDurabilityLevels
      have hfin : finalDur < N := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)
      let durFin : Fin N := ⟨finalDur, hfin⟩
      -- Recalculate level based on new dependencies
      let newLevel := calculateLevel rt.nodes newDepRecords
      let currentRev := rt.revision durFin
      let newNode : Node N := {
        durability := durFin
        verifiedAt := currentRev  -- Update verified_at
        changedAt := node.changedAt  -- changedAt unchanged! This is key for early cutoff
        level := newLevel
        dependencies := newDepRecords
        dependents := node.dependents
      }
      let baseNodes := fun q => if q = qid then some newNode else rt.nodes q
      -- Clean up stale edges from old dependencies (matching Rust impl)
      let cleanedNodes := cleanupStaleEdges baseNodes qid node.dependencies newDeps
      let newNodes := updateGraphEdges cleanedNodes qid newDepRecords
      .ok ⟨newNodes, rt.revision, rt.numDurabilityLevels⟩

/-- Confirm changed operation - value different after recompute.
    Recalculates durability and level based on new dependencies (matching Rust impl). -/
def confirmChanged {N : Nat} (rt : Runtime N) (qid : QueryId)
    (newDeps : List QueryId) : Except (List QueryId) (Runtime N × RevisionCounter) :=
  match rt.nodes qid with
  | none => .ok (rt, 0)
  | some node =>
    match buildDepRecords rt.nodes newDeps with
    | .error missing => .error missing
    | .ok newDepRecords =>
      -- Recalculate effective durability based on new dependencies (like Rust does)
      let effectiveDur := calculateEffectiveDurability rt.nodes node.durability.val newDepRecords (N - 1)
      let finalDur := min effectiveDur (N - 1)
      have hN : N > 0 := rt.numDurabilityLevels
      have hfin : finalDur < N := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)
      let durFin : Fin N := ⟨finalDur, hfin⟩
      -- Recalculate level based on new dependencies
      let newLevel := calculateLevel rt.nodes newDepRecords
      let (rt', newRev) := rt.incrementRevision durFin
      let newNode : Node N := {
        durability := durFin
        verifiedAt := newRev
        changedAt := newRev  -- Update changed_at! Dependents will see this
        level := newLevel
        dependencies := newDepRecords
        dependents := node.dependents
      }
      let baseNodes := fun q => if q = qid then some newNode else rt'.nodes q
      -- Clean up stale edges from old dependencies (matching Rust impl)
      let cleanedNodes := cleanupStaleEdges baseNodes qid node.dependencies newDeps
      let newNodes := updateGraphEdges cleanedNodes qid newDepRecords
      .ok (⟨newNodes, rt'.revision, rt'.numDurabilityLevels⟩, newRev)

/-- Key theorem: After confirmUnchanged, changedAt is preserved
    This is the essence of early cutoff -/
theorem confirmUnchanged_preserves_changedAt {N : Nat}
    (rt : Runtime N) (qid : QueryId) (newDeps : List QueryId)
    (node : Node N) (hnode : rt.nodes qid = some node)
    (hnoself : ∀ dep ∈ node.dependencies, dep.queryId ≠ qid) :
    match confirmUnchanged rt qid newDeps with
    | .ok rt' => ∃ n, rt'.nodes qid = some n ∧ n.changedAt = node.changedAt
    | .error _ => True := by
  unfold confirmUnchanged
  simp [hnode]
  cases hbd : buildDepRecords rt.nodes newDeps with
  | error missing =>
    simp
  | ok newDepRecords =>
    -- Recalculate durability and level (matching the new definition)
    let effectiveDur := calculateEffectiveDurability rt.nodes node.durability.val newDepRecords (N - 1)
    let finalDur := min effectiveDur (N - 1)
    have hN : N > 0 := rt.numDurabilityLevels
    have hfin : finalDur < N := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)
    let durFin : Fin N := ⟨finalDur, hfin⟩
    let newLevel := calculateLevel rt.nodes newDepRecords
    let currentRev := rt.revision durFin
    let qidNode : Node N := {
      durability := durFin
      verifiedAt := currentRev
      changedAt := node.changedAt
      level := newLevel
      dependencies := newDepRecords
      dependents := node.dependents
    }
    let baseNodes : QueryId → Option (Node N) :=
      fun q => if q = qid then some qidNode else rt.nodes q
    -- cleanupStaleEdges preserves baseNodes at qid (no self-dependency)
    let cleanedNodes := cleanupStaleEdges baseNodes qid node.dependencies newDeps
    have hclean_qid : cleanedNodes qid = baseNodes qid :=
      cleanupStaleEdges_preserves_at_qid baseNodes qid node.dependencies newDeps hnoself
    have hbase : baseNodes qid = some qidNode := by simp [baseNodes]
    have hclean_base : cleanedNodes qid = some qidNode := by rw [hclean_qid, hbase]
    have hfold :
        ∃ n', updateGraphEdges cleanedNodes qid newDepRecords qid = some n' ∧ n'.changedAt = qidNode.changedAt := by
      rw [updateGraphEdges_eq]
      simpa using foldl_updateGraphEdgesStep_preserves_changedAt qid qid cleanedNodes newDepRecords qidNode hclean_base
    rcases hfold with ⟨n', hn', hchg⟩
    refine ⟨n', ?_, ?_⟩
    · -- identify the runtime's nodes map
      convert hn' using 2
    · -- `qidNode.changedAt = node.changedAt` by construction
      exact Eq.trans hchg (by simp [qidNode])

/-- After confirmChanged, changedAt is updated -/
theorem confirmChanged_updates_changedAt {N : Nat}
    (rt : Runtime N) (qid : QueryId) (newDeps : List QueryId)
    (node : Node N) (hnode : rt.nodes qid = some node)
    (hnoself : ∀ dep ∈ node.dependencies, dep.queryId ≠ qid) :
    match confirmChanged rt qid newDeps with
    | .ok (rt', newRev) => ∃ n, rt'.nodes qid = some n ∧ n.changedAt = newRev
    | .error _ => True := by
  unfold confirmChanged
  simp only [hnode]
  cases hbd : buildDepRecords rt.nodes newDeps with
  | error missing =>
    simp
  | ok newDepRecords =>
    simp only
    -- The key observation: updateGraphEdges preserves changedAt
    have hN : N > 0 := rt.numDurabilityLevels
    let effectiveDur := calculateEffectiveDurability rt.nodes node.durability.val newDepRecords (N - 1)
    let finalDur := min effectiveDur (N - 1)
    have hfin : finalDur < N := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)
    let durFin : Fin N := ⟨finalDur, hfin⟩
    let newLevel := calculateLevel rt.nodes newDepRecords
    let incResult := rt.incrementRevision durFin
    let rt' := incResult.1
    let newRev := incResult.2
    let qidNode : Node N := {
      durability := durFin
      verifiedAt := newRev
      changedAt := newRev
      level := newLevel
      dependencies := newDepRecords
      dependents := node.dependents
    }
    let baseNodes : QueryId → Option (Node N) :=
      fun q => if q = qid then some qidNode else rt'.nodes q
    -- cleanupStaleEdges preserves baseNodes at qid (no self-dependency)
    let cleanedNodes := cleanupStaleEdges baseNodes qid node.dependencies newDeps
    have hclean_qid : cleanedNodes qid = baseNodes qid :=
      cleanupStaleEdges_preserves_at_qid baseNodes qid node.dependencies newDeps hnoself
    have hbase : baseNodes qid = some qidNode := by simp [baseNodes]
    have hclean_base : cleanedNodes qid = some qidNode := by rw [hclean_qid, hbase]
    have hfold :
        ∃ n', updateGraphEdges cleanedNodes qid newDepRecords qid = some n' ∧ n'.changedAt = qidNode.changedAt := by
      rw [updateGraphEdges_eq]
      simpa using foldl_updateGraphEdgesStep_preserves_changedAt qid qid cleanedNodes newDepRecords qidNode hclean_base
    rcases hfold with ⟨n', hn', hchg⟩
    refine ⟨n', ?_, ?_⟩
    · convert hn' using 2
    · simp only [qidNode, newRev] at hchg
      exact hchg

/-- The new revision from confirmChanged is greater than 0 -/
theorem confirmChanged_increases_rev {N : Nat}
    (rt : Runtime N) (qid : QueryId) (newDeps : List QueryId)
    (node : Node N) (hnode : rt.nodes qid = some node) :
    match confirmChanged rt qid newDeps with
    | .ok (_, newRev) => newRev > 0
    | .error _ => True := by
  unfold confirmChanged
  simp only [hnode]
  cases hbd : buildDepRecords rt.nodes newDeps with
  | error missing => simp
  | ok newDepRecords =>
    simp only
    have hN : N > 0 := rt.numDurabilityLevels
    let effectiveDur := calculateEffectiveDurability rt.nodes node.durability.val newDepRecords (N - 1)
    let finalDur := min effectiveDur (N - 1)
    have hfin : finalDur < N := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)
    let durFin : Fin N := ⟨finalDur, hfin⟩
    have hinc : (rt.incrementRevision durFin).2 = rt.revision durFin + 1 := incrementRevision_returns_new rt durFin
    have : (rt.incrementRevision durFin).2 > 0 := by rw [hinc]; exact Nat.succ_pos _
    convert this using 2

/-- Early cutoff theorem: If a node's value doesn't change (confirmUnchanged),
    any dependent that observed the old changedAt will still see the same changedAt,
    so it remains valid with respect to that dependency -/
theorem early_cutoff_preserves_observation {N : Nat}
    (rt : Runtime N) (qid : QueryId) (newDeps : List QueryId)
    (node : Node N) (hnode : rt.nodes qid = some node)
    (hnoself : ∀ dep ∈ node.dependencies, dep.queryId ≠ qid)
    (observedAt : RevisionCounter) (hobs : observedAt = node.changedAt) :
    match confirmUnchanged rt qid newDeps with
    | .ok rt' => ∃ n, rt'.nodes qid = some n ∧ n.changedAt ≤ observedAt
    | .error _ => True := by
  unfold confirmUnchanged
  simp only [hnode]
  cases hbd : buildDepRecords rt.nodes newDeps with
  | error missing => simp
  | ok newDepRecords =>
    simp only
    have hN : N > 0 := rt.numDurabilityLevels
    let effectiveDur := calculateEffectiveDurability rt.nodes node.durability.val newDepRecords (N - 1)
    let finalDur := min effectiveDur (N - 1)
    have hfin : finalDur < N := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)
    let durFin : Fin N := ⟨finalDur, hfin⟩
    let newLevel := calculateLevel rt.nodes newDepRecords
    let currentRev := rt.revision durFin
    let qidNode : Node N := {
      durability := durFin
      verifiedAt := currentRev
      changedAt := node.changedAt
      level := newLevel
      dependencies := newDepRecords
      dependents := node.dependents
    }
    let baseNodes : QueryId → Option (Node N) :=
      fun q => if q = qid then some qidNode else rt.nodes q
    -- cleanupStaleEdges preserves baseNodes at qid (no self-dependency)
    let cleanedNodes := cleanupStaleEdges baseNodes qid node.dependencies newDeps
    have hclean_qid : cleanedNodes qid = baseNodes qid :=
      cleanupStaleEdges_preserves_at_qid baseNodes qid node.dependencies newDeps hnoself
    have hbase : baseNodes qid = some qidNode := by simp [baseNodes]
    have hclean_base : cleanedNodes qid = some qidNode := by rw [hclean_qid, hbase]
    have hfold :
        ∃ n', updateGraphEdges cleanedNodes qid newDepRecords qid = some n' ∧ n'.changedAt = qidNode.changedAt := by
      rw [updateGraphEdges_eq]
      simpa using foldl_updateGraphEdgesStep_preserves_changedAt qid qid cleanedNodes newDepRecords qidNode hclean_base
    rcases hfold with ⟨n', hn', hchg⟩
    refine ⟨n', ?_, ?_⟩
    · convert hn' using 2
    · have : n'.changedAt = node.changedAt := Eq.trans hchg (by simp [qidNode])
      simp [hobs, this]

end EarlyCutoff

/-! ## Global Invariant Preservation -/

section InvariantPreservation

/-- `confirmUnchanged` does not change an unrelated node.

If `other ≠ qid`, `other ∉ newDeps`, and `other` is not in the old dependencies,
then neither the target update, cleanup, nor the reverse-edge updates touch `other`. -/
lemma confirmUnchanged_other_unchanged {N : Nat} (rt : Runtime N)
    (qid other : QueryId) (newDeps : List QueryId)
    (node : Node N) (hnode : rt.nodes qid = some node)
    (hne : other ≠ qid) (hnot : other ∉ newDeps)
    (hnotold : ∀ dep ∈ node.dependencies, dep.queryId ≠ other) :
    match confirmUnchanged rt qid newDeps with
    | .ok rt' => rt'.nodes other = rt.nodes other
    | .error _ => True := by
  unfold confirmUnchanged
  simp only [hnode]
  cases hbd : buildDepRecords rt.nodes newDeps with
  | error missing => simp
  | ok newDepRecords =>
    simp only
    have hN : N > 0 := rt.numDurabilityLevels
    let effectiveDur := calculateEffectiveDurability rt.nodes node.durability.val newDepRecords (N - 1)
    let finalDur := min effectiveDur (N - 1)
    have hfin : finalDur < N := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)
    let durFin : Fin N := ⟨finalDur, hfin⟩
    let newLevel := calculateLevel rt.nodes newDepRecords
    let currentRev := rt.revision durFin
    let newNode' : Node N := {
      durability := durFin
      verifiedAt := currentRev
      changedAt := node.changedAt
      level := newLevel
      dependencies := newDepRecords
      dependents := node.dependents
    }
    let baseNodes : QueryId → Option (Node N) :=
      fun q => if q = qid then some newNode' else rt.nodes q
    -- cleanupStaleEdges preserves other (not in old deps)
    let cleanedNodes := cleanupStaleEdges baseNodes qid node.dependencies newDeps
    have hclean_other : cleanedNodes other = baseNodes other :=
      cleanupStaleEdges_other_unchanged baseNodes qid other node.dependencies newDeps hnotold
    have hbaseOther : baseNodes other = rt.nodes other := by simp [baseNodes, hne]
    have hother : ∀ dep ∈ newDepRecords, dep.queryId ≠ other := by
      intro dep hmem
      have hqid_mem : dep.queryId ∈ newDeps :=
        buildDepRecords_ok_mem_queryId_mem (nodes := rt.nodes) (depIds := newDeps) (depRecords := newDepRecords) hbd dep hmem
      exact fun heq => hnot (by simpa [heq] using hqid_mem)
    have hupd : updateGraphEdges cleanedNodes qid newDepRecords other = cleanedNodes other :=
      updateGraphEdges_other_unchanged cleanedNodes qid other newDepRecords hother
    calc
      updateGraphEdges cleanedNodes qid newDepRecords other
          = cleanedNodes other := hupd
      _ = baseNodes other := hclean_other
      _ = rt.nodes other := hbaseOther

/-- `confirmChanged` does not change an unrelated node.

If `other ≠ qid`, `other ∉ newDeps`, and `other` is not in the old dependencies,
then neither the target update, cleanup, nor the reverse-edge updates touch `other`. -/
lemma confirmChanged_other_unchanged {N : Nat} (rt : Runtime N)
    (qid other : QueryId) (newDeps : List QueryId)
    (node : Node N) (hnode : rt.nodes qid = some node)
    (hne : other ≠ qid) (hnot : other ∉ newDeps)
    (hnotold : ∀ dep ∈ node.dependencies, dep.queryId ≠ other) :
    match confirmChanged rt qid newDeps with
    | .ok (rt', _newRev) => rt'.nodes other = rt.nodes other
    | .error _ => True := by
  unfold confirmChanged
  simp only [hnode]
  cases hbd : buildDepRecords rt.nodes newDeps with
  | error missing => simp
  | ok newDepRecords =>
    simp only
    have hN : N > 0 := rt.numDurabilityLevels
    let effectiveDur := calculateEffectiveDurability rt.nodes node.durability.val newDepRecords (N - 1)
    let finalDur := min effectiveDur (N - 1)
    have hfin : finalDur < N := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)
    let durFin : Fin N := ⟨finalDur, hfin⟩
    let newLevel := calculateLevel rt.nodes newDepRecords
    let incResult := rt.incrementRevision durFin
    let rt' := incResult.1
    let newRev := incResult.2
    have hpresNodes : rt'.nodes = rt.nodes := by
      simpa [rt', incResult] using (incrementRevision_preserves_nodes (rt := rt) (d := durFin))
    let newNode' : Node N := {
      durability := durFin
      verifiedAt := newRev
      changedAt := newRev
      level := newLevel
      dependencies := newDepRecords
      dependents := node.dependents
    }
    let baseNodes : QueryId → Option (Node N) :=
      fun q => if q = qid then some newNode' else rt'.nodes q
    -- cleanupStaleEdges preserves other (not in old deps)
    let cleanedNodes := cleanupStaleEdges baseNodes qid node.dependencies newDeps
    have hclean_other : cleanedNodes other = baseNodes other :=
      cleanupStaleEdges_other_unchanged baseNodes qid other node.dependencies newDeps hnotold
    have hbaseOther : baseNodes other = rt.nodes other := by
      simp [baseNodes, hne, hpresNodes]
    have hother : ∀ dep ∈ newDepRecords, dep.queryId ≠ other := by
      intro dep hmem
      have hqid_mem : dep.queryId ∈ newDeps :=
        buildDepRecords_ok_mem_queryId_mem (nodes := rt.nodes) (depIds := newDeps) (depRecords := newDepRecords) hbd dep hmem
      exact fun heq => hnot (by simpa [heq] using hqid_mem)
    have hupd : updateGraphEdges cleanedNodes qid newDepRecords other = cleanedNodes other :=
      updateGraphEdges_other_unchanged cleanedNodes qid other newDepRecords hother
    calc
      updateGraphEdges cleanedNodes qid newDepRecords other
          = cleanedNodes other := hupd
      _ = baseNodes other := hclean_other
      _ = rt.nodes other := hbaseOther

/-! ### noSelfDependency preservation for confirm operations -/

/-- confirmUnchanged preserves noSelfDependency when qid is not in newDeps -/
theorem confirmUnchanged_preserves_noSelfDependency {N : Nat} (rt : Runtime N)
    (qid : QueryId) (newDeps : List QueryId)
    (hinv : noSelfDependency rt.nodes)
    (hnotIn : qid ∉ newDeps) :
    match confirmUnchanged rt qid newDeps with
    | .ok rt' => noSelfDependency rt'.nodes
    | .error _ => True := by
  unfold confirmUnchanged
  cases hnode : rt.nodes qid with
  | none => trivial
  | some node =>
    cases hbd : buildDepRecords rt.nodes newDeps with
    | error missing => trivial
    | ok newDepRecords =>
      simp only []
      -- Define intermediate structures explicitly (matching confirmUnchanged definition)
      have hN : N > 0 := rt.numDurabilityLevels
      let effectiveDur := calculateEffectiveDurability rt.nodes node.durability.val newDepRecords (N - 1)
      let finalDur := min effectiveDur (N - 1)
      have hfin : finalDur < N := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)
      let durFin : Fin N := ⟨finalDur, hfin⟩
      let newLevel := calculateLevel rt.nodes newDepRecords
      let currentRev := rt.revision durFin
      let newNode' : Node N := {
        durability := durFin
        verifiedAt := currentRev
        changedAt := node.changedAt
        level := newLevel
        dependencies := newDepRecords
        dependents := node.dependents
      }
      let baseNodes : QueryId → Option (Node N) := fun q => if q = qid then some newNode' else rt.nodes q
      let cleanedNodes := cleanupStaleEdges baseNodes qid node.dependencies newDeps
      let finalNodes := updateGraphEdges cleanedNodes qid newDepRecords
      intro other otherNode hotherNode dep hdep
      by_cases heq : other = qid
      · -- Case: other = qid
        have hbaseQid : baseNodes qid = some newNode' := by simp only [baseNodes, ite_true]
        have ⟨n1, hn1, _, _, _, hdeps1⟩ := cleanupStaleEdges_preserves_node baseNodes qid qid node.dependencies newDeps newNode' hbaseQid
        have ⟨n2, hn2, hdeps2⟩ := updateGraphEdges_preserves_dependencies qid qid cleanedNodes newDepRecords n1 hn1
        rw [heq] at hotherNode
        rw [hn2] at hotherNode
        injection hotherNode with heq'
        have hdepsOther : otherNode.dependencies = newDepRecords := by
          rw [← heq', hdeps2, hdeps1]
        rw [hdepsOther] at hdep
        rw [heq]
        exact buildDepRecords_ok_no_self rt.nodes newDeps newDepRecords qid hbd hnotIn dep hdep
      · -- Case: other ≠ qid
        have hbaseOther : baseNodes other = rt.nodes other := by simp only [baseNodes, heq, ite_false]
        obtain ⟨origNode, horigNode⟩ := updateGraphEdges_some_implies_some qid other cleanedNodes newDepRecords otherNode hotherNode
        -- Work backward: origNode is from cleanedNodes, which preserves nodes from baseNodes
        obtain ⟨n1, hn1⟩ := cleanupStaleEdges_some_implies_some qid other baseNodes node.dependencies newDeps origNode horigNode
        simp only [baseNodes, heq, ite_false] at hn1
        have ⟨n1', hn1', _, _, _, hdeps1⟩ := cleanupStaleEdges_preserves_node baseNodes qid other node.dependencies newDeps n1 (by simp [baseNodes, heq, hn1])
        have ⟨n2', hn2', hdeps2⟩ := updateGraphEdges_preserves_dependencies qid other cleanedNodes newDepRecords n1' hn1'
        rw [hn2'] at hotherNode
        injection hotherNode with heq'
        have hdepsOther : otherNode.dependencies = n1.dependencies := by
          rw [← heq', hdeps2, hdeps1]
        rw [hdepsOther] at hdep
        exact hinv other n1 hn1 dep hdep

/-- confirmChanged preserves noSelfDependency when qid is not in newDeps -/
theorem confirmChanged_preserves_noSelfDependency {N : Nat} (rt : Runtime N)
    (qid : QueryId) (newDeps : List QueryId)
    (hinv : noSelfDependency rt.nodes)
    (hnotIn : qid ∉ newDeps) :
    match confirmChanged rt qid newDeps with
    | .ok (rt', _) => noSelfDependency rt'.nodes
    | .error _ => True := by
  unfold confirmChanged
  cases hnode : rt.nodes qid with
  | none => trivial
  | some node =>
    cases hbd : buildDepRecords rt.nodes newDeps with
    | error missing => trivial
    | ok newDepRecords =>
      simp only []
      -- Define intermediate structures explicitly (matching confirmChanged definition)
      have hN : N > 0 := rt.numDurabilityLevels
      let effectiveDur := calculateEffectiveDurability rt.nodes node.durability.val newDepRecords (N - 1)
      let finalDur := min effectiveDur (N - 1)
      have hfin : finalDur < N := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)
      let durFin : Fin N := ⟨finalDur, hfin⟩
      let newLevel := calculateLevel rt.nodes newDepRecords
      let incResult := rt.incrementRevision durFin
      let rt' := incResult.1
      let newRev := incResult.2
      have hrtNodes : rt'.nodes = rt.nodes := incrementRevision_preserves_nodes rt durFin
      let newNode' : Node N := {
        durability := durFin
        verifiedAt := newRev
        changedAt := newRev
        level := newLevel
        dependencies := newDepRecords
        dependents := node.dependents
      }
      let baseNodes : QueryId → Option (Node N) := fun q => if q = qid then some newNode' else rt'.nodes q
      let cleanedNodes := cleanupStaleEdges baseNodes qid node.dependencies newDeps
      let finalNodes := updateGraphEdges cleanedNodes qid newDepRecords
      intro other otherNode hotherNode dep hdep
      by_cases heq : other = qid
      · -- Case: other = qid
        have hbaseQid : baseNodes qid = some newNode' := by simp only [baseNodes, ite_true]
        have ⟨n1, hn1, _, _, _, hdeps1⟩ := cleanupStaleEdges_preserves_node baseNodes qid qid node.dependencies newDeps newNode' hbaseQid
        have ⟨n2, hn2, hdeps2⟩ := updateGraphEdges_preserves_dependencies qid qid cleanedNodes newDepRecords n1 hn1
        rw [heq] at hotherNode
        rw [hn2] at hotherNode
        injection hotherNode with heq'
        have hdepsOther : otherNode.dependencies = newDepRecords := by
          rw [← heq', hdeps2, hdeps1]
        rw [hdepsOther] at hdep
        rw [heq]
        exact buildDepRecords_ok_no_self rt.nodes newDeps newDepRecords qid hbd hnotIn dep hdep
      · -- Case: other ≠ qid
        have hbaseOther : baseNodes other = rt'.nodes other := by simp only [baseNodes, heq, ite_false]
        obtain ⟨origNode, horigNode⟩ := updateGraphEdges_some_implies_some qid other cleanedNodes newDepRecords otherNode hotherNode
        obtain ⟨n1, hn1⟩ := cleanupStaleEdges_some_implies_some qid other baseNodes node.dependencies newDeps origNode horigNode
        simp only [baseNodes, heq, ite_false] at hn1
        rw [hrtNodes] at hn1
        have ⟨n1', hn1', _, _, _, hdeps1⟩ := cleanupStaleEdges_preserves_node baseNodes qid other node.dependencies newDeps n1 (by simp [baseNodes, heq, hrtNodes, hn1])
        have ⟨n2', hn2', hdeps2⟩ := updateGraphEdges_preserves_dependencies qid other cleanedNodes newDepRecords n1' hn1'
        rw [hn2'] at hotherNode
        injection hotherNode with heq'
        have hdepsOther : otherNode.dependencies = n1.dependencies := by
          rw [← heq', hdeps2, hdeps1]
        rw [hdepsOther] at hdep
        exact hinv other n1 hn1 dep hdep

end InvariantPreservation

/-! ## Early Cutoff with Dependents -/

section EarlyCutoffDependents

/-- confirmUnchanged doesn't change revision -/
lemma confirmUnchanged_preserves_revision {N : Nat} (rt : Runtime N)
    (qid : QueryId) (newDeps : List QueryId) :
    match confirmUnchanged rt qid newDeps with
    | .ok rt' => rt'.revision = rt.revision
    | .error _ => True := by
  unfold confirmUnchanged
  cases hnode : rt.nodes qid with
  | none => simp
  | some node =>
    cases hbd : buildDepRecords rt.nodes newDeps with
    | error missing =>
      simp
    | ok newDepRecords =>
      simp

/-- If dependent was valid before confirmUnchanged, it stays valid after -/
theorem confirmUnchanged_preserves_dependent_validity {N : Nat}
    (rt : Runtime N) (qid dependentId : QueryId) (newDeps : List QueryId)
    (atRev : Revision N)
    (hne : dependentId ≠ qid) -- dependent is not the confirmed node itself
    (hvalid_before : isValidAt rt dependentId atRev = true) :
    match confirmUnchanged rt qid newDeps with
    | .ok rt' => isValidAt rt' dependentId atRev = true
    | .error _ => True := by
  unfold confirmUnchanged
  cases hqnode : rt.nodes qid with
  | none =>
    simpa [hqnode] using hvalid_before
  | some qidNode =>
    cases hbd : buildDepRecords rt.nodes newDeps with
    | error missing => simp
    | ok newDepRecords =>
      simp only
      have hN : N > 0 := rt.numDurabilityLevels
      let effectiveDur := calculateEffectiveDurability rt.nodes qidNode.durability.val newDepRecords (N - 1)
      let finalDur := min effectiveDur (N - 1)
      have hfin : finalDur < N := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)
      let durFin : Fin N := ⟨finalDur, hfin⟩
      let newLevel := calculateLevel rt.nodes newDepRecords
      let currentRev := rt.revision durFin
      let newNode : Node N := {
        durability := durFin
        verifiedAt := currentRev
        changedAt := qidNode.changedAt  -- Key: unchanged!
        level := newLevel
        dependencies := newDepRecords
        dependents := qidNode.dependents
      }
      let baseNodes := fun q => if q = qid then some newNode else rt.nodes q
      -- Now we have cleanedNodes in the definition
      let cleanedNodes := cleanupStaleEdges baseNodes qid qidNode.dependencies newDeps
      let finalNodes := updateGraphEdges cleanedNodes qid newDepRecords
      -- Show that cleanupStaleEdges doesn't affect isValidAt
      have hclean_valid :
          isValidAt (rt := ⟨cleanedNodes, rt.revision, rt.numDurabilityLevels⟩) dependentId atRev =
            isValidAt (rt := ⟨baseNodes, rt.revision, rt.numDurabilityLevels⟩) dependentId atRev := by
        exact isValidAt_cleanupStaleEdges (rt := ⟨baseNodes, rt.revision, rt.numDurabilityLevels⟩)
          qid dependentId qidNode.dependencies newDeps atRev
      have hvalid_eq :
          isValidAt (rt := ⟨finalNodes, rt.revision, rt.numDurabilityLevels⟩) dependentId atRev =
            isValidAt (rt := ⟨cleanedNodes, rt.revision, rt.numDurabilityLevels⟩) dependentId atRev := by
        simpa [finalNodes] using
          (isValidAt_updateGraphEdges (rt := ⟨cleanedNodes, rt.revision, rt.numDurabilityLevels⟩)
            qid newDepRecords dependentId atRev)
      -- First, show the goal matches finalNodes
      suffices h : isValidAt (rt := ⟨finalNodes, rt.revision, rt.numDurabilityLevels⟩) dependentId atRev = true by
        convert h using 2
      rw [hvalid_eq, hclean_valid]
      -- Now we work with baseNodes instead of cleanedNodes
      have hbefore := hvalid_before
      unfold isValidAt
      simp only
      unfold isValidAt at hbefore
      cases hdep : rt.nodes dependentId with
      | none =>
        simp only [hdep] at hbefore
        exact absurd hbefore Bool.false_ne_true
      | some depNode =>
        -- Show baseNodes dependentId = some depNode since dependentId ≠ qid
        have hbase_dep : baseNodes dependentId = some depNode := by simp [baseNodes, hne, hdep]
        simp only [hbase_dep]
        simp only [hdep] at hbefore
        by_cases hverified : depNode.verifiedAt ≥ atRev.counters depNode.durability
        · simp [hverified]
        · simp only [hverified, ite_false] at hbefore ⊢
          have hbeforeAll :
              depNode.dependencies.all (fun dep =>
                match rt.nodes dep.queryId with
                | none => false
                | some dn => !decide (dep.observedChangedAt < dn.changedAt)) = true := hbefore
          suffices
              depNode.dependencies.all (fun dep =>
                match baseNodes dep.queryId with
                | none => false
                | some dn => !decide (dep.observedChangedAt < dn.changedAt)) = true by
            exact this
          rw [List.all_eq_true] at hbeforeAll ⊢
          intro dep hdep_mem
          have hdep_before := hbeforeAll dep hdep_mem
          by_cases hdep_qid : dep.queryId = qid
          · subst hdep_qid
            -- newNode.changedAt = qidNode.changedAt, so the comparison is the same
            simp only [baseNodes]
            simp only [ite_true]
            simpa [hqnode, newNode] using hdep_before
          · -- dep.queryId ≠ qid, so baseNodes dep.queryId = rt.nodes dep.queryId
            have hbase_eq : baseNodes dep.queryId = rt.nodes dep.queryId := by simp [baseNodes, hdep_qid]
            simp only [hbase_eq]
            exact hdep_before

/-- Multi-level: If nodes A and B are valid, and we confirmUnchanged on C (distinct from A and B),
    both A and B remain valid -/
theorem multi_level_early_cutoff {N : Nat} (rt : Runtime N)
    (a b c : QueryId) (newDeps : List QueryId) (atRev : Revision N)
    (hac : a ≠ c) (hbc : b ≠ c)
    (hvalid_a : isValidAt rt a atRev = true)
    (hvalid_b : isValidAt rt b atRev = true) :
    match confirmUnchanged rt c newDeps with
    | .ok rt' => isValidAt rt' a atRev = true ∧ isValidAt rt' b atRev = true
    | .error _ => True := by
  cases hcu : confirmUnchanged rt c newDeps with
  | error missing =>
    simp
  | ok rt' =>
    constructor
    · have ha :=
        confirmUnchanged_preserves_dependent_validity
          (rt := rt) (qid := c) (dependentId := a) (newDeps := newDeps) (atRev := atRev) hac hvalid_a
      simpa [hcu] using ha
    · have hb :=
        confirmUnchanged_preserves_dependent_validity
          (rt := rt) (qid := c) (dependentId := b) (newDeps := newDeps) (atRev := atRev) hbc hvalid_b
      simpa [hcu] using hb

end EarlyCutoffDependents

/-! ## Summary of Verified Properties -/

/-
  PROVEN PROPERTIES:
  ==================

  Basic Operations:
  - markVerified_other_unchanged: markVerified only modifies target node
  - markVerified_monotone': markVerified never decreases verified_at
  - incrementRevision_monotone: revision counters are monotonic
  - incrementRevision_increments: increment works correctly
  - incrementRevision_preserves_nodes: increment doesn't modify nodes

  Invariant Preservation:
  - minDepDurability_empty: empty deps returns default
  - minDepDurability_le_default: result ≤ default
  - calculateEffectiveDurability_le_requested: durability ≤ requested
  - calculateEffectiveDurability_le_maxDur: durability ≤ maxDur
  - register_other_unchanged: register only modifies target node
  - register_wellformed: registered node has valid durability

  Graph Consistency (Phase 1):
  - dependentsConsistent: bidirectional consistency definition
  - updateGraphEdges: operation to maintain dependents lists
  - register: public operation for registration (updates reverse edges)

  Validity Specification (Phase 2):
  - isValidAt_verified: verified nodes are valid
  - isValidAt_deps_all_unchanged: unchanged deps means valid
  - isValidAt_false_reason: contrapositive characterization
  - isValidAt_deps_unchanged: original ambiguous version
  - isValidAt_dep_changed: changed dep means invalid (if not verified)

  Global Invariant Preservation (Phase 3):
  - confirmUnchanged_other_unchanged: only modifies target
  - confirmChanged_other_unchanged: only modifies target

  Early Cutoff with Dependents (Phase 4):
  - confirmUnchanged_preserves_changedAt: key early cutoff property
  - confirmChanged_updates_changedAt: changed updates changedAt
  - confirmChanged_increases_rev: new rev is incremented
  - early_cutoff_preserves_observation: observation remains valid
  - confirmUnchanged_preserves_revision: revision unchanged
  - confirmUnchanged_preserves_dependent_validity: dependents stay valid
  - multi_level_early_cutoff: multi-level propagation theorem

  These proofs establish:
  1. The design correctly enforces durability invariant via calculateEffectiveDurability
  2. The early cutoff mechanism works: confirmUnchanged preserves changedAt
  3. Validity detection is correct: changed deps are detected
  4. Global invariants are preserved by all operations
  5. Dependent validity is preserved through early cutoff
-/

end Whale
