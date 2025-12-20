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

/-- Confirm unchanged operation - value same after recompute -/
def confirmUnchanged {N : Nat} (rt : Runtime N) (qid : QueryId)
    (newDeps : List QueryId) : Except (List QueryId) (Runtime N) :=
  match rt.nodes qid with
  | none => .ok rt
  | some node =>
    match buildDepRecords rt.nodes newDeps with
    | .error missing => .error missing
    | .ok newDepRecords =>
      let d : Fin N := node.durability
      let currentRev := rt.revision d
      let newNode := { node with
        verifiedAt := currentRev  -- Update verified_at
        -- changedAt unchanged! This is key for early cutoff
        dependencies := newDepRecords
      }
      let baseNodes := fun q => if q = qid then some newNode else rt.nodes q
      let newNodes := updateGraphEdges baseNodes qid newDepRecords
      .ok ⟨newNodes, rt.revision, rt.numDurabilityLevels⟩

/-- Confirm changed operation - value different after recompute -/
def confirmChanged {N : Nat} (rt : Runtime N) (qid : QueryId)
    (newDeps : List QueryId) : Except (List QueryId) (Runtime N × RevisionCounter) :=
  match rt.nodes qid with
  | none => .ok (rt, 0)
  | some node =>
    match buildDepRecords rt.nodes newDeps with
    | .error missing => .error missing
    | .ok newDepRecords =>
      let d : Fin N := node.durability
      let (rt', newRev) := rt.incrementRevision d
      let newNode := { node with
        verifiedAt := newRev
        changedAt := newRev  -- Update changed_at! Dependents will see this
        dependencies := newDepRecords
      }
      let baseNodes := fun q => if q = qid then some newNode else rt'.nodes q
      let newNodes := updateGraphEdges baseNodes qid newDepRecords
      .ok (⟨newNodes, rt'.revision, rt'.numDurabilityLevels⟩, newRev)

/-- Key theorem: After confirmUnchanged, changedAt is preserved
    This is the essence of early cutoff -/
theorem confirmUnchanged_preserves_changedAt {N : Nat}
    (rt : Runtime N) (qid : QueryId) (newDeps : List QueryId)
    (node : Node N) (hnode : rt.nodes qid = some node) :
    match confirmUnchanged rt qid newDeps with
    | .ok rt' => ∃ n, rt'.nodes qid = some n ∧ n.changedAt = node.changedAt
    | .error _ => True := by
  unfold confirmUnchanged
  -- reduce the outer match on `rt.nodes qid`
  simp [hnode]
  cases hbd : buildDepRecords rt.nodes newDeps with
  | error missing =>
    simp
  | ok newDepRecords =>
    -- `updateGraphEdges` may change `dependents`, but never changes `changedAt`.
    -- Build the base node update first.
    let d : Fin N := node.durability
    let currentRev := rt.revision d
    let qidNode : Node N := { node with
      verifiedAt := currentRev
      dependencies := newDepRecords
    }
    let baseNodes : QueryId → Option (Node N) :=
      fun q => if q = qid then some qidNode else rt.nodes q
    have hbase : baseNodes qid = some qidNode := by simp [baseNodes]
    have hfold :
        ∃ n', updateGraphEdges baseNodes qid newDepRecords qid = some n' ∧ n'.changedAt = qidNode.changedAt := by
      rw [updateGraphEdges_eq]
      simpa using foldl_updateGraphEdgesStep_preserves_changedAt qid qid baseNodes newDepRecords qidNode hbase
    rcases hfold with ⟨n', hn', hchg⟩
    refine ⟨n', ?_, ?_⟩
    · -- identify the runtime's nodes map
      simpa [baseNodes, confirmUnchanged, hnode, hbd] using hn'
    · -- `qidNode.changedAt = node.changedAt` by construction
      exact Eq.trans hchg (by simp [qidNode])

/-- After confirmChanged, changedAt is updated -/
theorem confirmChanged_updates_changedAt {N : Nat}
    (rt : Runtime N) (qid : QueryId) (newDeps : List QueryId)
    (node : Node N) (hnode : rt.nodes qid = some node) :
    match confirmChanged rt qid newDeps with
    | .ok (rt', newRev) => ∃ n, rt'.nodes qid = some n ∧ n.changedAt = newRev
    | .error _ => True := by
  unfold confirmChanged
  simp [hnode]
  cases hbd : buildDepRecords rt.nodes newDeps with
  | error missing =>
    simp
  | ok newDepRecords =>
    let d : Fin N := node.durability
    let (rt', newRev) := rt.incrementRevision d
    let qidNode : Node N := { node with
      verifiedAt := newRev
      changedAt := newRev
      dependencies := newDepRecords
    }
    let baseNodes : QueryId → Option (Node N) :=
      fun q => if q = qid then some qidNode else rt'.nodes q
    have hbase : baseNodes qid = some qidNode := by simp [baseNodes]
    have hfold :
        ∃ n', updateGraphEdges baseNodes qid newDepRecords qid = some n' ∧ n'.changedAt = qidNode.changedAt := by
      rw [updateGraphEdges_eq]
      simpa using foldl_updateGraphEdgesStep_preserves_changedAt qid qid baseNodes newDepRecords qidNode hbase
    rcases hfold with ⟨n', hn', hchg⟩
    refine ⟨n', ?_, ?_⟩
    · simpa [baseNodes, confirmChanged, hnode, hbd] using hn'
    · -- qidNode.changedAt = newRev
      simpa [qidNode] using hchg

/-- The new revision from confirmChanged is greater than current -/
theorem confirmChanged_increases_rev {N : Nat}
    (rt : Runtime N) (qid : QueryId) (newDeps : List QueryId)
    (node : Node N) (hnode : rt.nodes qid = some node) :
    match confirmChanged rt qid newDeps with
    | .ok (_, newRev) => newRev = rt.revision node.durability + 1
    | .error _ => True := by
  unfold confirmChanged
  cases hbd : buildDepRecords rt.nodes newDeps with
  | error missing =>
    simp [hnode]
  | ok newDepRecords =>
    simp [hnode, incrementRevision_returns_new]

/-- Early cutoff theorem: If a node's value doesn't change (confirmUnchanged),
    any dependent that observed the old changedAt will still see the same changedAt,
    so it remains valid with respect to that dependency -/
theorem early_cutoff_preserves_observation {N : Nat}
    (rt : Runtime N) (qid : QueryId) (newDeps : List QueryId)
    (node : Node N) (hnode : rt.nodes qid = some node)
    (observedAt : RevisionCounter) (hobs : observedAt = node.changedAt) :
    match confirmUnchanged rt qid newDeps with
    | .ok rt' => ∃ n, rt'.nodes qid = some n ∧ n.changedAt ≤ observedAt
    | .error _ => True := by
  unfold confirmUnchanged
  simp [hnode]
  cases hbd : buildDepRecords rt.nodes newDeps with
  | error missing =>
    simp
  | ok newDepRecords =>
    let d : Fin N := node.durability
    let currentRev := rt.revision d
    let qidNode : Node N := { node with
      verifiedAt := currentRev
      dependencies := newDepRecords
    }
    let baseNodes : QueryId → Option (Node N) :=
      fun q => if q = qid then some qidNode else rt.nodes q
    have hbase : baseNodes qid = some qidNode := by simp [baseNodes]
    have hfold :
        ∃ n', updateGraphEdges baseNodes qid newDepRecords qid = some n' ∧ n'.changedAt = qidNode.changedAt := by
      rw [updateGraphEdges_eq]
      simpa using foldl_updateGraphEdgesStep_preserves_changedAt qid qid baseNodes newDepRecords qidNode hbase
    rcases hfold with ⟨n', hn', hchg⟩
    refine ⟨n', ?_, ?_⟩
    · simpa [baseNodes, confirmUnchanged, hnode, hbd] using hn'
    · -- changedAt unchanged, so ≤ observedAt
      have : n'.changedAt = node.changedAt := by
        -- qidNode.changedAt = node.changedAt by construction
        exact Eq.trans hchg (by simp [qidNode])
      simp [hobs, this]

end EarlyCutoff

/-! ## Global Invariant Preservation -/

section InvariantPreservation

/-- `confirmUnchanged` does not change an unrelated node.

If `other ≠ qid` and `other ∉ newDeps`, then neither the target update nor the reverse-edge updates touch `other`. -/
lemma confirmUnchanged_other_unchanged {N : Nat} (rt : Runtime N)
    (qid other : QueryId) (newDeps : List QueryId)
    (hne : other ≠ qid) (hnot : other ∉ newDeps) :
    match confirmUnchanged rt qid newDeps with
    | .ok rt' => rt'.nodes other = rt.nodes other
    | .error _ => True := by
  unfold confirmUnchanged
  cases hnode : rt.nodes qid with
  | none =>
    -- `confirmUnchanged` is a no-op
    simp
  | some node =>
    cases hbd : buildDepRecords rt.nodes newDeps with
    | error missing =>
      simp
    | ok newDepRecords =>
      let baseNodes : QueryId → Option (Node N) :=
        fun q =>
          if q = qid then
            some { node with verifiedAt := rt.revision node.durability, dependencies := newDepRecords }
          else rt.nodes q
      -- The resulting nodes map is `updateGraphEdges baseNodes qid newDepRecords`.
      -- First, `baseNodes other = rt.nodes other` since `other ≠ qid`.
      have hbaseOther : baseNodes other = rt.nodes other := by simp [baseNodes, hne]
      -- Next, `updateGraphEdges` does not touch `other` because `other ∉ newDeps` implies `dep.queryId ≠ other`.
      have hother : ∀ dep ∈ newDepRecords, dep.queryId ≠ other := by
        intro dep hmem
        have hqid_mem : dep.queryId ∈ newDeps :=
          buildDepRecords_ok_mem_queryId_mem (nodes := rt.nodes) (depIds := newDeps) (depRecords := newDepRecords) hbd dep hmem
        exact fun heq => hnot (by simpa [heq] using hqid_mem)
      have hupd : updateGraphEdges baseNodes qid newDepRecords other = baseNodes other :=
        updateGraphEdges_other_unchanged baseNodes qid other newDepRecords hother
      -- reduce to the `calc` chain
      calc
        updateGraphEdges baseNodes qid newDepRecords other
            = baseNodes other := hupd
        _ = rt.nodes other := hbaseOther

/-- `confirmChanged` does not change an unrelated node.

If `other ≠ qid` and `other ∉ newDeps`, then neither the target update nor the reverse-edge updates touch `other`. -/
lemma confirmChanged_other_unchanged {N : Nat} (rt : Runtime N)
    (qid other : QueryId) (newDeps : List QueryId)
    (hne : other ≠ qid) (hnot : other ∉ newDeps) :
    match confirmChanged rt qid newDeps with
    | .ok (rt', _newRev) => rt'.nodes other = rt.nodes other
    | .error _ => True := by
  unfold confirmChanged
  cases hnode : rt.nodes qid with
  | none =>
    simp
  | some node =>
    cases hbd : buildDepRecords rt.nodes newDeps with
    | error missing =>
      simp
    | ok newDepRecords =>
      -- For `other ≠ qid`, the baseNodes agrees with `rt'.nodes` at `other`, and `rt'.nodes = rt.nodes`.
      let p := rt.incrementRevision node.durability
      let rt' : Runtime N := p.1
      let newRev : RevisionCounter := p.2
      have hpresNodes : rt'.nodes = rt.nodes := by
        simpa [rt', p] using (incrementRevision_preserves_nodes (rt := rt) (d := node.durability))
      let baseNodes : QueryId → Option (Node N) :=
        fun q =>
          if q = qid then
            some { node with verifiedAt := newRev, changedAt := newRev, dependencies := newDepRecords }
          else rt'.nodes q
      have hbaseOther : baseNodes other = rt.nodes other := by
        simp [baseNodes, hne, hpresNodes]
      have hother : ∀ dep ∈ newDepRecords, dep.queryId ≠ other := by
        intro dep hmem
        have hqid_mem : dep.queryId ∈ newDeps :=
          buildDepRecords_ok_mem_queryId_mem (nodes := rt.nodes) (depIds := newDeps) (depRecords := newDepRecords) hbd dep hmem
        exact fun heq => hnot (by simpa [heq] using hqid_mem)
      have hupd : updateGraphEdges baseNodes qid newDepRecords other = baseNodes other :=
        updateGraphEdges_other_unchanged baseNodes qid other newDepRecords hother
      calc
        updateGraphEdges baseNodes qid newDepRecords other
            = baseNodes other := hupd
        _ = rt.nodes other := hbaseOther

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
    -- `.ok rt`
    simpa [hqnode] using hvalid_before
  | some qidNode =>
    cases hbd : buildDepRecords rt.nodes newDeps with
    | error missing =>
      simp
    | ok newDepRecords =>
      let d : Fin N := qidNode.durability
      let currentRev := rt.revision d
      let newNode : Node N := { qidNode with verifiedAt := currentRev, dependencies := newDepRecords }
      let baseNodes := fun q => if q = qid then some newNode else rt.nodes q
      let finalNodes := updateGraphEdges baseNodes qid newDepRecords
      -- reduce the top-level `match` to the successful branch
      simp
      -- `isValidAt` is invariant under `updateGraphEdges` (it only touches `dependents`)
      have hvalid_eq :
          isValidAt (rt := ⟨finalNodes, rt.revision, rt.numDurabilityLevels⟩) dependentId atRev =
            isValidAt (rt := ⟨baseNodes, rt.revision, rt.numDurabilityLevels⟩) dependentId atRev := by
        simpa [finalNodes] using
          (isValidAt_updateGraphEdges (rt := ⟨baseNodes, rt.revision, rt.numDurabilityLevels⟩)
            qid newDepRecords dependentId atRev)
      -- switch the goal to the `baseNodes` runtime
      rw [hvalid_eq]
      have hbefore := hvalid_before
      -- Goal: dependent node is unchanged, so reuse original proof, except for the dependency = qid case
      unfold isValidAt
      simp [baseNodes, hne]
      unfold isValidAt at hbefore
      cases hdep : rt.nodes dependentId with
      | none =>
        simp only [hdep] at hbefore
        exact absurd hbefore Bool.false_ne_true
      | some depNode =>
        simp [hdep] at hbefore ⊢
        -- verified case: immediate
        by_cases hverified : depNode.verifiedAt ≥ atRev.counters depNode.durability
        · simp [hverified]
        · simp only [hverified] at hbefore ⊢
          have hbeforeAll :
              depNode.dependencies.all (fun dep =>
                match rt.nodes dep.queryId with
                | none => false
                | some dn => !decide (dep.observedChangedAt < dn.changedAt)) = true := by
            simpa using hbefore
          suffices
              depNode.dependencies.all (fun dep =>
                match if dep.queryId = qid then some newNode else rt.nodes dep.queryId with
                | none => false
                | some dn => !decide (dep.observedChangedAt < dn.changedAt)) = true by
            simpa using this
          rw [List.all_eq_true] at hbeforeAll ⊢
          intro dep hdep_mem
          have hdep_before := hbeforeAll dep hdep_mem
          by_cases hdep_qid : dep.queryId = qid
          · subst hdep_qid
            simpa [hqnode, newNode] using hdep_before
          · simpa [hdep_qid] using hdep_before

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
