/-
  Atomic Operations for Whale
  ===========================

  This file defines and proves correctness of atomic compare-and-update
  operations that combine the semantics of `confirmUnchanged` and `confirmChanged`
  into single atomic operations.

  These operations correspond to the Rust functions:
  - `update_with_compare`: Atomic compare-and-update with early cutoff
  - `get_or_insert`: Atomic insert-if-absent

  The key insight is that these operations provide the same guarantees as
  the sequential `confirmUnchanged`/`confirmChanged`/`register` but in a
  single atomic step, eliminating race conditions.
-/

import WhaleSpec.Basic

set_option linter.style.longLine false

namespace Whale

/-! ## Update With Compare -/

/-- Result of an update_with_compare operation -/
structure UpdateCompareResult (N : Nat) where
  changed : Bool
  revision : RevisionCounter
  effectiveDurability : Durability

/-- Atomic compare-and-update operation.

    This combines the semantics of `confirmUnchanged` and `confirmChanged` into
    a single atomic operation. The compare function is evaluated inside the
    atomic section to determine whether the value has changed.

    Semantics:
    - If node doesn't exist: create new node (like `register`)
    - If node exists and compare returns true (changed):
      - Increment revision
      - Set changedAt = verifiedAt = newRev
    - If node exists and compare returns false (unchanged):
      - Preserve changedAt (early cutoff)
      - Set verifiedAt = currentRev (mark as verified)

    This matches the Rust implementation in `whale/src/runtime.rs`.
-/
def updateWithCompare {N : Nat} (rt : Runtime N) (qid : QueryId)
    (compare : Option (Node N) → Bool)
    (requestedDurability : Durability) (depIds : List QueryId)
    : Except (List QueryId) (Runtime N × UpdateCompareResult N) :=
  match buildDepRecords rt.nodes depIds with
  | .error missing => .error missing
  | .ok depRecords =>
    let effectiveDur := calculateEffectiveDurability rt.nodes requestedDurability depRecords (N - 1)
    let finalDur := min effectiveDur (N - 1)
    have hN : N > 0 := rt.numDurabilityLevels
    have hfin : finalDur < N := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)
    let durFin : Fin N := ⟨finalDur, hfin⟩
    let newLevel := calculateLevel rt.nodes depRecords
    let existingNode := rt.nodes qid
    let changed := compare existingNode
    -- Compute new timestamps based on whether value changed
    let (rt', newChangedAt, newVerifiedAt) :=
      if changed then
        let (rtInc, newRev) := rt.incrementRevision durFin
        (rtInc, newRev, newRev)
      else
        let currentRev := rt.revision durFin
        let oldChangedAt := existingNode.map (·.changedAt) |>.getD currentRev
        (rt, oldChangedAt, currentRev)
    -- Preserve existing dependents
    let oldDependents : List QueryId :=
      match rt'.nodes qid with
      | none => []
      | some oldNode => oldNode.dependents
    let newNode : Node N := {
      durability := durFin
      verifiedAt := newVerifiedAt
      changedAt := newChangedAt
      level := newLevel
      dependencies := depRecords
      dependents := oldDependents
    }
    let baseNodes := fun q => if q = qid then some newNode else rt'.nodes q
    -- Clean up stale edges from old dependencies
    let oldDeps := existingNode.map (·.dependencies) |>.getD []
    let cleanedNodes := cleanupStaleEdges baseNodes qid oldDeps depIds
    let newNodes := updateGraphEdges cleanedNodes qid depRecords
    .ok (⟨newNodes, rt'.revision, rt'.numDurabilityLevels⟩,
         ⟨changed, newChangedAt, finalDur⟩)

/-! ## Get Or Insert -/

/-- Result of a get_or_insert operation -/
inductive GetOrInsertResult (N : Nat)
  | inserted (node : Node N)
  | existing (node : Node N)

/-- Atomic get-or-insert operation.

    This atomically checks if a node exists and either:
    - Returns the existing node (no modification)
    - Inserts a new node with register semantics

    The key property is that revision is only incremented when actually
    inserting, not when returning an existing node. This prevents
    "wasted" revisions under contention.

    Semantics:
    - If node exists: return existing (GetOrInsertResult.existing)
    - If node doesn't exist: insert new node with changedAt = verifiedAt = newRev
      (GetOrInsertResult.inserted)

    This matches the Rust implementation in `whale/src/runtime.rs`.
-/
def getOrInsert {N : Nat} (rt : Runtime N) (qid : QueryId)
    (requestedDurability : Durability) (depIds : List QueryId)
    : Except (List QueryId) (Runtime N × GetOrInsertResult N) :=
  -- Check if node already exists
  match rt.nodes qid with
  | some existingNode =>
    -- Return existing without any modification or revision increment
    .ok (rt, .existing existingNode)
  | none =>
    -- Node doesn't exist, proceed with insert (like register)
    match buildDepRecords rt.nodes depIds with
    | .error missing => .error missing
    | .ok depRecords =>
      let effectiveDur := calculateEffectiveDurability rt.nodes requestedDurability depRecords (N - 1)
      let finalDur := min effectiveDur (N - 1)
      have hN : N > 0 := rt.numDurabilityLevels
      have hfin : finalDur < N := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)
      let durFin : Fin N := ⟨finalDur, hfin⟩
      let newLevel := calculateLevel rt.nodes depRecords
      -- Only increment revision when actually inserting
      let (rt', newRev) := rt.incrementRevision durFin
      let newNode : Node N := {
        durability := durFin
        verifiedAt := newRev
        changedAt := newRev
        level := newLevel
        dependencies := depRecords
        dependents := []
      }
      let baseNodes := fun q => if q = qid then some newNode else rt'.nodes q
      let newNodes := updateGraphEdges baseNodes qid depRecords
      .ok (⟨newNodes, rt'.revision, rt'.numDurabilityLevels⟩, .inserted newNode)

/-! ## Helper Lemmas -/

/-- Helper: updateGraphEdgesStep preserves verifiedAt -/
lemma updateGraphEdgesStep_preserves_verifiedAt {N : Nat} (qid target : QueryId)
    (ns : QueryId → Option (Node N)) (d : Dep) (n : Node N)
    (hn : ns target = some n) :
    ∃ n', updateGraphEdgesStep qid ns d target = some n' ∧ n'.verifiedAt = n.verifiedAt := by
  unfold updateGraphEdgesStep
  cases hd : ns d.queryId with
  | none => exact ⟨n, hn, rfl⟩
  | some depNode =>
    by_cases hmem : qid ∈ depNode.dependents
    · -- qid already in dependents, no modification
      simp only [hmem, ite_true]
      exact ⟨n, hn, rfl⟩
    · -- qid not in dependents, add it
      simp only [hmem, ite_false]
      by_cases htarget : target = d.queryId
      · -- target is the node being modified
        subst htarget
        simp only [ite_true]
        have heq : some depNode = some n := by rw [← hd]; exact hn
        injection heq with heq'
        refine ⟨{ depNode with dependents := qid :: depNode.dependents }, rfl, ?_⟩
        simp only
        rw [← heq']
      · -- target is a different node
        simp only [htarget, ite_false]
        exact ⟨n, hn, rfl⟩

/-- Helper lemma: updateGraphEdges preserves verifiedAt -/
lemma foldl_updateGraphEdgesStep_preserves_verifiedAt {N : Nat} (qid target : QueryId)
    (ns : QueryId → Option (Node N)) (deps : List Dep) (n : Node N)
    (hn : ns target = some n) :
    ∃ n', deps.foldl (updateGraphEdgesStep qid) ns target = some n' ∧ n'.verifiedAt = n.verifiedAt := by
  apply List.foldl_preserves_some_prop (P := fun a b => b.verifiedAt = a.verifiedAt)
    target ns deps n hn
  · intro ns' d n' hn'
    exact updateGraphEdgesStep_preserves_verifiedAt qid target ns' d n' hn'
  · intro a b c hab hbc; exact hbc.trans hab
  · intro _; rfl

/-! ## Correctness Properties -/

section UpdateWithCompareProperties

/-- When compare returns false on existing node, changedAt is preserved -/
theorem updateWithCompare_unchanged_preserves_changedAt {N : Nat}
    (rt : Runtime N) (qid : QueryId)
    (compare : Option (Node N) → Bool)
    (requestedDurability : Durability) (depIds : List QueryId)
    (node : Node N) (hnode : rt.nodes qid = some node)
    (hcompare : compare (some node) = false)
    (hnoself : ∀ dep ∈ node.dependencies, dep.queryId ≠ qid) :
    match updateWithCompare rt qid compare requestedDurability depIds with
    | .ok (rt', result) => result.changed = false ∧
        ∃ n, rt'.nodes qid = some n ∧ n.changedAt = node.changedAt
    | .error _ => True := by
  unfold updateWithCompare
  cases hbd : buildDepRecords rt.nodes depIds with
  | error missing => trivial
  | ok depRecords =>
    simp only [hnode, hcompare, Bool.false_eq_true, ↓reduceIte]
    constructor
    · trivial
    -- The key: when compare returns false, we preserve changedAt
    let effectiveDur := calculateEffectiveDurability rt.nodes requestedDurability depRecords (N - 1)
    let finalDur := min effectiveDur (N - 1)
    have hN : N > 0 := rt.numDurabilityLevels
    have hfin : finalDur < N := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)
    let durFin : Fin N := ⟨finalDur, hfin⟩
    let newLevel := calculateLevel rt.nodes depRecords
    let currentRev := rt.revision durFin
    -- The new node with preserved changedAt
    let newNode : Node N := {
      durability := durFin
      verifiedAt := currentRev
      changedAt := node.changedAt
      level := newLevel
      dependencies := depRecords
      dependents := node.dependents
    }
    let baseNodes : QueryId → Option (Node N) :=
      fun q => if q = qid then some newNode else rt.nodes q
    have hbase : baseNodes qid = some newNode := by simp [baseNodes]
    let cleanedNodes := cleanupStaleEdges baseNodes qid node.dependencies depIds
    have hclean : cleanedNodes qid = baseNodes qid :=
      cleanupStaleEdges_preserves_at_qid baseNodes qid node.dependencies depIds hnoself
    have hclean_base : cleanedNodes qid = some newNode := by rw [hclean, hbase]
    -- Use the lemma from Basic.lean
    have hfinal := foldl_updateGraphEdgesStep_preserves_changedAt qid qid cleanedNodes depRecords newNode hclean_base
    rw [updateGraphEdges_eq]
    obtain ⟨n', hn', hchg⟩ := hfinal
    exact ⟨n', hn', hchg⟩

/-- When compare returns true, changedAt equals the new revision -/
theorem updateWithCompare_changed_updates_changedAt {N : Nat}
    (rt : Runtime N) (qid : QueryId)
    (compare : Option (Node N) → Bool)
    (requestedDurability : Durability) (depIds : List QueryId)
    (hcompare : compare (rt.nodes qid) = true)
    (hnoself : match rt.nodes qid with
               | some node => ∀ dep ∈ node.dependencies, dep.queryId ≠ qid
               | none => True) :
    match updateWithCompare rt qid compare requestedDurability depIds with
    | .ok (rt', result) => result.changed = true ∧
        ∃ n, rt'.nodes qid = some n ∧ n.changedAt = result.revision
    | .error _ => True := by
  unfold updateWithCompare
  cases hbd : buildDepRecords rt.nodes depIds with
  | error missing => trivial
  | ok depRecords =>
    simp only [hcompare, ↓reduceIte]
    constructor
    · trivial
    let effectiveDur := calculateEffectiveDurability rt.nodes requestedDurability depRecords (N - 1)
    let finalDur := min effectiveDur (N - 1)
    have hN : N > 0 := rt.numDurabilityLevels
    have hfin : finalDur < N := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)
    let durFin : Fin N := ⟨finalDur, hfin⟩
    let incResult := rt.incrementRevision durFin
    let rtInc := incResult.1
    let newRev := incResult.2
    let newLevel := calculateLevel rt.nodes depRecords
    -- incrementRevision preserves nodes
    have hrtIncNodes : rtInc.nodes = rt.nodes := incrementRevision_preserves_nodes rt durFin
    -- Get old dependents
    let oldDependents : List QueryId :=
      match rtInc.nodes qid with
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
    let baseNodes : QueryId → Option (Node N) :=
      fun q => if q = qid then some newNode else rtInc.nodes q
    have hbase : baseNodes qid = some newNode := by simp [baseNodes]
    -- Handle the case analysis on rt.nodes qid
    cases hnode : rt.nodes qid with
    | none =>
      -- No old dependencies to clean
      have hclean : cleanupStaleEdges baseNodes qid [] depIds qid = baseNodes qid := by
        simp only [cleanupStaleEdges, List.foldl_nil]
      have hclean_base : cleanupStaleEdges baseNodes qid [] depIds qid = some newNode := by rw [hclean, hbase]
      have hfinal := foldl_updateGraphEdgesStep_preserves_changedAt qid qid
        (cleanupStaleEdges baseNodes qid [] depIds) depRecords newNode hclean_base
      rw [updateGraphEdges_eq]
      obtain ⟨n', hn', hchg⟩ := hfinal
      exact ⟨n', hn', hchg⟩
    | some node =>
      have hnoself' : ∀ dep ∈ node.dependencies, dep.queryId ≠ qid := by
        simp only [hnode] at hnoself
        exact hnoself
      have hclean : cleanupStaleEdges baseNodes qid node.dependencies depIds qid = baseNodes qid :=
        cleanupStaleEdges_preserves_at_qid baseNodes qid node.dependencies depIds hnoself'
      have hclean_base : cleanupStaleEdges baseNodes qid node.dependencies depIds qid = some newNode := by
        rw [hclean, hbase]
      have hfinal := foldl_updateGraphEdgesStep_preserves_changedAt qid qid
        (cleanupStaleEdges baseNodes qid node.dependencies depIds) depRecords newNode hclean_base
      rw [updateGraphEdges_eq]
      obtain ⟨n', hn', hchg⟩ := hfinal
      exact ⟨n', hn', hchg⟩

end UpdateWithCompareProperties

section GetOrInsertProperties

/-- get_or_insert returns existing node without modification -/
theorem getOrInsert_existing_unchanged {N : Nat}
    (rt : Runtime N) (qid : QueryId)
    (durability : Durability) (depIds : List QueryId)
    (node : Node N) (hnode : rt.nodes qid = some node) :
    getOrInsert rt qid durability depIds = .ok (rt, .existing node) := by
  unfold getOrInsert
  simp [hnode]

/-- get_or_insert doesn't modify runtime when node exists -/
theorem getOrInsert_existing_preserves_runtime {N : Nat}
    (rt : Runtime N) (qid : QueryId)
    (durability : Durability) (depIds : List QueryId)
    (node : Node N) (hnode : rt.nodes qid = some node) :
    match getOrInsert rt qid durability depIds with
    | .ok (rt', _) => rt' = rt
    | .error _ => True := by
  rw [getOrInsert_existing_unchanged rt qid durability depIds node hnode]

/-- get_or_insert doesn't increment revision when node exists -/
theorem getOrInsert_existing_preserves_revision {N : Nat}
    (rt : Runtime N) (qid : QueryId)
    (durability : Durability) (depIds : List QueryId)
    (node : Node N) (hnode : rt.nodes qid = some node) :
    match getOrInsert rt qid durability depIds with
    | .ok (rt', _) => rt'.revision = rt.revision
    | .error _ => True := by
  rw [getOrInsert_existing_unchanged rt qid durability depIds node hnode]

/-- get_or_insert on missing node creates node with changedAt = verifiedAt -/
theorem getOrInsert_inserted_changedAt_eq_verifiedAt {N : Nat}
    (rt : Runtime N) (qid : QueryId)
    (durability : Durability) (depIds : List QueryId)
    (hmissing : rt.nodes qid = none) :
    match getOrInsert rt qid durability depIds with
    | .ok (rt', .inserted node) =>
      ∃ n, rt'.nodes qid = some n ∧ n.changedAt = n.verifiedAt
    | .ok (_, .existing _) => False
    | .error _ => True := by
  unfold getOrInsert
  simp only [hmissing]
  cases hbd : buildDepRecords rt.nodes depIds with
  | error missing => trivial
  | ok depRecords =>
    simp only
    let effectiveDur := calculateEffectiveDurability rt.nodes durability depRecords (N - 1)
    let finalDur := min effectiveDur (N - 1)
    have hN : N > 0 := rt.numDurabilityLevels
    have hfin : finalDur < N := Nat.lt_of_le_of_lt (Nat.min_le_right _ _) (Nat.sub_lt hN Nat.one_pos)
    let durFin : Fin N := ⟨finalDur, hfin⟩
    let (rt', newRev) := rt.incrementRevision durFin
    let newLevel := calculateLevel rt.nodes depRecords
    let newNode : Node N := {
      durability := durFin
      verifiedAt := newRev
      changedAt := newRev
      level := newLevel
      dependencies := depRecords
      dependents := []
    }
    let baseNodes : QueryId → Option (Node N) :=
      fun q => if q = qid then some newNode else rt'.nodes q
    have hbase : baseNodes qid = some newNode := by simp [baseNodes]
    -- updateGraphEdges preserves changedAt and verifiedAt
    have hchg := foldl_updateGraphEdgesStep_preserves_changedAt qid qid baseNodes depRecords newNode hbase
    have hver := foldl_updateGraphEdgesStep_preserves_verifiedAt qid qid baseNodes depRecords newNode hbase
    rw [updateGraphEdges_eq]
    obtain ⟨n1, hn1, hchg1⟩ := hchg
    obtain ⟨n2, hn2, hver2⟩ := hver
    -- n1 and n2 are the same node
    have heq : n1 = n2 := by
      have h1 : depRecords.foldl (updateGraphEdgesStep qid) baseNodes qid = some n1 := hn1
      have h2 : depRecords.foldl (updateGraphEdgesStep qid) baseNodes qid = some n2 := hn2
      rw [h1] at h2
      injection h2
    refine ⟨n1, hn1, ?_⟩
    rw [hchg1, ← heq, hver2]
    -- newNode.changedAt = newNode.verifiedAt = newRev by construction
    rfl

end GetOrInsertProperties

/-! ## Equivalence with Sequential Operations -/

section Equivalence

/-- updateWithCompare with compare=false is equivalent to confirmUnchanged for changedAt -/
theorem updateWithCompare_false_equiv_confirmUnchanged_changedAt {N : Nat}
    (rt : Runtime N) (qid : QueryId)
    (durability : Durability) (depIds : List QueryId)
    (node : Node N) (hnode : rt.nodes qid = some node)
    (hnoself : ∀ dep ∈ node.dependencies, dep.queryId ≠ qid) :
    match updateWithCompare rt qid (fun _ => false) durability depIds with
    | .ok (rt1, result1) =>
      match confirmUnchanged rt qid depIds with
      | .ok rt2 =>
        ∃ n1 n2, rt1.nodes qid = some n1 ∧ rt2.nodes qid = some n2 ∧
                 n1.changedAt = n2.changedAt
      | .error _ => True
    | .error _ => True := by
  have h1 := updateWithCompare_unchanged_preserves_changedAt rt qid (fun _ => false)
               durability depIds node hnode rfl hnoself
  have h2 := confirmUnchanged_preserves_changedAt rt qid depIds node hnode hnoself
  cases huwc : updateWithCompare rt qid (fun _ => false) durability depIds with
  | error _ => trivial
  | ok p =>
    cases hcu : confirmUnchanged rt qid depIds with
    | error _ => trivial
    | ok rt2 =>
      simp only [huwc] at h1
      simp only [hcu] at h2
      obtain ⟨_, ⟨n1, hn1, hchg1⟩⟩ := h1
      obtain ⟨n2, hn2, hchg2⟩ := h2
      exact ⟨n1, n2, hn1, hn2, hchg1.trans hchg2.symm⟩

end Equivalence

/-! ## Summary of Correctness Guarantees -/

/-
  The atomic operations provide the following guarantees:

  1. **updateWithCompare**:
     - When compare returns false (unchanged): changedAt is preserved (early cutoff)
     - When compare returns true (changed): changedAt = verifiedAt = newRev
     - Equivalent to confirmUnchanged/confirmChanged but atomic

  2. **getOrInsert**:
     - When node exists: returns existing without any modification
     - When node missing: equivalent to register
     - Revision only incremented when actually inserting (no wasted revisions)

  These guarantee race-free operation when multiple threads access the same key:
  - Thread A and B both try to insert: exactly one succeeds, other gets existing
  - Thread A updates while B reads: B sees consistent old or new state
  - Early cutoff is preserved: if value unchanged, dependents not invalidated
-/

end Whale
