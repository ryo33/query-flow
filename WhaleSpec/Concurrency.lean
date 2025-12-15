/-
  Whale V3 Concurrency Model
  ==========================

  This file formalizes concurrent properties of the Whale system.
  We use an interleaving semantics where operations are atomic steps
  that can be executed in any order.

  Key properties:
  1. Commutativity: Operations on different nodes commute
  2. Idempotency: Certain operations are idempotent
  3. Monotonicity: Revision counters only increase
-/

import WhaleSpec.Basic

namespace Whale.Concurrency

open Whale

/-! ## Level 1: Interleaving Model - Commutativity -/

section Commutativity

/-- Helper: two runtimes are equal if their nodes and revisions are equal -/
theorem runtime_ext {N : Nat} (rt1 rt2 : Runtime N)
    (hnodes : rt1.nodes = rt2.nodes)
    (hrev : rt1.revision = rt2.revision) :
    rt1 = rt2 := by
  ext <;> simp_all

/-- markVerified on different nodes commutes
    This is the key property for lock-free concurrent updates -/
theorem markVerified_commute {N : Nat} (rt : Runtime N)
    (qid1 qid2 : QueryId) (atRev : Revision N) (hne : qid1 ≠ qid2) :
    markVerified (markVerified rt qid1 atRev) qid2 atRev =
    markVerified (markVerified rt qid2 atRev) qid1 atRev := by
  apply runtime_ext
  · -- nodes equality: each side modifies different nodes
    funext q
    by_cases hq1 : q = qid1 <;> by_cases hq2 : q = qid2
    · -- q = qid1 = qid2: contradiction with hne
      subst hq1 hq2; exact absurd rfl hne
    · -- q = qid1, q ≠ qid2
      subst hq1
      have hne' : q ≠ qid2 := hq2
      -- LHS: outer markVerified is at qid2, we look at q ≠ qid2, so unchanged
      rw [markVerified_other_unchanged (markVerified rt q atRev) qid2 q atRev hne']
      -- RHS: outer markVerified is at q, need to use markVerified_result_eq
      -- The input runtime's node at q equals rt.nodes q (by markVerified_other_unchanged)
      have heq : (markVerified rt qid2 atRev).nodes q = rt.nodes q :=
        markVerified_other_unchanged rt qid2 q atRev hne'
      -- Use markVerified_result_eq to show both sides have same result at q
      exact (markVerified_result_eq (markVerified rt qid2 atRev) rt q atRev heq).symm
    · -- q ≠ qid1, q = qid2: symmetric to above
      subst hq2
      have hne' : q ≠ qid1 := hq1
      rw [markVerified_other_unchanged (markVerified rt q atRev) qid1 q atRev hne']
      have heq : (markVerified rt qid1 atRev).nodes q = rt.nodes q :=
        markVerified_other_unchanged rt qid1 q atRev hne'
      exact markVerified_result_eq (markVerified rt qid1 atRev) rt q atRev heq
    · -- q ≠ qid1, q ≠ qid2: both sides equal rt.nodes q
      simp only [markVerified_other_unchanged _ qid2 q atRev hq2,
                 markVerified_other_unchanged _ qid1 q atRev hq1]
  · -- revision equality: markVerified doesn't change revision
    simp only [markVerified_preserves_revision]

end Commutativity

/-! ## Non-interference: confirmUnchanged -/

section ConfirmNonInterference

/-- If `confirmUnchanged` succeeds, it does not change an unrelated node that is not in the new deps list. -/
theorem confirmUnchanged_preserves_other_node {N : Nat} (rt : Runtime N)
    (qid other : QueryId) (newDeps : List QueryId)
    (hne : other ≠ qid) (hnot : other ∉ newDeps) :
    match confirmUnchanged rt qid newDeps with
    | .ok rt' => rt'.nodes other = rt.nodes other
    | .error _ => True := by
  simpa using (Whale.confirmUnchanged_other_unchanged (rt := rt) (qid := qid) (other := other)
    (newDeps := newDeps) hne hnot)

end ConfirmNonInterference

/-! ## Level 1: Idempotency -/

section Idempotency

/-- markVerified is idempotent on the same node with same revision
    This ensures concurrent retry operations are safe -/
theorem markVerified_idempotent {N : Nat} (rt : Runtime N)
    (qid : QueryId) (atRev : Revision N) :
    markVerified (markVerified rt qid atRev) qid atRev =
    markVerified rt qid atRev := by
  apply runtime_ext
  · -- nodes equality
    funext q
    by_cases hq : q = qid
    · -- q = qid: need to show applying markVerified twice gives same result
      subst hq
      cases hnode : rt.nodes q with
      | none =>
        -- When no node, markVerified returns rt unchanged, so nodes q = none
        have h1 : (markVerified rt q atRev).nodes q = none := markVerified_none rt q atRev hnode
        rw [markVerified_none (markVerified rt q atRev) q atRev h1]
        exact h1.symm
      | some node =>
        -- With `durability : Fin N`, there is no "invalid durability" branch.
        have h1 :
            (markVerified rt q atRev).nodes q =
              some { node with verifiedAt := max node.verifiedAt (atRev.counters node.durability) } := by
          simpa using (markVerified_at_target rt q atRev node hnode)
        rw [markVerified_at_target (markVerified rt q atRev) q atRev
              ({ node with verifiedAt := max node.verifiedAt (atRev.counters node.durability) }) h1]
        rw [markVerified_at_target rt q atRev node hnode]
        -- max (max a b) b = max a b
        simp [Nat.max_assoc, Nat.max_self]
    · -- q ≠ qid
      rw [markVerified_other_unchanged _ qid q atRev hq]
  · -- revision
    simp only [markVerified_preserves_revision]

end Idempotency

/-! ## Level 2: Atomic Operations Abstraction -/

section AtomicOps

/-- Abstract fetch_max operation: returns (new_value, old_value)
    This models the atomic compare-and-swap used in the implementation -/
def fetchMax (current proposed : Nat) : Nat × Nat :=
  (max current proposed, current)

/-- fetch_max is idempotent in terms of final value -/
theorem fetchMax_value_idempotent (v1 v2 : Nat) :
    (fetchMax (fetchMax v1 v2).1 v2).1 = (fetchMax v1 v2).1 := by
  unfold fetchMax
  simp only [Nat.max_assoc, Nat.max_self]

/-- fetch_max is monotonic -/
theorem fetchMax_monotone (current proposed : Nat) :
    current ≤ (fetchMax current proposed).1 := by
  unfold fetchMax
  exact Nat.le_max_left _ _

/-- fetch_max preserves the maximum seen so far -/
theorem fetchMax_preserves_max (current proposed : Nat) :
    (fetchMax current proposed).1 = max current proposed := rfl

/-- fetch_max is commutative for multiple updates -/
theorem fetchMax_comm (a b c : Nat) :
    (fetchMax (fetchMax a b).1 c).1 = (fetchMax (fetchMax a c).1 b).1 := by
  unfold fetchMax
  simp only [Nat.max_comm, Nat.max_left_comm]

/-- Abstract fetch_add operation -/
def fetchAdd (current delta : Nat) : Nat × Nat :=
  (current + delta, current)

/-- fetch_add is strictly increasing (for delta > 0) -/
theorem fetchAdd_strictly_increasing (current : Nat) {delta : Nat} (hd : delta > 0) :
    current < (fetchAdd current delta).1 := by
  unfold fetchAdd
  omega

end AtomicOps

/-! ## Level 2: Snapshot Isolation -/

section SnapshotIsolation

/-- A snapshot captures the revision state at a point in time -/
structure Snapshot (N : Nat) where
  revision : Revision N

/-- A snapshot is valid if it was taken before or at current revision -/
def Snapshot.isValidAt {N : Nat} (snap : Snapshot N) (rt : Runtime N) : Prop :=
  ∀ d : Fin N, snap.revision.counters d ≤ rt.revision d

/-- Taking a snapshot gives a valid snapshot -/
def takeSnapshot {N : Nat} (rt : Runtime N) : Snapshot N :=
  ⟨rt.currentRevision⟩

/-- Freshly taken snapshot is valid -/
theorem takeSnapshot_valid {N : Nat} (rt : Runtime N) :
    (takeSnapshot rt).isValidAt rt := by
  unfold takeSnapshot Snapshot.isValidAt Runtime.currentRevision
  intro d
  rfl

/-- Snapshot validity is preserved when revision only increases -/
theorem snapshot_valid_monotone {N : Nat} (snap : Snapshot N)
    (rt1 rt2 : Runtime N)
    (hvalid : snap.isValidAt rt1)
    (hmono : ∀ d : Fin N, rt1.revision d ≤ rt2.revision d) :
    snap.isValidAt rt2 := by
  unfold Snapshot.isValidAt at *
  intro d
  exact Nat.le_trans (hvalid d) (hmono d)

/-- After incrementRevision, snapshot at old revision is stale -/
theorem snapshot_stale_after_increment {N : Nat} (rt : Runtime N)
    (d : Fin N) :
    (takeSnapshot rt).revision.counters d < (rt.incrementRevision d).1.revision d := by
  unfold takeSnapshot Runtime.currentRevision
  simp only
  rw [incrementRevision_increments]
  exact Nat.lt_succ_self _

end SnapshotIsolation

/-! ## Monotonicity Properties -/

section Monotonicity

/-- Revision counters never decrease after markVerified -/
theorem revision_monotone_markVerified {N : Nat} (rt : Runtime N)
    (qid : QueryId) (atRev : Revision N) (d : Fin N) :
    rt.revision d ≤ (markVerified rt qid atRev).revision d := by
  rw [markVerified_preserves_revision]

/-- incrementRevision makes progress -/
theorem incrementRevision_progress {N : Nat} (rt : Runtime N) (d : Fin N) :
    rt.revision d < (rt.incrementRevision d).1.revision d := by
  rw [incrementRevision_increments]
  exact Nat.lt_succ_self _

/-- No operation decreases any revision counter -/
theorem no_revision_decrease {N : Nat} (rt : Runtime N)
    (qid : QueryId) (atRev : Revision N) (d : Fin N) :
    rt.revision d ≤ (markVerified rt qid atRev).revision d ∧
    rt.revision d ≤ (rt.incrementRevision d).1.revision d := by
  constructor
  · exact revision_monotone_markVerified rt qid atRev d
  · exact Nat.le_of_lt (incrementRevision_progress rt d)

end Monotonicity

/-! ## Concurrent Safety Summary -/

/-
  PROVEN CONCURRENT PROPERTIES:
  =============================

  Commutativity (Level 1):
  - markVerified_commute: Operations on different nodes can be reordered
    → This means concurrent updates to different queries are safe

  Idempotency (Level 1):
  - markVerified_idempotent: Same operation twice = once
    → This means retry/duplicate operations are safe

  Atomic Operations (Level 2):
  - fetchMax_value_idempotent: fetch_max converges
  - fetchMax_monotone: Values only increase
  - fetchMax_comm: Order of updates doesn't matter for final value
  - fetchAdd_strictly_increasing: Guarantees unique revision numbers

  Snapshot Isolation (Level 2):
  - takeSnapshot_valid: Snapshots are initially valid
  - snapshot_valid_monotone: Old snapshots remain valid
  - snapshot_stale_after_increment: Detects when revalidation needed

  Monotonicity:
  - revision_monotone_markVerified: Revisions never decrease
  - incrementRevision_progress: Always makes progress
  - no_revision_decrease: Global monotonicity

  IMPLICATIONS FOR SPEC.MD:
  =========================

  1. Lock-free safety: Operations on different nodes commute,
     so no locks needed for cross-node coordination

  2. Idempotent updates: fetch_max ensures that concurrent
     updates to verified_at converge to the same value

  3. Snapshot consistency: Readers see a consistent view,
     and can detect when their snapshot is stale

  4. Progress guarantee: incrementRevision always advances,
     ensuring no revision number collision
-/

end Whale.Concurrency
