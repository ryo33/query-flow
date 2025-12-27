/-
  Reusable helper lemmas for Whale specification proofs
-/

import Mathlib.Tactic

namespace Whale

/-! ## List.all Congruence Lemmas -/

/-- If two predicates agree pointwise, List.all agrees -/
theorem List.all_congr {α : Type*} {f g : α → Bool} (h : ∀ a, f a = g a) (l : List α) :
    l.all f = l.all g := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [List.all_cons, h, ih]

/-- List.all under function composition -/
theorem List.all_map_eq {α β : Type*} (f : α → β) (p : β → Bool) (l : List α) :
    (l.map f).all p = l.all (p ∘ f) := by
  induction l with
  | nil => rfl
  | cons hd tl ih => simp [List.all_cons, ih]

/-! ## Foldl Preservation Lemmas -/

/-- Generic foldl preservation: if step preserves P, foldl preserves P -/
theorem List.foldl_preserves {α β : Type*} {P : β → Prop} {f : β → α → β}
    (h_step : ∀ b a, P b → P (f b a)) {init : β} (h_init : P init) (l : List α) :
    P (l.foldl f init) := by
  induction l generalizing init with
  | nil => exact h_init
  | cons hd tl ih => exact ih (h_step init hd h_init)

/-- Foldl preserves property with witness extraction -/
theorem List.foldl_preserves_exists {α β γ : Type*}
    {f : β → α → β} {P : β → γ → Prop}
    (h_step : ∀ b a w, P b w → ∃ w', P (f b a) w')
    {init : β} {w₀ : γ} (h_init : P init w₀) (l : List α) :
    ∃ w, P (l.foldl f init) w := by
  induction l generalizing init w₀ with
  | nil => exact ⟨w₀, h_init⟩
  | cons hd tl ih =>
    obtain ⟨w', hw'⟩ := h_step init hd w₀ h_init
    exact ih hw'

/-- Foldl preserves "some" when step does -/
theorem List.foldl_preserves_some {α β γ : Type*} {f : (α → Option β) → γ → (α → Option β)}
    (key : α) (ns : α → Option β) (l : List γ) (n : β)
    (h_init : ns key = some n)
    (h_step : ∀ ns' d n', ns' key = some n' → ∃ n'', (f ns' d) key = some n'') :
    ∃ n', (l.foldl f ns) key = some n' := by
  induction l generalizing ns n with
  | nil => exact ⟨n, h_init⟩
  | cons hd tl ih =>
    obtain ⟨n', hn'⟩ := h_step ns hd n h_init
    exact ih (ns := f ns hd) (n := n') hn'

/-! ## Option Handling -/

/-- Unwrap option with default -/
theorem Option.getD_some_eq {α : Type*} (a b : α) :
    (some a).getD b = a := rfl

theorem Option.getD_none_eq {α : Type*} (b : α) :
    (none).getD b = b := rfl

end Whale
