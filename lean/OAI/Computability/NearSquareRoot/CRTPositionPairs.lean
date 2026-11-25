import OAI.Computability.NearSquareRoot.CRTPositionReflection
import Mathlib.Data.Fintype.Prod
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Grouping disjoint transpositions by chunk pair

A transposition of bit positions determines an unordered pair of chunks.
The same pair may label both ends, so this grouping includes transpositions
internal to a single chunk.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled

variable {α ι : Type*} [DecidableEq ι]
variable (u : Equiv.Perm α) (hu : Function.Involutive u)
variable (label : α → ι) (fixed : ∀ x, label (u x) = label x)

private def selected (j : ι) (x : α) : α := if label x = j then u x else x

include hu fixed in
private theorem selected_involutive (j : ι) : Function.Involutive (selected u label j) := by
  intro x
  by_cases h : label x = j <;> simp [selected, fixed, hu x, h]

private def selectPerm (j : ι) : Equiv.Perm α :=
  ⟨selected u label j, selected u label j, selected_involutive u hu label fixed j,
    selected_involutive u hu label fixed j⟩

private theorem apply_selected (js : List ι) (hj : js.Nodup) (x : α) :
    ((js.map (selectPerm u hu label fixed)).foldl (fun a v => v a) x) =
      if label x ∈ js then u x else x := by
  induction js generalizing x with
  | nil => simp
  | cons j t ih =>
    have h := List.nodup_cons.mp hj
    rw [List.map_cons, List.foldl_cons, ih h.2]
    change (if label (selected u label j x) ∈ t then u (selected u label j x)
      else selected u label j x) = _
    by_cases he : label x = j
    · simp [selected, he, fixed, h.1]
    · simp [selected, he]

/-- At most one involution per chunk pair suffices to perform all transpositions
of the given involution. Each stage moves positions only between its two chunks. -/
theorem exists_chunk_pair_factors {C B : Type*} [Fintype C] [LinearOrder C]
    (u : Equiv.Perm (C × B)) (hu : Function.Involutive u) :
    ∃ t : List (Equiv.Perm (C × B)), t.length ≤ Fintype.card C ^ 2 ∧
      (∀ v ∈ t, Function.Involutive v ∧ ∃ c d : C, ∀ p, v p ≠ p →
        (p.1 = c ∧ (v p).1 = d) ∨ (p.1 = d ∧ (v p).1 = c)) ∧
      ∀ p, t.foldl (fun a v => v a) p = u p := by
  classical
  let label (x : C × B) := (min x.1 (u x).1, max x.1 (u x).1)
  have fixed (x : C × B) : label (u x) = label x := by
    dsimp only [label]
    rw [hu x, min_comm, max_comm]
  let js := (Finset.univ : Finset (C × C)).toList
  refine ⟨js.map (selectPerm u hu label fixed), ?_, ?_, ?_⟩
  · simp [js, Fintype.card_prod, pow_two]
  · intro v hv
    obtain ⟨j, _, rfl⟩ := List.mem_map.mp hv
    refine ⟨selected_involutive u hu label fixed j, j.1, j.2, ?_⟩
    intro p hp
    by_cases h : label p = j
    · change (p.1 = j.1 ∧ (selected u label j p).1 = j.2) ∨
        (p.1 = j.2 ∧ (selected u label j p).1 = j.1)
      rw [selected, ite_eq_left h, ← h]
      rcases le_total p.1 (u p).1 with hl | hl <;> simp [label, hl]
    · exact False.elim (hp (ite_eq_right h))
  · intro p
    rw [apply_selected u hu label fixed js Finset.univ.nodup_toList]
    simp [js]

private theorem peelSwaps {A : Type*} [DecidableEq A] (xs : List A)
    (u : Equiv.Perm A) (hu : Function.Involutive u) :
    ∃ w : Equiv.Perm A, Function.Involutive w ∧ (∀ x ∈ xs, w x = x) ∧
      (∀ x, u x = x → w x = x) ∧ ∃ t : List (A × A), t.length = xs.length ∧
      (∀ q ∈ t, q.1 ∈ xs) ∧ ∀ x, t.foldl (fun a q => Equiv.swap q.1 q.2 a) (w x) = u x := by
  induction xs generalizing u with
  | nil => exact ⟨u, hu, by simp, fun _ h => h, [], rfl, by simp, fun _ => rfl⟩
  | cons a xs ih =>
    let s := Equiv.swap a (u a)
    let v := u.trans s
    have cancel (x : A) : s (s x) = x := s.symm_apply_apply x
    have comm (x : A) : u (s x) = s (u x) := by
      have h := u.injective.swap_apply a (u a) x
      rw [hu a, Equiv.swap_comm (u a) a] at h
      exact h.symm
    have hv : Function.Involutive v := by
      intro x
      change s (u (s (u x))) = x
      rw [comm, hu x, cancel]
    have va : v a = a := Equiv.swap_apply_right ..
    have preserve (x : A) (fixed : u x = x) : v x = x := by
      change Equiv.swap a (u a) (u x) = x
      rw [fixed]
      by_cases ha : x = a
      · subst x
        rw [fixed, Equiv.swap_apply_left]
      · exact Equiv.swap_apply_of_ne_of_ne ha (fun eq => ha (u.injective (fixed.trans eq)))
    obtain ⟨w, hw, hx, hf, t, ht, small, run⟩ := ih v hv
    refine ⟨w, hw, ?_, fun x e => hf x (preserve x e), t ++ [(a, u a)], ?_, ?_, ?_⟩
    · intro x mem
      rcases List.mem_cons.mp mem with rfl | h
      · exact hf _ va
      · exact hx x h
    · simp [ht]
    · intro q h
      rcases List.mem_append.mp h with h | h
      · exact List.mem_cons_of_mem _ (small q h)
      · obtain rfl := List.mem_singleton.mp h
        exact List.mem_cons_self
    · intro x
      rw [List.foldl_append, run]
      exact cancel (u x)

/-- An involution on the bulk positions together with a tail of length `r`
requires at most `r` extra swaps. The remaining bulk involution fixes every
tail position. Swaps with equal endpoints give the identity. -/
theorem exists_tail_swaps {P : Type*} {r : ℕ} [DecidableEq P]
    (u : Equiv.Perm (P ⊕ Fin r)) (hu : Function.Involutive u) :
    ∃ v : Equiv.Perm P, Function.Involutive v ∧ ∃ t : List ((P ⊕ Fin r) × (P ⊕ Fin r)),
      t.length ≤ r ∧ (∀ q ∈ t, ∃ j : Fin r, q.1 = Sum.inr j) ∧
      ∀ p, t.foldl (fun a q => Equiv.swap q.1 q.2 a) ((v.sumCongr (Equiv.refl _)) p) = u p := by
  let xs := (List.finRange r).map (Sum.inr (α := P))
  obtain ⟨w, hw, tails, _, t, hlen, hmem, run⟩ := peelSwaps xs u hu
  have fixed (j : Fin r) : w (.inr j) = .inr j := tails _ (by simp [xs])
  have stays (p : P) : ∃ b : P, w (.inl p) = .inl b := by
    cases h : w (.inl p) with
    | inl b => exact ⟨b, rfl⟩
    | inr j => exact False.elim (Sum.inl_ne_inr (w.injective (h.trans (fixed j).symm)))
  let f (p : P) := (stays p).choose
  have e (p : P) : w (.inl p) = .inl (f p) := (stays p).choose_spec
  have invol : Function.Involutive f := by
    intro p
    apply Sum.inl.inj (β := Fin r)
    rw [← e (f p), ← e p, hw (.inl p)]
  let v : Equiv.Perm P := ⟨f, f, invol, invol⟩
  have restrict (p : P ⊕ Fin r) : (v.sumCongr (Equiv.refl _)) p = w p := by
    cases p with
    | inl a => exact (e a).symm
    | inr j => exact (fixed j).symm
  refine ⟨v, invol, t, ?_, ?_, fun p => (restrict p) ▸ run p⟩
  · simp [hlen, xs]
  · intro q h
    obtain ⟨j, _, hj⟩ := List.mem_map.mp (hmem q h)
    exact ⟨j, hj.symm⟩

/-- Three consecutive equally sized position chunks, followed by at most two
individual positions. -/
def threeChunksWithTail (k : ℕ) : Fin k ≃ ((Fin 3 × Fin (k / 3)) ⊕ Fin (k % 3)) :=
  (((finProdFinEquiv.sumCongr (Equiv.refl _)).trans finSumFinEquiv).trans
    (finCongr (show 3 * (k / 3) + k % 3 = k by omega))).symm

@[simp] theorem threeChunksWithTail_bulk (k : ℕ) (c : Fin 3) (p : Fin (k / 3)) :
    ((threeChunksWithTail k).symm (.inl (c,p))).val = p.val + k / 3 * c.val := rfl

@[simp] theorem threeChunksWithTail_tail (k : ℕ) (j : Fin (k % 3)) :
    ((threeChunksWithTail k).symm (.inr j)).val = 3 * (k / 3) + j.val := rfl

end Controlled

end NearSquareRoot
end Computability
end OAI
