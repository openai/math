import Mathlib.Data.Fin.Tuple.Sort
import Mathlib.Data.Fintype.Card
import Mathlib.Logic.Equiv.Prod
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

namespace OAI
/-! # Parallel stages of fixed short sorts

Each block reads and writes a fixed, ordered set of positions. Its action on
the records is the stable permutation used by the physical sort relation.
-/

namespace Hierarchy.Tagged.SortLift

open scoped BigOperators Classical
noncomputable section

structure Stage (n : ℕ) where
  blocks : ℕ
  length : Fin blocks → ℕ
  input : (Σ b, Fin (length b)) ≃ Fin n
  output : (Σ b, Fin (length b)) ≃ Fin n

variable {n : ℕ} {α κ : Type*} [LinearOrder κ]

def Stage.blockKey (S : Stage n) (key : α → κ) (x : Fin n → α) (b : Fin S.blocks)
    (j : Fin (S.length b)) : κ :=
  key (x (S.input ⟨b,j⟩))

def Stage.perm (S : Stage n) (key : α → κ) (x : Fin n → α) : Equiv.Perm (Fin n) :=
  S.output.symm.trans ((Equiv.sigmaCongrRight fun b => Tuple.sort (S.blockKey key x b)).trans S.input)

def Stage.eval (S : Stage n) (key : α → κ) (x : Fin n → α) : Fin n → α :=
  x ∘ S.perm key x

theorem Stage.eval_output (S : Stage n) (key : α → κ) (x : Fin n → α)
    (b : Fin S.blocks) (j : Fin (S.length b)) :
    S.eval key x (S.output ⟨b,j⟩) =
      x (S.input ⟨b, Tuple.sort (fun i => key (x (S.input ⟨b,i⟩))) j⟩) := by
  simp [Stage.eval,Stage.perm]
  rfl

def cutCount {ι : Type*} [Fintype ι] (p : ι → Prop) : ℕ :=
  (Finset.univ.filter p).card

theorem cutCount_equiv {ι ι' : Type*} [Fintype ι] [Fintype ι']
    (e : ι ≃ ι') (p : ι' → Prop) : cutCount (fun i => p (e i)) = cutCount p := by
  have h := Fintype.card_congr (e.subtypeEquiv (p := fun i => p (e i)) (q := p) fun _ => Iff.rfl)
  simpa only [cutCount,Fintype.card_subtype] using h

theorem Stage.lt_cut_iff (S : Stage n) (key : α → κ) (x : Fin n → α)
    (b : Fin S.blocks) (j : Fin (S.length b)) (t : κ) :
    key (S.eval key x (S.output ⟨b,j⟩)) < t ↔
      j.val < cutCount (fun i : Fin (S.length b) => key (x (S.input ⟨b,i⟩)) < t) := by
  rw [S.eval_output]
  let f := S.blockKey key x b
  have count := cutCount_equiv (Tuple.sort f) (fun i => f i < t)
  have rank := Tuple.lt_card_lt_iff_apply_lt_of_monotone
    (j := j) (a := t) (Tuple.monotone_sort f)
  change f (Tuple.sort f j) < t ↔ j.val < cutCount (fun i => f i < t)
  rw [← count]
  refine rank.symm.trans ?_
  apply iff_of_eq
  congr 1
  unfold cutCount
  apply congrArg Finset.card
  ext i
  simp []

def run (ss : List (Stage n)) (key : α → κ) (x : Fin n → α) : Fin n → α :=
  ss.foldl (fun y S => S.eval key y) x

def blockCount (ss : List (Stage n)) : ℕ := (ss.map Stage.blocks).sum

theorem run_perm (ss : List (Stage n)) (key : α → κ) (x : Fin n → α) :
    ∃ e : Equiv.Perm (Fin n), run ss key x = x ∘ e := by
  induction ss generalizing x with
  | nil => exact ⟨Equiv.refl _,rfl⟩
  | cons S ss ih =>
    obtain ⟨e,he⟩ := ih (S.eval key x)
    exact ⟨e.trans (S.perm key x),he⟩

theorem run_eq_sorted (ss : List (Stage n)) (x : Fin n → κ)
    (h : Monotone (run ss id x)) : run ss id x = x ∘ Tuple.sort x := by
  obtain ⟨e,he⟩ := run_perm ss id x
  rw [he] at h ⊢
  exact Tuple.comp_sort_eq_comp_iff_monotone.mpr h

end
end Hierarchy.Tagged.SortLift

end OAI
