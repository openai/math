import OAI.Computability.VPVNP.ChainAssignments
import OAI.Computability.VPVNP.LiveModes

/-! # Raw cut assignments of the two live modes

The cut at the midpoint carries the accumulated exponents. Each later
interior cut carries a configuration of the evaluator. The two missing
endpoint cuts have unique empty strings. Local agreement of neighboring
mode flags forces a single flag throughout the whole chain.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ChainAssignments

open CutSchedule ExponentTrace LiveChain

/-- The cut following a first-half group, counting from the first interior cut through the
midpoint. -/
def firstCut {h : ℕ} (i : Fin (2^h)) : Fin (2^(h+1)+1) :=
  ⟨i.val+1, by have := i.isLt; rw [pow_succ]; omega⟩

/-- An interior cut strictly after the midpoint, indexed by its position among the evaluator
configuration cuts. -/
def laterCut {h : ℕ} (i : Fin (2^h-1)) : Fin (2^(h+1)+1) :=
  ⟨2^h+(i.val+1), by have := i.isLt; rw [pow_succ]; omega⟩

theorem coverCuts {h : ℕ} (j : Fin (2^(h+1)+1)) :
    j = 0 ∨ j = Fin.last (2^(h+1)) ∨ (∃ i, j = firstCut i) ∨ ∃ i, j = laterCut i := by
  by_cases hz : j.val = 0
  · exact Or.inl (Fin.ext hz)
  by_cases hl : j.val = 2^(h+1)
  · exact Or.inr (Or.inl (Fin.ext hl))
  by_cases hj : j.val ≤ 2^h
  · exact Or.inr (Or.inr (Or.inl ⟨⟨j.val-1, by omega⟩, Fin.ext (by dsimp [firstCut]; omega)⟩))
  have hb := j.isLt
  have hp := pow_succ (2 : ℕ) h
  exact Or.inr (Or.inr (Or.inr ⟨⟨j.val-(2^h+1), by omega⟩, Fin.ext (by dsimp [laterCut]; omega)⟩))

private def joinCuts {h Δ : ℕ} (fst : LiveBits h Δ) (lst : TailBits h Δ) (j : Fin (2^(h+1)+1)) :
    Bits (width (h+1) Δ j.val) :=
  if hj : 0 < j.val ∧ j.val ≤ 2^h then
    let i : Fin (2^h) := ⟨j.val-1, by omega⟩
    (show i.val+1 = j.val by dsimp [i]; omega) ▸ fst i
  else if hk : 2^h < j.val ∧ j.val < 2^(h+1) then
    let i : Fin (2^h-1) := ⟨j.val-(2^h+1), by have := pow_succ (2 : ℕ) h; omega⟩
    (show 2^h + (i.val+1) = j.val by dsimp [i]; omega) ▸ lst i
  else fun _ => false

private theorem join_first {h Δ : ℕ} (fst : LiveBits h Δ) (lst : TailBits h Δ) (i : Fin (2^h)) :
    joinCuts fst lst (firstCut i) = fst i := by
  have hi := i.isLt
  simp [joinCuts, firstCut, Nat.succ_le_iff.mpr hi]

private theorem join_later {h Δ : ℕ} (fst : LiveBits h Δ) (lst : TailBits h Δ) (i : Fin (2^h-1)) :
    joinCuts fst lst (laterCut i) = lst i := by
  have hi := i.isLt
  have h1 : ¬(0 < 2^h+(i.val+1) ∧ 2^h+(i.val+1) ≤ 2^h) := by omega
  have h2 : 2^h < 2^h+(i.val+1) ∧ 2^h+(i.val+1) < 2^(h+1) := by rw [pow_succ]; omega
  have heq : 2^h + (i.val+1) - (2^h+1) = i.val := by omega
  dsimp only [joinCuts, laterCut]
  split
  · contradiction
  · have transport (k : Fin (2^h-1)) (same : k = i)
        (hw : 2^h+(k.val+1) = 2^h+(i.val+1)) :
        (hw ▸ lst k : Bits (width (h+1) Δ (2^h+(i.val+1)))) = lst i := by
      subst k
      rfl
    apply transport
    exact Fin.ext heq

/-- Raw physical cuts are exactly the first-half and tail fields with no
extra choices for either missing endpoint. -/
def liveCutEquiv (h Δ : ℕ) : AllCuts h Δ ≃ LiveBits h Δ × TailBits h Δ where
  toFun c := (fun i => c (firstCut i), fun i => c (laterCut i))
  invFun x := joinCuts x.1 x.2
  left_inv c := by
    funext j
    rcases coverCuts j with rfl | rfl | ⟨i,rfl⟩ | ⟨i,rfl⟩
    · funext k
      exact Fin.elim0 (k.cast (width_zero _ _))
    · funext k
      exact Fin.elim0 (k.cast (width_end _ _))
    · apply join_first
    · apply join_later
  right_inv x := Prod.ext (funext (join_first x.1 x.2)) (funext (join_later x.1 x.2))

/-- Equality at every interior group propagates the first mode flag to all
interior cuts. The case of a single interior cut needs no comparisons. -/
theorem commonMode {n : ℕ} (flags : Fin (n+1) → Bool)
    (interior : ∀ i : Fin n, flags i.castSucc = flags i.succ) :
    ∃! mode, ∀ i, flags i = mode := by
  refine ⟨flags 0, ?_, fun mode hm => (hm 0).symm⟩
  intro i
  induction i using Fin.induction with
  | zero => rfl
  | succ j ih => exact (interior j).symm.trans ih

end ChainAssignments

end VPVNP
end Computability
end OAI
