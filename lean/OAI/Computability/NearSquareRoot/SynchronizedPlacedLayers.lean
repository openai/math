import OAI.Computability.NearSquareRoot.SynchronizedPrimitive
import OAI.Computability.NearSquareRoot.SynchronizedPadding
import Mathlib.Logic.Equiv.Fintype
import Mathlib.Tactic

/-! Relocating and replicating a primitive short-transform layer. In a block of
even cardinality the unused cells of a pair stage can themselves be matched
into identity pairs. -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ShortFourier

open Matrix SynchronizedPair SynchronizedPadding

variable {A B S : Type} [DecidableEq A] [DecidableEq B] [DecidableEq S]

private theorem layer_of_eq {M N : Matrix A A ℂ} (h : ShortLayer N) (e : M = N) : ShortLayer M := e ▸ h

theorem ShortLayer.relocate {M : Matrix A A ℂ} (h : ShortLayer M) (e : A ≃ B) :
    ShortLayer (M.submatrix e.symm e.symm) := by
  cases h with
  | permutation p =>
    let q := (e.symm.trans p).trans e
    apply layer_of_eq (ShortLayer.permutation q)
    ext i j
    change (if e.symm i = p (e.symm j) then (1 : ℂ) else 0) =
      if i = e (p (e.symm j)) then 1 else 0
    simp only [Equiv.symm_apply_eq]
  | phase d hd =>
    rw [submatrix_diagonal_equiv]
    exact .phase _ (fun i ↦ hd _)
  | pairs f V hv hva =>
    exact .pairs (f.trans e) V hv hva

theorem ShortLayer.copies {M : Matrix A A ℂ} (h : ShortLayer M) :
    ShortLayer (blockDiagonal fun _ : S ↦ M) := by
  cases h with
  | permutation e =>
    apply layer_of_eq (ShortLayer.permutation (e.prodCongr (Equiv.refl S)))
    ext ⟨i,s⟩ ⟨j,t⟩
    change (if s = t then if i = e j then (1 : ℂ) else 0 else 0) =
      if (i,s) = (e j,t) then 1 else 0
    simp [Prod.mk.injEq, ← ite_and, and_comm]
  | phase d hd =>
    rw [blockDiagonal_diagonal]
    exact .phase _ fun i ↦ hd _
  | @pairs T _ e V hv hva =>
    let g := (Equiv.prodAssoc (Fin 2) T S).symm.trans (e.prodCongr (Equiv.refl S))
    convert ShortLayer.pairs g (fun u : T × S ↦ V u.1) (fun u ↦ hv _) (fun u ↦ hva _) using 1
    ext ⟨i,s⟩ ⟨j,t⟩
    change (if s = t then
      if (e.symm i).2 = (e.symm j).2 then V (e.symm i).2 (e.symm i).1 (e.symm j).1 else 0 else 0) =
      if ((e.symm i).2,s) = ((e.symm j).2,t)
      then V (e.symm i).2 (e.symm i).1 (e.symm j).1 else 0
    simp [Prod.mk.injEq, ← ite_and, and_comm]

variable [Fintype A] [Fintype B]

/-- Fill the unused complement of a primitive stage on an even block.
For a pair stage the parity of the complement follows from the occupied pairs. -/
theorem ShortLayer.withUnused {M : Matrix A A ℂ} (h : ShortLayer M)
    (heven : Even (Fintype.card A + Fintype.card B)) :
    ShortLayer (axisPadding (b := B) M) := by
  classical
  cases h with
  | permutation p =>
    apply layer_of_eq (ShortLayer.permutation (p.sumCongr (Equiv.refl B)))
    ext (i | i) (j | j) <;> simp [axisPadding, Matrix.fromBlocks, one_apply]
  | phase d hd =>
    let d' := Sum.elim d (fun _ : B ↦ 1)
    convert ShortLayer.phase d' (fun i ↦ by cases i <;> simp [d', hd]) using 1
    ext (i | i) (j | j) <;> simp [axisPadding, diagonal_apply, d', one_apply]
  | @pairs T _ e V hv hva =>
    have : Finite T := Finite.of_injective (fun t : T ↦ e (0,t))
      (fun x y h ↦ congrArg Prod.snd (e.injective h))
    let _ := Fintype.ofFinite T
    have hc := Fintype.card_congr e
    simp only [Fintype.card_prod, Fintype.card_fin] at hc
    obtain ⟨n,hn⟩ := heven
    let C := Fin (Fintype.card B / 2)
    let f : Fin 2 × C ≃ B := Fintype.equivOfCardEq <| by simp [C]; omega
    let g := (Equiv.prodSumDistrib (Fin 2) T C).trans (e.sumCongr f)
    let D : T ⊕ C → PairMatrix := Sum.elim V (fun _ ↦ 1)
    convert ShortLayer.pairs g D (fun z ↦ by
      cases z with
      | inl t => exact hv t
      | inr t => exact identity_threeWalsh) (fun z ↦ by
      cases z with
      | inl t => exact hva t
      | inr t => simpa [D] using identity_threeWalsh) using 1
    ext (i | i) (j | j)
    · simp [axisPadding, g, D, blockDiagonal_apply, submatrix_apply]
    · simp [axisPadding, g, D, blockDiagonal_apply, submatrix_apply]
    · simp [axisPadding, g, D, blockDiagonal_apply, submatrix_apply]
    · simp [axisPadding, g, D, blockDiagonal_apply, submatrix_apply, one_apply]
      have hij : (i = j) ↔ ((f.symm i).2 = (f.symm j).2 ∧ (f.symm i).1 = (f.symm j).1) := by
        rw [← f.symm.injective.eq_iff, Prod.ext_iff, and_comm]
      simp [hij, ← ite_and]

end ShortFourier

end NearSquareRoot
end Computability
end OAI
