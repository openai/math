import OAI.Computability.MultitapeWeakETH.CorrectedDisplay
import OAI.Computability.MultitapeWeakETH.MaskEntropy
import OAI.LinearAlgebra.MatrixMultiplication.Duality.EntropyHelpers

/-! # Entropy of the four physical masks on each block processor -/

namespace OAI.Computability.MultitapeWeakETH.FoldedNetwork

open Finset MatrixMultiplication MatrixMultiplication.Foundation
open scoped BigOperators Classical
noncomputable section

private def flatten {b : ℕ} (p : Fin 4 → Word b) : Word (4*b) := fun k =>
  let ri := finProdFinEquiv.symm k
  p ri.1 ri.2

private theorem flatten_injective {b : ℕ} : Function.Injective (flatten (b:=b)) := by
  intro p q eq
  funext r i
  simpa [flatten] using congrFun eq (finProdFinEquiv (r,i))

private theorem mask_at {n b : ℕ} (z : Fin 4 → Word n) (target : Fin 4 → Fin (2^n))
    (r : Fin 4) (j : Block n b) (i : Fin b) :
    errorMasks b z target r j i = true ↔
      ∃ hi : j.val*b+i.val < n, z r (⟨_,hi⟩ : Fin n).rev ≠ residueWord n (target r) (⟨_,hi⟩ : Fin n).rev := by
  rw [errorMasks,Difference.maskFor,← residueWord_reverse]
  by_cases pos : j.val*b+i.val < n
  · have eq (x : Word n) :
        Difference.message b j.val (List.ofFn x).reverse i = x (⟨_,pos⟩ : Fin n).rev := by
      have idx : j.val*b+i.val < (List.ofFn x).reverse.length := by simpa using pos
      simp only [Difference.message,List.getElem?_eq_getElem idx,Option.getD_some,List.getElem_reverse,List.getElem_ofFn]
      apply congrArg x
      apply Fin.ext
      simp only [List.length_ofFn,Fin.val_rev]
      omega
    rw [eq,eq]
    simp [pos]
  · simp [Difference.message,pos]

private theorem card_as_sum {I : Type} [Fintype I] (p : I → Bool) :
    (univ.filter fun i => p i).card = ∑ i, if p i then 1 else 0 := by simp

private theorem column_weight {n b : ℕ} (hb : 0 < b) (z : Fin 4 → Word n)
    (target : Fin 4 → Fin (2^n)) (r : Fin 4) :
    (∑ j : Block n b, (univ.filter fun i => errorMasks b z target r j i).card) ≤
      errors (z r) (residueWord n (target r)) := by
  let bad := univ.filter fun ji : Block n b × Fin b => errorMasks b z target r ji.1 ji.2
  have sum : (∑ j : Block n b, (univ.filter fun i => errorMasks b z target r j i).card) = bad.card := by
    unfold bad
    simp_rw [card_as_sum]
    rw [Fintype.sum_prod_type]
  rw [sum]
  let index (p : ↥bad) : Fin n :=
    (⟨p.val.1.val*b+p.val.2.val,((mask_at z target r _ _).mp (mem_filter.mp p.property).2).choose⟩ : Fin n).rev
  apply card_le_card_of_injective (f:=fun p => ⟨index p,mem_filter.mpr
    ⟨mem_univ _,((mask_at z target r _ _).mp (mem_filter.mp p.property).2).choose_spec⟩⟩)
  intro p q h
  have idx := congrArg (fun v => (Fin.rev v.val).val) h
  change (Fin.rev (index p)).val = (Fin.rev (index q)).val at idx
  simp only [index,Fin.rev_rev] at idx
  have high := congrArg (· / b) idx
  have low := congrArg (· % b) idx
  simp [Nat.mul_comm _ b,Nat.mul_add_div hb,Nat.div_eq_of_lt p.val.2.isLt,Nat.div_eq_of_lt q.val.2.isLt,
    Nat.mod_eq_of_lt p.val.2.isLt,Nat.mod_eq_of_lt q.val.2.isLt] at high low
  exact Subtype.ext (Prod.ext (Fin.ext high) (Fin.ext low))

/-- Four padded block masks are one joint site pin. Padding adds coordinates
with zero error. The law on the returned rows can be arbitrary. -/
theorem processor_entropy {A : Type} [Fintype A] {n b : ℕ} (hb : 0 < b) (p : FiniteLaw A)
    (z : A → Fin 4 → Word n) (target : A → Fin 4 → Fin (2^n))
    (budget : ∀ x r, 100*errors (z x r) (residueWord n (target x r)) ≤ n) :
    (∑ j : Block n b, finiteEntropy (p.map (fun x r => errorMasks b (z x) (target x) r j)).mass) ≤
      ((n ⌈/⌉ b : ℕ):ℝ)*(4*b:ℕ)*Real.binEntropy (1/100) := by
  let m := n ⌈/⌉ b
  let raw (j : Fin m) (x : A) := fun r => errorMasks b (z x) (target x) r j
  let mask (j : Fin m) (x : A) := flatten (raw j x)
  have weight (x : A) : (∑ j : Fin m, (univ.filter fun i => mask j x i).card) ≤ 4*(n/100) := by
    have per (j : Fin m) : (univ.filter fun i => mask j x i).card =
        ∑ r, (univ.filter fun i => raw j x r i).card := by
      simp_rw [card_as_sum]
      rw [← Fintype.sum_prod_type']
      apply Fintype.sum_equiv finProdFinEquiv.symm
      intro i
      rfl
    simp_rw [per]
    rw [sum_comm]
    have total := sum_le_sum (s:=univ) (fun (r : Fin 4) _ =>
      (column_weight hb (z x) (target x) r).trans (show errors (z x r) (residueWord n (target x r)) ≤ n/100 by
        have := budget x r; omega))
    simpa [raw,m] using total
  have cap : n ≤ m*b := by rw [mul_comm]; exact (ceilDiv_le_iff_le_mul hb).mp le_rfl
  have charged := mask_entropy p (fun _ : Fin m => 4*b) mask (e:=1/100) (by norm_num) (by norm_num) (by
    intro x
    simp only [sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul]
    rw [← Nat.cast_sum]
    have h : 100*(∑ j : Fin m, (univ.filter fun i => mask j x i).card) ≤ m*(4*b) := by
      calc
        _ ≤ 100*(4*(n/100)) := Nat.mul_le_mul_left 100 (weight x)
        _ = 4*(n/100*100) := by ring
        _ ≤ 4*(m*b) := Nat.mul_le_mul_left _ ((Nat.div_mul_le_self n 100).trans cap)
        _ = _ := by ring
    exact (by
      push_cast at *
      have bound := Nat.cast_le (α:=ℝ) |>.mpr h
      push_cast at bound
      linarith))
  have ent (j : Fin m) : finiteEntropy (p.map (mask j)).mass = finiteEntropy (p.map (raw j)).mass := by
    rw [← DualEntropyHelpers.map_comp_mass p (raw j) flatten]
    exact (p.map (raw j)).map_entropy_of_injective _ flatten_injective
  simpa only [ent,sum_const,card_univ,Fintype.card_fin,nsmul_eq_mul] using charged

end
end OAI.Computability.MultitapeWeakETH.FoldedNetwork
