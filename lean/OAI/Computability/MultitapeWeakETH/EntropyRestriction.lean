import OAI.Computability.MultitapeWeakETH.CodedRestriction
import OAI.Computability.MultitapeWeakETH.ColorRate

/-! # Exact-type realization of the finite entropy comparison -/

namespace OAI.Computability.MultitapeWeakETH

open VPVNP.WireTensor Finset MatrixMultiplication.Foundation
open LabelHierarchyCounts StageHierarchyResources
open scoped BigOperators Classical

private theorem population_map {R A B : Type} [Fintype R] [Fintype A] [Fintype B]
    (w : R → A) (f : A → B) (b : B) :
    wordPopulation (f ∘ w) b = pushforwardCounts (wordPopulation w) f b := by
  classical
  have count := sum_card_fiberwise_eq_card_filter (univ : Finset R) (univ.filter fun a => f a = b) w
  simpa only [pushforwardCounts,wordPopulation,Fintype.card_subtype,mem_filter,mem_univ,true_and,
    sum_filter,Function.comp_apply] using count.symm

/-- The pin alphabet on each spoke consists only of streams of its prescribed
marginal type. The demand wires have the independent binary widths obtained
from the conditional extension pools. All endpoint coincidences are allowed. -/
theorem exact_type_wire_restriction {K J A : Type} [Field K] [Fintype J] [Fintype A]
    (T : Tensor K J) (root : J) (Pin : J → Type) [∀ j, Fintype (Pin j)] (pin : ∀ j, A → Pin j)
    (counts : A → ℕ) (labels : ℕ → A → Bool) (depth t : ℕ)
    (separate : Function.Injective (labelRecordOf labels depth))
    (large : depth+1 < t*(∑ x, counts x)) (u v : Fin depth → J)
    (maps : ∀ j, Pin j → (wireNetwork (k := K) u v (fun _ => Bool)).Basis j → T.Basis j → K)
    (scalar : A → K) (nz : ∀ a, scalar a ≠ 0)
    (display : ∀ a, applyLocal (fun j => maps j (pin j a)) T.coeff =
      fun b => if b = edgeAssignment u v (fun j => labels j a) then scalar a else 0) :
    let r := t*∑ a, counts a
    let Stream := fun j => PopulationWords (Fin r) (fun q => t*pushforwardCounts counts (pin j) q)
    Restricts (tensorProduct (tensorFamilyProduct (fun _ : Fin r => T))
      (wireNetwork (fun _ : J => root) id Stream)) (wireNetwork u v
        (fun j => Fin (2^colorBits (stageRefinementCount counts labels j t) r))) := by
  intro r Stream
  let L (j : Fin depth) := Fin (2^colorBits (stageRefinementCount counts labels j t) r)
  let B := (wireNetwork (k := K) u v (fun _ => Bool)).Basis
  obtain ⟨color,allColors⟩ := exact_type_binary_labels counts labels depth t separate large
  choose words hits using allColors
  let chosen (s : (j : Fin depth) → L j) := (words s).val
  let index (j : J) (s : (e : Fin depth) → L e) : Stream j := by
    refine ⟨(pin j) ∘ chosen s,fun q => ?_⟩
    rw [population_map]
    unfold pushforwardCounts
    simp only [mul_sum]
    apply sum_congr rfl
    intro a _
    by_cases h : pin j a = q <;> simp only [h,ite_true,ite_false,mul_zero]
    exact (words s).property a
  let read (j : J) (chunks : Fin r → B j) : (wireNetwork (k := K) u v L).Basis j :=
    ⟨fun e h => color e (fun i => (chunks i).1 e h), fun e h => color e (fun i => (chunks i).2 e h)⟩
  refine coded_wire_restriction T root B Pin Stream pin maps
    (fun a => edgeAssignment u v (fun j => labels j a)) scalar nz ?_ u v L chosen index
    (fun _ stream => stream.val) (fun _ _ _ => rfl) read ?_
  · intro a
    rw [display]
    funext z
    split <;> split <;> first | rfl | (rename_i h₁ h₂; exact False.elim (h₁ h₂)) | (rename_i h₁ h₂; exact False.elim (h₂ h₁))
  intro s j
  apply Prod.ext
  · funext e h
    exact hits s e
  · funext e h
    exact hits s e

end OAI.Computability.MultitapeWeakETH
