import OAI.LinearAlgebra.SpectralBooks.CopyLabelTensor
import OAI.LinearAlgebra.SpectralBooks.Prices

/-! # Copying a coefficient label in a tensor power

Grouping the powers of a tensor with a copied label gives the same restriction
class as copying the entire label word after grouping.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

namespace SiteTensor.Raw

open scoped Classical

variable {I : Type} {K : Type*} [Fintype I] [Nonempty I] [Field K]

theorem ofRaw_powerTensor (T : Raw.{0} I K) (m : ℕ) :
    ofRaw (T.powerTensor m) = ofRaw T ^ m :=
  ofRaw_groupedPower m T.coeff

omit [Fintype I] [Nonempty I] in
/-- If two local labels agree on the support, their words also agree on
the support of any power, including after encoding the word. -/
theorem powerTensor_labels_match (T : Raw.{0} I K) {a b : I} {D E : Type*}
    (ha : T.Leg a → D) (hb : T.Leg b → D)
    (hmatch : ∀ x, T.coeff x ≠ 0 → ha (x a) = hb (x b))
    (m : ℕ) (encode : (Fin m → D) → E) (x : ∀ i, (T.powerTensor m).Leg i)
    (hx : (T.powerTensor m).coeff x ≠ 0) :
    encode (fun j => ha (x a j)) = encode (fun j => hb (x b j)) := by
  apply congrArg encode
  funext j
  apply hmatch (fun i => x i j)
  intro hj
  exact hx (Finset.prod_eq_zero (Finset.mem_univ j) hj)

private def wordCopyEquiv {A B D E : Type} {m : ℕ} (e : (Fin m → D) ≃ E) :
    (Fin m → A × (B → D)) ≃ (Fin m → A) × (B → E) where
  toFun x := (fun j => (x j).1, fun u => e (fun j => (x j).2 u))
  invFun x := fun j => (x.1 j, fun u => e.symm (x.2 u) j)
  left_inv x := by simp
  right_inv x := by simp

/-- The entire copied word may use any alphabet in bijection with words of
length `m`. Taking `D = Fin q` and `E = Fin (q ^ m)` gives the CD power step. -/
theorem ofRaw_appendLabel_power (T : Raw.{0} I K) (s : I) {D E : Type} [Fintype D] [Fintype E]
    (label : (∀ i, T.Leg i) → D) (m : ℕ) (e : (Fin m → D) ≃ E) :
    ofRaw ((T.powerTensor m).appendLabel s E (fun x => e (fun j => label (fun i => x i j)))) =
      ofRaw (T.appendLabel s D label) ^ m := by
  classical
  rw [← ofRaw_powerTensor]
  symm
  apply Quotient.sound
  apply reindex_equivalent (fun _ => wordCopyEquiv e)
  intro x
  let w : Fin m → D := fun j => (x s j).2 ⟨(), rfl⟩
  let l : Fin m → D := fun j => label (fun i => (x i j).1)
  let t : Fin m → K := fun j => T.coeff (fun i => (x i j).1)
  change (∏ j, if w j = l j then t j else 0) = if e w = e l then ∏ j, t j else 0
  by_cases h : w = l
  · simp [h]
  · rw [ite_eq_right (fun he => h (e.injective he))]
    obtain ⟨j, hj⟩ := Function.ne_iff.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ j) (ite_eq_right hj)

end SiteTensor.Raw

end SpectralBooks
end LinearAlgebra
end OAI
