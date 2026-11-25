import OAI.LinearAlgebra.FiniteFourier.JetOpenAssemblyMatrix
import OAI.LinearAlgebra.FiniteFourier.JetOpenAssemblyBasis
import OAI.LinearAlgebra.FiniteFourier.DyadicLayerCost

/-! # Synchronized layers on jet coordinates

A synchronized monomial layer uses one fixed jet multiplier at each address.
The operand basis identifies the resulting decoded matrix action with scalar
restriction on the full array.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

open Matrix Polynomial

variable {R S : Type*} [CommRing R] [CommRing S] {e h : ℕ}

variable {φ : R →+* S} {η : S} {m : S[X]}

/-- A scaled address permutation fits in forty times the coordinate volume
times the shorter-length envelope, including zero and nonunit scalings. -/
theorem JetCircuitsOver.monomialLayer {I : Type*} [Fintype I] [DecidableEq I]
    (jets : JetCircuitsOver φ η m e h)
    (basis : Function.Bijective (fun u : Fin 2 → R => φ (u 0) + η * φ (u 1)))
    (hm : m.Monic) (hd : m.natDegree = e) (he : 0 < e) (hh : 0 < h) {s : ℕ}
    (hc : 2*e*h ≤ s) (perm : Equiv.Perm I) (scale : I → JetQuotient m h) :
    JetMatrixCircuit φ η m e h (fun i j => if perm i = j then scale i else 0)
      ((Fintype.card I : ℝ) * (40*e*h*convolutionEnvelope s)) := by
  choose g hg p hp using fun i => jets.operandScale_envelope basis hm hd he hh hc (scale i)
  obtain ⟨t, ht, q, hq⟩ := circuit_family p
  let c := q.rewire (fun i => (1,(perm i.1,i.2))) (fun j : I × ((Fin h × Fin e) × Fin 2) =>
    (1,⟨j.1,j.2⟩))
  refine ⟨t, ?_, c, fun x => funext fun i => ?_⟩
  · have ht' : (t : ℝ) ≤ ∑ i, (g i : ℝ) := by exact_mod_cast ht
    exact ht'.trans (by simpa using Finset.sum_le_sum (fun i (_ : i ∈ Finset.univ) => hg i))
  · have heval : (fun j => c.eval x (i,j)) = (p i).eval (fun j => x (perm i,j)) := by
      funext j
      simp [c, Circuit.eval_rewire, hq, Function.comp_def]
    change jetOperandValue φ η m (fun j => c.eval x (i,j)) = _
    rw [heval, hp]
    simp [mulVec, dotProduct, ite_mul, jetOperandArray]

section Restriction

variable [Algebra R S]

private theorem jetOperandArray_eq_packInputs {T : Type*}
    (hb : Function.Bijective (fun t : Fin 2 → R => algebraMap R S (t 0) + η*algebraMap R S (t 1)))
    (hm : m.Monic) (hd : m.natDegree = e) (he : 0 < e)
    (x : T × ((Fin h × Fin e) × Fin 2) → R) :
    jetOperandArray (algebraMap R S) η m x = packInputs (jetOperandBasis η hb hm hd he h) x := by
  funext i
  exact (jetOperandBasis_decode η hb hm hd he _).symm.trans (Module.Basis.equivFun_symm_apply ..)

/-- A circuit for the restriction to the operand basis acts by the original
matrix on decoded jets. -/
theorem JetMatrixCircuit.of_restrict {I O : Type*} [Fintype I]
    (hb : Function.Bijective (fun x : Fin 2 → R => algebraMap R S (x 0) + η*algebraMap R S (x 1)))
    (hm : m.Monic) (hd : m.natDegree = e) (he : 0 < e)
    {A : Matrix O I (JetQuotient m h)} {g : ℕ} {C : ℝ}
    (hq : RealizableAtMost (restrictMatrix (jetOperandBasis η hb hm hd he h) A) g)
    (hg : (g : ℝ) ≤ C) : JetMatrixCircuit (algebraMap R S) η m e h A C := by
  obtain ⟨s, hs, q, hq⟩ := hq
  refine ⟨s, (by exact_mod_cast hs : (s : ℝ) ≤ g) |>.trans hg, q, fun x => ?_⟩
  rw [jetOperandArray_eq_packInputs hb hm hd he, Circuit.eval_eq_mulVec, hq,
    restrictMatrix_mulVec, pack_unpack, jetOperandArray_eq_packInputs hb hm hd he]

/-- A synchronized word on a finite array of jets is realized over the base
ring with one fixed multiplier per address and a tensor shear on each basis coordinate. -/
theorem LayerWord.jetMatrixCircuit {I : Type} [Fintype I] [DecidableEq I]
    {A : Matrix I I (JetQuotient m h)} {d s : ℕ} {β C : ℝ} (w : LayerWord d A)
    (jets : JetCircuitsOver (algebraMap R S) η m e h)
    (hb : Function.Bijective (fun t : Fin 2 → R => algebraMap R S (t 0) + η*algebraMap R S (t 1)))
    (hm : m.Monic) (hd : m.natDegree = e) (he : 0 < e) (hh : 0 < h) (hc : 2*e*h ≤ s)
    (ht : ShearTensorBound R β C) (hβ : 0 ≤ β) (hC : 0 ≤ C) :
    JetMatrixCircuit (algebraMap R S) η m e h A
      (d * ((Fintype.card I : ℝ)*(40*e*h*convolutionEnvelope s) +
        (2*e*h)*(C*(Fintype.card I : ℝ)*(1+Real.logb 2 (Fintype.card I))^β))) := by
  let V : ℝ := Fintype.card I
  let M : ℝ := 40*e*h*convolutionEnvelope s
  let H : ℝ := C*V*(1+Real.logb 2 V)^β
  have hreal := w.realizable_restrict_of_shear_bound (jetOperandBasis η hb hm hd he h)
    (fun u => jets.operandMatrix_envelope η hb hm hd he hh hc (u : JetQuotient m h)) ht hβ hC
  apply JetMatrixCircuit.of_restrict hb hm hd he hreal
  have hM : 0 ≤ M := by
    have h1 := convolutionEnvelope_one_le ((by positivity : 0 < 2*e*h).trans_le hc)
    dsimp [M]
    positivity
  have hlog : 0 ≤ Real.logb 2 V := by
    cases hcI : Fintype.card I with
    | zero => simp [V, hcI]
    | succ k =>
      exact Real.logb_nonneg (by norm_num) (by dsimp [V]; exact_mod_cast (by omega : 1 ≤ Fintype.card I))
  have hH : 0 ≤ H := by dsimp [H,V] at *; positivity
  simp only [Fintype.card_prod, Fintype.card_fin, Nat.cast_mul, Nat.cast_add, Nat.cast_ofNat]
  change (d : ℝ) * (V * (⌊M⌋₊ : ℝ) + (h*e*2 : ℝ) * (⌊H⌋₊ : ℝ)) ≤ _
  rw [show (h*e*2 : ℝ) = 2*e*h by ring]
  gcongr
  · exact Nat.floor_le hM
  · exact Nat.floor_le hH

end Restriction

end FiniteFourier
end LinearAlgebra
end OAI
