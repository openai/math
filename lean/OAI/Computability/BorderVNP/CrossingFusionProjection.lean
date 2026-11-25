import OAI.Computability.BorderVNP.CrossingFusionAssembly
import OAI.Computability.BorderVNP.CrossingFrameProjection

/-!
# Specialization to the signed universal path polynomial

The complete Boolean frame emits one variable for each selected external
group label and a scalar `-1` for each negative local path. Its weighted
sum is exactly the side polynomial. A signed weighted-CNF query places
this sum in the universal family by literal projection at all sufficiently
large input lengths.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.FusionStage

open VPVNP MvPolynomial
open scoped Classical

variable {m d p : ℕ} {w : WireStates (leastEnergy m) (2^m)} {left : Bool} {b : Fin d → Bool}

/-- The variable weights of the external flags and the minus-one weight of each signed stage. -/
def labelWeights (R : Type*) [CommRing R] : Projection R (Labels d p m) ((Fin d ⊕ Fin p) × Fin (2^m)) :=
  Sum.elim Sum.inl (fun _ => Sum.inr (-1))

private theorem signProduct {i : Fin d} (s : Fin d → Bool → Bool) (h : s i false ≠ s i true) :
    signValue (s i) = if s i true then -1 else 1 := by
  cases hf : s i false <;> cases ht : s i true <;> simp_all [signValue]

private theorem flag_product (R : Type*) [CommRing R] {f : Checkers w left b}
    {addr : CutBit d (2*leastEnergy m) (stateCountAt (d*leastEnergy m)) ↪ Fin p × Fin m}
    (F : CompleteFrame f addr) (g : Data f) :
    (if F.circuit.eval (encode f g) none then
      ∏ j, if F.circuit.eval (encode f g) (some j) then (labelWeights R j).elim X C else 1 else 0) =
    (pathSign f g.1 g.2.1 g.2.2.1 g.2.2.2 : MvPolynomial _ R) *
      sideMonomial R g.1 (binaryBridge addr (g.2.1,maskIndex _ (g.2.2.1 (Fin.last d)))) := by
  let s := stageFlags f g.1 g.2.1 g.2.2.1 g.2.2.2
  have hlegal : legal f (encode f g) := (legal_iff f _).mpr ⟨g,rfl⟩
  have ha : F.circuit.eval (encode f g) none = true ↔ ∀ i, s i false ≠ s i true := by
    rw [F.accepted, and_iff_right hlegal]
    simp only [s, stageFrame_encode]
  by_cases hs : ∀ i, s i false ≠ s i true
  · rw [ite_eq_left (ha.mpr hs), Fintype.prod_sum_type, Fintype.prod_prod_type]
    simp only [labelWeights, Sum.elim_inl, Sum.elim_inr, F.flag, F.negative, decide_eq_true_eq,
      Finset.prod_ite_eq, Finset.mem_univ, ↓reduceIte, map_neg, map_one, Fintype.prod_sum_type,
      sideMonomial]
    rw [mul_comm]
    congr 1
    rw [pathSign, Int.cast_prod]
    apply Finset.prod_congr rfl
    intro i _
    change (if s i true then -1 else 1) = (signValue (s i) : MvPolynomial _ R)
    rw [signProduct s (hs i)]
    split_ifs <;> norm_num
  · rw [ite_eq_right (ha.not.mpr hs)]
    obtain ⟨i,hi⟩ := not_forall.mp hs
    have hzero : signValue (s i) = 0 := by simp [signValue, not_not.mp hi]
    have hz : pathSign f g.1 g.2.1 g.2.2.1 g.2.2.2 = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ i) hzero
    simp [hz]

/-- The weighted Boolean-sum compiled by the signed-CNF machine is the
actual formal polynomial of the side array. -/
theorem fullFrame_polynomial (R : Type*) [CommRing R] {f : Checkers w left b}
    {addr : CutBit d (2*leastEnergy m) (stateCountAt (d*leastEnergy m)) ↪ Fin p × Fin m}
    (F : CompleteFrame f addr) :
    (∑ r : Raw f → Bool, if F.circuit.eval r none then
      ∏ j, if F.circuit.eval r (some j) then (labelWeights R j).elim X C else 1 else 0) =
      sidePolynomial (binarySideTensor R w addr left b) := by
  classical
  rw [polynomial_signed_paths R f addr,
    ← Finset.sum_subset (Finset.subset_univ (Finset.univ.image (encode f))),
    Finset.sum_image (encode_injective f).injOn]
  · simp only [flag_product, Data, Fintype.sum_prod_type]
  · intro r _ hr
    have miss : r ∉ Set.range (encode f) := by simpa [Set.mem_range] using hr
    exact ite_eq_right (fun h => miss ((legal_iff f r).1 ((F.accepted r).1 h).1))

/-- Each sufficiently long `Pstar n` has a genuine variable/scalar projection
onto the complete side polynomial, over every coefficient ring. -/
theorem projection_at_length (R : Type*) [CommRing R] (f : Checkers w left b)
    (addr : CutBit d (2*leastEnergy m) (stateCountAt (d*leastEnergy m)) ↪ Fin p × Fin m)
    (F : CompleteFrame f addr) (B n : ℕ) (hr : Fintype.card (Raw f) ≤ B)
    (ht : Fintype.card (Labels d p m) ≤ B) (hF : F.circuit.size ≤ B)
    (hn : 100000000000 * (B+1)^6 ≤ n) :
    ∃ φ : Projection R (Fin n × Bool) ((Fin d ⊕ Fin p) × Fin (2^m)),
      φ.hom (MvPolynomial.map (Int.castRingHom R) (Pstar n)) =
        sidePolynomial (binarySideTensor R w addr left b) := by
  obtain ⟨φ,h⟩ := frame_projection_at_length F.circuit none some (labelWeights R) B n hr ht hF hn
  have allInputs : @Finset.univ (Raw f → Bool) (@Pi.instFintype _ _ (fun a b => Classical.propDecidable (a=b))
      (inferInstance : Fintype (Raw f)) (fun _ => Bool.fintype)) = (Finset.univ : Finset (Raw f → Bool)) := by
    ext a
    simp
  rw [allInputs] at h
  exact ⟨φ,h.trans (fullFrame_polynomial R F)⟩

end Crossing.FusionStage

end BorderVNP
end Computability
end OAI
