import OAI.LinearAlgebra.TensorSpectrum.Additive.Finite
import OAI.LinearAlgebra.TensorSpectrum.AdditiveCone.Stable
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Fintype.EquivFin

/-!
# From absence of additive states to an actual catalyst

Finite coordinate bounds and state constraints are encoded by integer vectors.
Their integer cone certificate is evaluated in the stable additive group, so
the final inequality retains the catalyst and requires no cancellation in `S`.
-/

open scoped BigOperators

namespace OAI.LinearAlgebra.TensorSpectrum

open OAI.LinearAlgebra.TensorSpectrum.AdditiveCone

namespace FiniteStateEncoding

variable {S : Type*} [CommSemiring S] [PartialOrder S]

noncomputable def coordinateEquiv (U : Finset S) :=
  Fintype.equivFin {s : S // s ∈ U}

noncomputable def coordinate (U : Finset S)
    (j : Fin (Fintype.card {s : S // s ∈ U})) : S :=
  ((coordinateEquiv U).symm j).val

noncomputable def basis (U : Finset S) (s : S) :
    Fin (Fintype.card {s : S // s ∈ U}) → ℤ := by
  classical
  exact if hs : s ∈ U then Pi.single (coordinateEquiv U ⟨s, hs⟩) 1 else 0

def realEvaluate {n : ℕ} (L : Fin n → ℝ) (z : Fin n → ℤ) : ℝ :=
  ∑ j, (z j : ℝ) * L j

theorem realEvaluate_sub {n : ℕ} (L : Fin n → ℝ) (a b : Fin n → ℤ) :
    realEvaluate L (fun j => a j - b j) = realEvaluate L a - realEvaluate L b := by
  simp [realEvaluate, Int.cast_sub, sub_mul, Finset.sum_sub_distrib]

theorem realEvaluate_scalar {n : ℕ} (L : Fin n → ℝ) (c : ℤ) (a : Fin n → ℤ) :
    realEvaluate L (fun j => c * a j) = (c : ℝ) * realEvaluate L a := by
  simp [realEvaluate, Int.cast_mul, mul_assoc, Finset.mul_sum]

theorem evaluate_sub {G : Type*} [AddCommGroup G] {n : ℕ}
    (v : Fin n → G) (a b : Fin n → ℤ) :
    evaluate v (fun j => a j - b j) = evaluate v a - evaluate v b := by
  simp only [evaluate, sub_eq_add_neg, add_zsmul, neg_zsmul,
    Finset.sum_add_distrib, Finset.sum_neg_distrib]

omit [CommSemiring S] [PartialOrder S] in
theorem evaluate_basis_index {G : Type*} [AddCommGroup G]
    (U : Finset S) (v : Fin (Fintype.card {s : S // s ∈ U}) → G)
    (s : S) (hs : s ∈ U) :
    evaluate v (basis U s) = v (coordinateEquiv U ⟨s, hs⟩) := by
  classical
  rw [basis, dite_eq_left hs]
  unfold evaluate
  rw [Fintype.sum_eq_single (coordinateEquiv U ⟨s, hs⟩),
    Pi.single_eq_same, one_zsmul]
  intro j hj
  rw [Pi.single_eq_of_ne hj, zero_zsmul]

omit [PartialOrder S] in
theorem evaluate_basis (U : Finset S) (s : S) (hs : s ∈ U) :
    evaluate (fun j => StableGroup.embed (coordinate U j)) (basis U s) =
      StableGroup.embed s := by
  rw [evaluate_basis_index U _ s hs]
  simp [coordinate]

omit [PartialOrder S] in
theorem embed_nat_mul (n : ℕ) (s : S) :
    (n : ℤ) • StableGroup.embed s = StableGroup.embed ((n : S) * s) := by
  rw [natCast_zsmul]
  simpa only [nsmul_eq_mul] using ((StableGroup.embed (S := S)).map_nsmul n s).symm

abbrev InequalityIndex (U : Finset S) (F : Finset (StateConstraint S)) :=
  {s : S // s ∈ U} ⊕ ({s : S // s ∈ U} ⊕ {c : StateConstraint S // c ∈ F})

noncomputable def inequality (T : S) (k : ℕ) (R : S → ℕ)
    (U : Finset S) (F : Finset (StateConstraint S)) :
    InequalityIndex U F → Fin (Fintype.card {s : S // s ∈ U}) → ℤ
  | .inl s => basis U s.val
  | .inr (.inl s) => fun j => (R s.val : ℤ) * basis U 1 j - basis U s.val j
  | .inr (.inr c) => match c.val with
    | .order x y _ => fun j => basis U y j - basis U x j
    | .detect s => fun j => basis U (T * s) j - (k : ℤ) * basis U s j
    | _ => 0

noncomputable def relation (U : Finset S) (F : Finset (StateConstraint S)) :
    {c : StateConstraint S // c ∈ F} → Fin (Fintype.card {s : S // s ∈ U}) → ℤ
  | ⟨.zero, _⟩ => basis U 0
  | ⟨.add x y, _⟩ => fun j => basis U (x + y) j - basis U x j - basis U y j
  | _ => 0

def leftElement (U : Finset S) (F : Finset (StateConstraint S)) :
    InequalityIndex U F → S
  | .inl _ => 0
  | .inr (.inl s) => s.val
  | .inr (.inr c) => match c.val with
    | .order x _ _ => x
    | _ => 0

def rightElement (R : S → ℕ) (U : Finset S) (F : Finset (StateConstraint S)) :
    InequalityIndex U F → S
  | .inl s => s.val
  | .inr (.inl s) => (R s.val : S)
  | .inr (.inr c) => match c.val with
    | .order _ y _ => y
    | _ => 0

def detectionElement (U : Finset S) (F : Finset (StateConstraint S)) :
    InequalityIndex U F → S
  | .inr (.inr ⟨.detect s, _⟩) => s
  | _ => 0

theorem left_le_right (R : S → ℕ) (U : Finset S) (F : Finset (StateConstraint S))
    (hzero : ∀ s : S, 0 ≤ s) (hR : ∀ s : S, s ≤ (R s : S)) :
    ∀ i, leftElement U F i ≤ rightElement R U F i := by
  rintro (s | (s | ⟨c, hc⟩))
  · exact hzero s.val
  · exact hR s.val
  · cases c <;> simp only [leftElement, rightElement, le_refl]
    assumption

theorem inequality_evaluate (T : S) (k : ℕ) (R : S → ℕ)
    (U : Finset S) (F : Finset (StateConstraint S)) (h1 : 1 ∈ U)
    (hcoords : ∀ c ∈ F, c.coordinates T ⊆ U) :
    ∀ i, evaluate (fun j => StableGroup.embed (coordinate U j))
        (inequality T k R U F i) =
      (StableGroup.embed (rightElement R U F i) -
        StableGroup.embed (leftElement U F i)) +
      (StableGroup.embed (T * detectionElement U F i) -
        StableGroup.embed ((k : S) * detectionElement U F i)) := by
  rintro (s | (s | ⟨c, hc⟩))
  · simpa only [inequality, rightElement, leftElement, detectionElement,
      mul_zero, map_zero, sub_zero, sub_self, add_zero] using evaluate_basis U s.val s.property
  · simp only [inequality, rightElement, leftElement, detectionElement,
      evaluate_sub, evaluate_scalar, evaluate_basis U 1 h1,
      evaluate_basis U s.val s.property, embed_nat_mul, mul_one,
      mul_zero, map_zero, sub_self, add_zero]
  · cases c with
    | zero => simp [inequality, rightElement, leftElement, detectionElement, evaluate]
    | one => simp [inequality, rightElement, leftElement, detectionElement, evaluate]
    | add x y => simp [inequality, rightElement, leftElement, detectionElement, evaluate]
    | order x y hxy =>
      have hx : x ∈ U := hcoords (.order x y hxy) hc (by simp [StateConstraint.coordinates])
      have hy : y ∈ U := hcoords (.order x y hxy) hc (by simp [StateConstraint.coordinates])
      simp only [inequality, rightElement, leftElement, detectionElement,
        evaluate_sub, evaluate_basis U x hx, evaluate_basis U y hy,
        mul_zero, map_zero, sub_self, add_zero]
    | detect s =>
      have hs : s ∈ U := hcoords (.detect s) hc (by simp [StateConstraint.coordinates])
      have hTs : T * s ∈ U := hcoords (.detect s) hc (by simp [StateConstraint.coordinates])
      simp only [inequality, rightElement, leftElement, detectionElement,
        evaluate_sub, evaluate_scalar, evaluate_basis U s hs,
        evaluate_basis U (T * s) hTs, embed_nat_mul, map_zero, sub_self, zero_add]

theorem relation_evaluate (T : S) (U : Finset S) (F : Finset (StateConstraint S))
    (h0 : 0 ∈ U) (hcoords : ∀ c ∈ F, c.coordinates T ⊆ U) :
    ∀ c, evaluate (fun j => StableGroup.embed (coordinate U j)) (relation U F c) = 0 := by
  rintro ⟨c, hc⟩
  cases c with
  | zero => simpa only [relation, map_zero] using evaluate_basis U 0 h0
  | one => simp [relation, evaluate]
  | add x y =>
    have hx : x ∈ U := hcoords (.add x y) hc (by simp [StateConstraint.coordinates])
    have hy : y ∈ U := hcoords (.add x y) hc (by simp [StateConstraint.coordinates])
    have hxy : x + y ∈ U := hcoords (.add x y) hc (by simp [StateConstraint.coordinates])
    simp only [relation, evaluate_sub, evaluate_basis U x hx,
      evaluate_basis U y hy, evaluate_basis U (x + y) hxy]
    rw [(StableGroup.embed (S := S)).map_add x y]
    abel
  | order x y hxy => simp [relation, evaluate]
  | detect s => simp [relation, evaluate]

theorem no_normalized_functional (T : S) (k : ℕ) (R : S → ℕ)
    (U : Finset S) (F : Finset (StateConstraint S))
    (hinconsistent : ¬ ∃ f : S → ℝ,
      (∀ s ∈ U, f s ∈ Set.Icc 0 (R s : ℝ)) ∧ ∀ c ∈ F, c.Holds T k f) :
    ¬ ∃ L : Fin (Fintype.card {s : S // s ∈ U}) → ℝ,
      realEvaluate L (basis U 1) = 1 ∧
      (∀ i, 0 ≤ realEvaluate L (inequality T k R U F i)) ∧
      (∀ c, realEvaluate L (relation U F c) = 0) := by
  rintro ⟨L, hunit, hineq, hrel⟩
  let f : S → ℝ := fun s => realEvaluate L (basis U s)
  apply hinconsistent
  refine ⟨f, ?_, ?_⟩
  · intro s hs
    have hlo := hineq (.inl ⟨s, hs⟩)
    have hhi := hineq (.inr (.inl ⟨s, hs⟩))
    change 0 ≤ f s at hlo
    change 0 ≤ realEvaluate L (fun j => (R s : ℤ) * basis U 1 j - basis U s j) at hhi
    rw [realEvaluate_sub, realEvaluate_scalar, hunit] at hhi
    simp only [Int.cast_natCast, mul_one] at hhi
    exact ⟨hlo, by change f s ≤ (R s : ℝ); change 0 ≤ (R s : ℝ) - f s at hhi; linarith⟩
  · intro c hc
    cases c with
    | zero => exact hrel ⟨.zero, hc⟩
    | one => exact hunit
    | add x y =>
      have h := hrel ⟨.add x y, hc⟩
      change realEvaluate L (fun j => basis U (x + y) j - basis U x j - basis U y j) = 0 at h
      rw [realEvaluate_sub, realEvaluate_sub] at h
      change f (x + y) - f x - f y = 0 at h
      change f (x + y) = f x + f y
      linarith
    | order x y hxy =>
      have h := hineq (.inr (.inr ⟨.order x y hxy, hc⟩))
      change 0 ≤ realEvaluate L (fun j => basis U y j - basis U x j) at h
      rw [realEvaluate_sub] at h
      change 0 ≤ f y - f x at h
      change f x ≤ f y
      linarith
    | detect s =>
      have h := hineq (.inr (.inr ⟨.detect s, hc⟩))
      change 0 ≤ realEvaluate L (fun j => basis U (T * s) j - (k : ℤ) * basis U s j) at h
      rw [realEvaluate_sub, realEvaluate_scalar] at h
      simp only [Int.cast_natCast] at h
      change 0 ≤ f (T * s) - (k : ℝ) * f s at h
      change (k : ℝ) * f s ≤ f (T * s)
      linarith

end FiniteStateEncoding

variable {S : Type*} [CommSemiring S] [PartialOrder S]

/-- Failure of the normalized additive monotone state space produces a genuine
strict positive integer gain with one catalyst. All finite encoding and cone
steps are proved from the given semiring and order hypotheses. -/
theorem catalyst_of_no_state (T : S) (k : ℕ) (R : S → ℕ)
    (hadd : ∀ a b c : S, a ≤ b → a + c ≤ b + c)
    (hzero : ∀ s : S, 0 ≤ s) (hR : ∀ s : S, s ≤ (R s : S))
    (hnone : stateSet T k = ∅) :
    ∃ m : ℕ, 0 < m ∧ ∃ D s : S, D + (m : S) + T * s ≤ D + (k : S) * s := by
  classical
  obtain ⟨F, U, h0, h1, hcoords, hbad⟩ := finite_coordinate_obstruction T k R hnone
  let g := FiniteStateEncoding.inequality T k R U F
  let r := FiniteStateEncoding.relation U F
  let unit := FiniteStateEncoding.basis U (1 : S)
  obtain ⟨m, hm, c, d, hc, hcertificate⟩ :=
    integer_cone_certificate_of_no_state g r unit
      (FiniteStateEncoding.no_normalized_functional T k R U F hbad)
  have hmNat : 0 < m.toNat := by omega
  have hmCast : (m.toNat : ℤ) = m := Int.toNat_of_nonneg (le_of_lt hm)
  obtain ⟨X, Y, s, hXY, hstable⟩ := stable_certificate_of_integer_cone hadd
    (FiniteStateEncoding.coordinate U) g r unit m.toNat k T c d hc
    (FiniteStateEncoding.leftElement U F) (FiniteStateEncoding.rightElement R U F)
    (FiniteStateEncoding.detectionElement U F)
    (FiniteStateEncoding.left_le_right R U F hzero hR)
    (FiniteStateEncoding.evaluate_basis U 1 h1)
    (FiniteStateEncoding.inequality_evaluate T k R U F h1 hcoords)
    (FiniteStateEncoding.relation_evaluate T U F h0 hcoords)
    (by simpa only [hmCast] using hcertificate)
  obtain ⟨D, hD⟩ := stable_certificate_to_catalyst hadd hXY hstable
  exact ⟨m.toNat, hmNat, D, s, hD⟩

end OAI.LinearAlgebra.TensorSpectrum
