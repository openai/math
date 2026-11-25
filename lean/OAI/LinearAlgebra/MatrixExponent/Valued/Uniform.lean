import OAI.LinearAlgebra.MatrixExponent.Valued.StarWeights
import OAI.LinearAlgebra.MatrixExponent.Prices.Tensor
import OAI.LinearAlgebra.MatrixExponent.Spectral.Place
import OAI.LinearAlgebra.MatrixExponent.Prices.Sync
import Mathlib.Order.Filter.Cocardinal
import OAI.LinearAlgebra.MatrixExponent.Prices.Motion.Rigidity

/-!
# A discounted state

Integer thresholds suffice even for rational valuations. Summing the
filtered envelopes with geometric weights gives a positive additive
functional. After taking a character, powers recover rational shifts.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued
open Spectral

variable {E K S : Type} [Field E] [Field K] [Algebra E K] [Infinite E]
    [Fintype S] [Nonempty S]

theorem weighted_state (v : AddValuation K (WithTop ℚ)) (hv : constants E K ≤ integralRing v)
    (f : Tensor E S →+* ℝ) (hf : Monotone f) (b : ℝ) (hb : 0 < b) :
    ∃ M : ITensor (constants E K) S →+ ℝ, Monotone M ∧ 0 < M 1 ∧
      (∀ A B, M (ITensor.fromBase le_rfl A * B) = f A * M B) ∧
      ∀ (c : K) (m : ℤ), (↑(m : ℚ) : WithTop ℚ) ≤ v c →
        ∀ B, M (ITensor.scalar _ _ c * B) ≤ Real.exp (-(m : ℝ) * b) * M B := by
  let T := ITensor (constants E K) S
  let L (A : T) (n : ℤ) := Real.exp (-(n : ℝ) * b) * best f (cutoff v E n) A
  have hp (A : T) (n : ℤ) : 0 ≤ L A n :=
    mul_nonneg (Real.exp_pos _).le (best_nonneg f hf _ _)
  have sum (A : T) : Summable (L A) := by
    apply summable_int_iff_summable_nat_and_neg.mpr
    constructor
    · obtain ⟨C, hC⟩ := sample_bounded f hf A
      have hg := summable_geometric_of_lt_one (Real.exp_pos (-b)).le
        (Real.exp_lt_one_iff.mpr (neg_neg_of_pos hb))
      refine Summable.of_nonneg_of_le (fun n => hp _ _) ?_ (hg.mul_right C)
      intro n
      unfold L
      rw [Int.cast_natCast, neg_mul, ← mul_neg, Real.exp_nat_mul]
      exact mul_le_mul_of_nonneg_left (best_le _ _ _ (fun l _ => hC l)) (by positivity)
    · obtain ⟨m, hm⟩ := best_floor v f hf A
      apply (summable_nat_add_iff (m + 1)).mp
      have e : ∀ n : ℕ, L A (-(↑(n + (m + 1)) : ℤ)) = 0 := by
        intro n
        unfold L
        rw [hm _ (by push_cast; linarith), mul_zero]
      simpa only [e] using (summable_zero : Summable (fun _ : ℕ => (0 : ℝ)))
  let M : T →+ ℝ :=
    { toFun := fun A => ∑' n, L A n
      map_zero' := by simp [L, best_zero f hf]
      map_add' := fun A B => by
        rw [← (sum A).tsum_add (sum B)]
        exact tsum_congr fun n => by unfold L; rw [best_add f hf, mul_add] }
  refine ⟨M, ?_, ?_, ?_, ?_⟩
  · intro A B h
    exact Summable.tsum_le_tsum (fun n => mul_le_mul_of_nonneg_left (best_mono f hf _ h)
      (Real.exp_pos _).le) (sum A) (sum B)
  · have h : 0 < L 1 0 := by simpa [L] using best_unit v f hf hv
    exact h.trans_le ((sum _).le_tsum 0 fun n _ => hp _ n)
  · intro A B
    change (∑' n, L _ n) = _ * ∑' n, L _ n
    rw [← tsum_mul_left]
    exact tsum_congr fun n => by unfold L; rw [best_mul f hf, mul_left_comm]
  · intro c m hc B
    let A := ITensor.scalar (constants E K) S c * B
    change (∑' n, L A n) ≤ _ * ∑' n, L B n
    rw [← (Equiv.addRight m).tsum_eq (L A), ← tsum_mul_left]
    refine Summable.tsum_le_tsum (fun n => ?_)
      ((sum A).comp_injective (Equiv.addRight m).injective) ((sum B).mul_left _)
    change L A (n + m) ≤ _ * L B n
    unfold L
    have h := best_shift v f hf (s := ↑(n + m)) c hc B
    rw [Int.cast_add, add_sub_cancel_right] at h
    rw [Int.cast_add, Int.cast_add, neg_add_rev, add_mul, Real.exp_add, ← mul_assoc]
    exact mul_le_mul_of_nonneg_left h (by positivity)

end OAI.LinearAlgebra.MatrixExponent.Valued
end

/-! # A multiplicative lift with valuation bounds -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued
open Spectral Prices

variable {E K S : Type} [Field E] [Field K] [Algebra E K] [Infinite E]
    [Fintype S] [Nonempty S]

private theorem stable_sum {T I : Type*} [CommSemiring T] (M : T →+ ℝ) (A : I → T) (r : I → ℝ)
    (hr : ∀ i, StableLE M (A i) 1 (r i)) (u : Finset I) :
    StableLE M (∑ i ∈ u, A i) 1 (∑ i ∈ u, r i) := by
  intro x
  rw [Finset.sum_mul, map_sum, Finset.sum_mul]
  exact Finset.sum_le_sum (fun i _ => hr i x)

private theorem stable_nat {T : Type*} [CommSemiring T] (M : T →+ ℝ) {A : T} {r : ℝ}
    (h : StableLE M A 1 r) (n : ℕ) : StableLE M (A * n) 1 (n * r) := by
  intro x
  rw [mul_comm A, mul_assoc, ← nsmul_eq_mul, map_nsmul, nsmul_eq_mul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (h x) (Nat.cast_nonneg n)

theorem weighted_character (v : AddValuation K (WithTop ℚ)) (hv : constants E K ≤ integralRing v)
    (f : Tensor E S →+* ℝ) (hf : Monotone f) (b : ℝ) (hb : 0 < b) :
    ∃ g : ITensor (constants E K) S →+* ℝ, Monotone g ∧
      (∀ A, g (ITensor.fromBase le_rfl A) = f A) ∧
      ∀ (c : K) (m : ℤ), (↑(m : ℚ) : WithTop ℚ) ≤ v c →
        g (ITensor.scalar _ _ c) ≤ Real.exp (-(m : ℝ) * b) := by
  classical
  let O := constants E K
  let T := ITensor O S
  obtain ⟨M, hm, h1, hf', hM⟩ := weighted_state v hv f hf b hb
  have hs (c : K) : ∃ r ≥ 0, StableLE M (ITensor.scalar O S c) 1 r := by
    obtain ⟨n, hn⟩ := exists_floor v c
    have h := hM c (-n) (by simpa using hn)
    exact ⟨_, (Real.exp_pos _).le, fun x => by rw [one_mul]; exact h x⟩
  have mono (x y : T) (h : x ≤ y) (u : T) : M (x * u) ≤ M (y * u) := by
    rw [mul_comm x, mul_comm y]
    exact hm (ITensor.mul_le_mul_left _ _ _ h)
  have lower (A : T) : A ≠ 0 → ∃ c, StableLE M 1 A c := by
    refine Quotient.inductionOn A fun a ha => ?_
    obtain ⟨x, hx⟩ := not_forall.mp fun he => ha ((ITensor.ofRaw_eq_zero a).mpr he)
    obtain ⟨r, hr, h⟩ := hs (a.coeff x)⁻¹
    refine ⟨r, fun u => ?_⟩
    have e := h (ITensor.scalar O S (a.coeff x) * u)
    rw [← mul_assoc, ← ITensor.scalar_mul, inv_mul_cancel₀ hx, ITensor.scalar_one, one_mul, one_mul] at e
    rw [one_mul]
    exact e.trans (mul_le_mul_of_nonneg_left (mono _ _ (ITensor.scalar_coeff a x) _) hr)
  have upper (A : T) : ∃ c ≥ 0, StableLE M A 1 c := by
    refine Quotient.inductionOn A fun a => ?_
    let L (i : ∀ s, a.leg s) := ITensor.scalar O S (a.coeff i)
    let B := ∑ i, L i
    have hb (i : ∀ s, a.leg s) : L i ≤ B := by
      unfold B
      rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      simpa only [zero_add] using ITensor.add_le_add_right _ _ (L i)
        (ITensor.zero_le (∑ j ∈ Finset.univ.erase i, L j))
    obtain ⟨n, hn⟩ := ITensor.table_bound O a.leg a.coeff B hb
    rw [ITensor.table_coeff] at hn
    choose r hr h using fun i => hs (a.coeff i)
    have h' := stable_nat M (stable_sum M L r h Finset.univ) n
    exact ⟨_, mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun i _ => hr i),
      fun u => (mono _ _ hn u).trans (h' u)⟩
  have test : ProductBound (fun _ : Empty => (1 : T)) (fun _ => (1 : ℝ)) M := by
    refine ⟨M 1, fun w => ?_⟩
    cases w with
    | nil => simp
    | cons i _ => exact i.elim
  obtain ⟨g, hg, _, h⟩ := character_of_products ITensor.mul_le_mul_left ITensor.zero_le
    (fun _ => zero_le_one) M hm h1 test lower upper
  refine ⟨g, hg, ?_, ?_⟩
  · intro A
    let X := ITensor.fromBase (show constants E K ≤ O from le_rfl) A
    have e : ∀ y, M (X * y) = f A * M y := hf' A
    apply le_antisymm
    · simpa only [map_one, mul_one] using h X 1 (f A) (fun u => by rw [one_mul, e])
    · rcases le_or_gt (f A) 0 with hn | hn
      · exact hn.trans (by rw [← map_zero g]; exact hg (ITensor.zero_le _))
      · have hl := h 1 X (f A)⁻¹ (fun u => by rw [one_mul, e, inv_mul_cancel_left₀ hn.ne'])
        rwa [map_one, le_inv_mul_iff₀ hn, mul_one] at hl
  · intro c m hc
    simpa only [map_one, mul_one] using h (ITensor.scalar O S c) 1 (Real.exp (-(m : ℝ) * b))
      (fun u => by rw [one_mul]; exact hM c m hc u)

end OAI.LinearAlgebra.MatrixExponent.Valued
end

/-!
# Integral restriction by scalar interpolation

In a uniform inequality for tensors polynomial in each of finitely
many scalars, integral scalars may replace constants one at a time.
Apply this to the entries of the local restriction matrices.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
open Spectral

variable {E K S : Type} [Field E] [Field K] [Algebra E K] [Infinite E]
    [Fintype S] [Nonempty S] {O V : Subring K}

theorem of_polynomial (X : S → Type) [∀ s, Fintype (X s)]
    (P : (∀ s, X s) → Polynomial K) :
    ∃ d, Family (fun a => table O X (fun x => (P x).eval a)) d := by
  classical
  obtain ⟨d, hd⟩ := (Set.finite_range (fun x => (P x).natDegree)).bddAbove
  exact ⟨d, X, inferInstance, P, fun x => hd ⟨x, rfl⟩, fun _ => rfl⟩

theorem Family.bound_constants {A : K → ITensor O S} {d : ℕ} (h : Family A d)
    (f : ITensor O S →+* ℝ) (hf : Monotone f) (hV : ∀ c ∈ V, f (scalar O S c) ≤ 1)
    (hv : constants E K ≤ V) {r : ℝ} (hr : ∀ a ∈ constants E K, f (A a) ≤ r)
    (c : K) (hc : c ∈ V) : f (A c) ≤ r := by
  let φ := algebraMap E K
  have hi (t : E) : φ t ∈ constants E K := ⟨t, rfl⟩
  refine h.bound_scalar f hf hV φ φ.injective (fun i => hv (hi i)) ?_ (fun i => hr _ (hi i)) c hc
  intro i j
  rw [← map_sub, ← map_inv₀]
  exact hv (hi _)

theorem bound_grid {I : Type} [Fintype I] [DecidableEq I] (A : (I → K) → ITensor O S)
    (ha : ∀ x i, ∃ d, Family (fun c => A (Function.update x i c)) d)
    (f : ITensor O S →+* ℝ) (hf : Monotone f) (hV : ∀ c ∈ V, f (scalar O S c) ≤ 1)
    (hv : constants E K ≤ V) {r : ℝ} (hr : ∀ x, (∀ i, x i ∈ constants E K) → f (A x) ≤ r)
    (x : I → K) (hx : ∀ i, x i ∈ V) : f (A x) ≤ r := by
  have H (t : Finset I) (y : I → K) (hy : ∀ i, y i ∈ V)
      (hg : ∀ i ∉ t, y i ∈ constants E K) : f (A y) ≤ r := by
    induction t using Finset.induction_on generalizing y with
    | empty => exact hr y fun i => hg i (by simp)
    | @insert i t _ ih =>
      obtain ⟨_, hi⟩ := ha y i
      have hb (c : K) (hc : c ∈ constants E K) : f (A (Function.update y i c)) ≤ r := by
        apply ih
        · intro j
          by_cases h : j = i
          · simpa [h] using hv hc
          · simpa [Function.update_of_ne h] using hy j
        · intro j hj
          by_cases h : j = i
          · simpa [h] using hc
          · simpa [Function.update_of_ne h] using hg j (by simp [hj, h])
      simpa using hi.bound_constants f hf hV hv hb (y i) (hy i)
  exact H Finset.univ x hx fun _ h => (h (Finset.mem_univ _)).elim

theorem integral_mono (f : ITensor (constants E K) S →+* ℝ) (hf : Monotone f)
    (hv : constants E K ≤ V) (hs : ∀ c ∈ V, f (scalar _ _ c) ≤ 1)
    {A B : Raw K S} (h : Restricts V A B) : f (ofRaw B) ≤ f (ofRaw A) := by
  classical
  let I := Σ s, B.leg s × A.leg s
  let X (l : I → K) := table (constants E K) B.leg
    (fun x => ∑ i : A.term, ∏ s, ∑ y, l ⟨s, x s, y⟩ * A.factor i s y)
  have hp (l : I → K) (j : I) : ∃ d, Family (fun c => X (Function.update l j c)) d := by
    let L (i : I) := if i = j then Polynomial.X else Polynomial.C (l i)
    have e (i : I) (c : K) : (L i).eval c = Function.update l j c i := by
      by_cases h : i = j <;> simp [L, h]
    let P (x : ∀ s, B.leg s) :=
      ∑ i : A.term, ∏ s, ∑ y, L ⟨s, x s, y⟩ * Polynomial.C (A.factor i s y)
    obtain ⟨d, hd⟩ := of_polynomial (O := constants E K) B.leg P
    refine ⟨d, ?_⟩
    simpa only [P, Polynomial.eval_finsetSum, Polynomial.eval_prod, Polynomial.eval_mul,
      Polynomial.eval_C, e] using hd
  have hr (l : I → K) (hl : ∀ i, l i ∈ constants E K) : f (X l) ≤ f (ofRaw A) := by
    apply hf
    refine ⟨fun s x y => l ⟨s, x, y⟩, fun _ _ _ => hl _, fun x => ?_⟩
    exact Raw.coeff_ofTable _ _ _
  obtain ⟨L, hL, he⟩ := h
  let l (i : I) := L i.1 i.2.1 i.2.2
  have hh := bound_grid X hp f hf hs hv hr l (fun i => hL _ _ _)
  have e : X l = ofRaw B := by
    unfold X l
    rw [← table_coeff (constants E K) B]
    exact congrArg _ (funext he).symm
  rwa [e] at hh

end OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
end

/-!
# Integral restrictions and change of sites

A surjective grouping preserves sums. Arbitrary placements also allow
unused sites and preserve products, scalar weights and base-field tensors.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
open Spectral

variable {K S T R : Type} [Field K] {O : Subring K}
  [Fintype S] [Fintype T] [Fintype R] [DecidableEq S] [DecidableEq T] [DecidableEq R]

def place (f : T → S) : ITensor O T → ITensor O S :=
  Quotient.map (Raw.group f) fun _ _ h => ⟨h.1.group f, h.2.group f⟩

theorem place_ofRaw (f : T → S) (A : Raw K T) :
    place f (ofRaw (O := O) A) = ofRaw (A.group f) := rfl

theorem place_mono (f : T → S) : Monotone (place (O := O) f) :=
  fun A B => Quotient.inductionOn₂ A B fun _ _ h => Restricts.group h f

theorem place_zero (f : T → S) : place f (0 : ITensor O T) = 0 :=
  ofRaw_eq (Raw.integral_group_zero f)

theorem place_one (f : T → S) : place f (1 : ITensor O T) = 1 :=
  ofRaw_eq (Raw.integral_group_one f)

theorem place_mul (f : T → S) (A B : ITensor O T) :
    place f (A * B) = place f A * place f B :=
  Quotient.inductionOn₂ A B fun a b => ofRaw_eq (Raw.integral_group_mul f a b)

theorem place_id (A : ITensor O S) : place id A = A :=
  Quotient.inductionOn A fun a => ofRaw_eq (Raw.integral_group_id a)

theorem place_comp (f : T → S) (g : R → T) (A : ITensor O R) :
    place (f ∘ g) A = place f (place g A) :=
  Quotient.inductionOn A fun a => ofRaw_eq (Raw.integral_group_comp f g a)

theorem place_inl [Nonempty S] (A : ITensor O S) :
    place (Sum.inl : S → S ⊕ T) A = pad T A :=
  Quotient.inductionOn A fun a => ofRaw_eq (Raw.integral_group_inl a)

def group (f : T → S) (hf : Function.Surjective f) : ITensor O T →+* ITensor O S where
  toFun := place f
  map_zero' := place_zero f
  map_one' := place_one f
  map_mul' := place_mul f
  map_add' A B := Quotient.inductionOn₂ A B fun a b => ofRaw_eq (Raw.integral_group_add f hf a b)

theorem place_eq_group (f : T → S) (hf : Function.Surjective f) (A : ITensor O T) :
    place f A = group f hf A := rfl

theorem group_mono (f : T → S) (hf : Function.Surjective f) :
    Monotone (group (O := O) f hf) := place_mono f

theorem group_pad [Nonempty S] (f : S ⊕ T → S) (hf : Function.Surjective f)
    (h : ∀ s, f (.inl s) = s) (A : ITensor O S) :
    group f hf (pad T A) = A := by
  rw [← place_eq_group, ← place_inl, ← place_comp, show f ∘ Sum.inl = id from funext h, place_id]

theorem place_add_le [Nonempty T] (f : T → S) (A B : ITensor O T) :
    place f (A + B) ≤ place f A + place f B := by
  let g : T ⊕ S → S := Sum.elim f id
  have hg : Function.Surjective g := fun s => ⟨.inr s, rfl⟩
  have he (X : ITensor O T) : place f X = group g hg (pad S X) := by
    rw [← place_eq_group, ← place_inl, ← place_comp]
    rfl
  rw [he, he, he, ← (group g hg).map_add]
  exact group_mono g hg ((padding S).add_le A B)

theorem place_scalar [Nonempty S] [Nonempty T] (f : T → S) (c : K) :
    place f (scalar O T c) = scalar O S c := by
  apply ofRaw_eq
  refine equiv_coeff (fun s => Equiv.ofUnique (Raw.Fiber f s → Unit) Unit) fun x => ?_
  erw [Raw.coeff_group, Raw.coeff_ofTable, Raw.coeff_ofTable]

variable {E : Type} [Field E] [Algebra E K] (hO : constants E K ≤ O)

theorem place_fromBase (f : T → S) (A : Tensor E T) :
    place f (fromBase hO A) = fromBase hO (Tensor.place f A) := by
  refine Quotient.inductionOn A fun a => ofRaw_eq ?_
  refine relabel (Equiv.refl _) (fun _ => Equiv.refl _) fun i s x => ?_
  exact (map_prod (algebraMap E K) _ _).symm

abbrev wire (a b : S) (n : ℕ) : ITensor O S := fromBase hO (Tensor.wire E a b n)

theorem place_wire (f : T → S) (a b : T) (n : ℕ) :
    place f (wire hO a b n) = wire hO (f a) (f b) n := by
  simp only [wire, place_fromBase, Tensor.place_wire]

theorem wire_ofRaw (a b : S) (n : ℕ) :
    wire hO a b n = ofRaw (Raw.wire K a b n) := by
  apply ofRaw_eq
  refine relabel (Equiv.refl _) (fun _ => Equiv.refl _) fun i s x => ?_
  change Fin n at i x
  change algebraMap E K (if x = Raw.port {a, b} s i then 1 else 0) =
    if x = Raw.port {a, b} s i then 1 else 0
  split <;> simp

end OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
end

/-!
# Constant tests suffice for a lifted price

A restriction to an old-site tensor uses finitely many matrix entries.
Power interpolation bounds its value at integral entries by the uniform
bound at constant entries, even if the old tensor itself varies.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
open Spectral Prices

variable {E K S U : Type} [Field E] [Field K] [Algebra E K]
  [Fintype S] [Nonempty S] [Fintype U] {O : Subring K} (hv : constants E K ≤ O)

theorem fromBase_table (X : S → Type) [∀ s, Fintype (X s)] (u : (∀ s, X s) → E) :
    fromBase hv (Tensor.ofRaw (Raw.ofTable X u)) = table O X (fun x => algebraMap E K (u x)) := by
  apply ofRaw_eq
  refine equiv_coeff (fun _ => Equiv.refl _) fun x => ?_
  erw [Raw.coeff_map, Raw.coeff_ofTable, Raw.coeff_ofTable]
  rfl

variable [Infinite E] (f : Tensor E S →+* ℝ) (g : ITensor O S →+* ℝ)
    (hg : Monotone g) (he : ∀ A, g (fromBase hv A) = f A)
include hg he

theorem lift_test (A : Tensor E (S ⊕ U)) {r : ℝ}
    (h : ∀ B, Tensor.pad U B ≤ A → f B ≤ r)
    (B : ITensor O S) (hB : pad U B ≤ fromBase hv A) : g B ≤ r := by
  classical
  revert h hB
  refine Quotient.inductionOn₂ A B fun a b h hB => ?_
  let φ := algebraMap E K
  let I := Σ s, (Raw.pad U b).leg s × a.leg s
  let w (x : ∀ s, b.leg s) : ∀ s, (Raw.pad U b).leg s := Sum.rec x (fun _ => ())
  let X (l : I → K) := table O b.leg
    (fun x => ∑ i : a.term, ∏ s, ∑ y, l ⟨s, w x s, y⟩ * φ (a.factor i s y))
  have hp (l : I → K) (j : I) : ∃ d, Family (fun c => X (Function.update l j c)) d := by
    let L (i : I) := if i = j then Polynomial.X else Polynomial.C (l i)
    have e (i : I) (c : K) : (L i).eval c = Function.update l j c i := by
      by_cases h : i = j <;> simp [L, h]
    let P (x : ∀ s, b.leg s) :=
      ∑ i : a.term, ∏ s, ∑ y, L ⟨s, w x s, y⟩ * Polynomial.C (φ (a.factor i s y))
    obtain ⟨d, hd⟩ := of_polynomial (O := O) b.leg P
    refine ⟨d, ?_⟩
    simpa only [P, Polynomial.eval_finsetSum, Polynomial.eval_prod, Polynomial.eval_mul,
      Polynomial.eval_C, e] using hd
  have hr (l : I → K) (hl : ∀ i, l i ∈ constants E K) : g (X l) ≤ r := by
    choose v ev using hl
    let F (x : ∀ s, b.leg s) := ∑ i : a.term, ∏ s, ∑ y, v ⟨s, w x s, y⟩ * a.factor i s y
    let C := Raw.ofTable b.leg F
    have e : X l = fromBase hv (Tensor.ofRaw C) := by
      rw [show C = Raw.ofTable _ F from rfl, fromBase_table]
      unfold X F
      simp only [map_sum, map_prod, map_mul, ev]
      rfl
    rw [e, he]
    apply h
    refine ⟨fun s x y => v ⟨s, x, y⟩, fun x => ?_⟩
    erw [Raw.pad_coeff, Raw.coeff_ofTable]
    have hx : w (fun s => x (.inl s)) = x := by funext j; cases j <;> rfl
    unfold F
    rw [hx]
  obtain ⟨L, hi, hL⟩ := hB
  let l (i : I) := L i.1 i.2.1 i.2.2
  have hz := bound_grid X hp g hg (fun c hc => by simpa using hg (scalar_le_one O c hc)) hv hr
    l (fun i => hi _ _ _)
  have e : X l = ofRaw b := by
    rw [← table_coeff O b]
    unfold X
    apply congrArg
    funext x
    have H := hL (w x)
    rw [Raw.pad_coeff] at H
    exact H.symm
  rw [e] at hz
  exact hz

theorem lift_assisted (hf : Monotone f) (A : Tensor E (S ⊕ U)) :
    assisted (pad U) g (fromBase hv A) ≤ Tensor.assisted f A := by
  obtain ⟨k, hk, ek, ea⟩ := (Tensor.assisted_minimum f hf A).1
  refine ((extensionData g hg).test_iff _ _).mpr fun n B hB => ?_
  rw [← map_pow] at hB
  refine lift_test hv f g hg he _ ?_ B hB
  intro C hC
  rw [← ea, ← map_pow, ← ek]
  exact hk hC

end OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
end

/-! A submean bound on a valuation star by one Lagrange interpolation. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.ITensor

open Prices Motion K0 Finset
open scoped Classical

variable {E S U : Type} [Field E] [Fintype S] [Nonempty S] [Fintype U]


theorem scalar_bound {K : Type} [Field K] {v : AddValuation K (WithTop ℚ)}
    {W : Subring K} (f : ITensor W S →+* ℝ)
    (hscalar : ∀ (z : K) (q : ℚ), v z = ↑q → f (scalar W S z) = Real.exp (-(q : ℝ)))
    {z : K} {q : ℚ} (hz : ↑q ≤ v z) :
    f (scalar W S z) ≤ Real.exp (-(q : ℝ)) := by
  by_cases h : z = 0
  · rw [h, show scalar W S 0 = 0 from (ofRaw_eq_zero _).mpr (fun y => Spectral.Raw.coeff_ofTable _ _ y),
      map_zero]
    positivity
  obtain ⟨p, hp⟩ := WithTop.ne_top_iff_exists.mp ((v).ne_top_iff.mpr h)
  rw [hscalar z p hp.symm, Real.exp_le_exp]
  exact neg_le_neg (Rat.cast_le.mpr (WithTop.coe_le_coe.mp (hz.trans_eq hp.symm)))

variable {A : K0 E → ITensor (integralRing (K0.val E)) (S ⊕ U)} {d : ℕ}

/-- Bounds at the arm ends imply an upper bound at every integral
parameter. Lengths weight the logarithmic prices by their reciprocals. -/
theorem Family.assisted_star [Infinite E] (h : Family A d) (f : ITensor (integralRing (K0.val E)) S →+* ℝ)
    (hf : Monotone f)
    (hscalar : ∀ (z : K0 E) (q : ℚ), val E z = ↑q → f (scalar (integralRing (K0.val E)) S z) = Real.exp (-(q : ℝ)))
    {n : ℕ} (c : Fin n → K0 E) (hc : ∀ j, 0 ≤ val E (c j))
    (hd : ∀ i j, i ≠ j → val E (c i - c j) = 0)
    (r : Option (Fin n) → ℚ) (hr : ∀ j, 0 < r j) (R : Option (Fin n) → ℝ)
    (hR : ∀ j y, 0 ≤ val E y → assisted (pad U) f (A (armEnd c r y j)) ≤ Real.exp (R j))
    (μ : ℝ) (hμ : 0 ≤ ∑ j, (μ - R j) / (r j : ℝ))
    (x : K0 E) (hx : 0 ≤ val E x) : assisted (pad U) f (A x) ≤ Real.exp μ := by
  let v := (Set.finite_singleton (0 : E)).infinite_compl.natEmbedding _
  let D : Star.Data E n := ⟨c, hc, hd, r, hr, v.trans (Function.Embedding.subtype _),
    fun i => (v i).2⟩
  let H := extensionData (U := U) f hf
  obtain ⟨C, hC, hb⟩ := Star.linear_size D R μ d
  refine H.test_with_loss _ (Real.exp_nonneg _) hC fun N _ s hs => ?_
  let I := Star.Index (Star.size D R μ d N)
  let w : I → K0 E := Star.node D
  refine (h.test_nodes f hf N x hs w (Star.injective D) (Star.sufficient D R μ d N)).trans ?_
  calc
    _ ≤ ∑ _i : I, Real.exp μ ^ N := by
      refine sum_le_sum fun i _ => ?_
      have ha : assisted (pad U) f (A (w i)) ≤ Real.exp (R i.1) :=
        hR _ _ (by rw [val_C (D.hu _)])
      have hp := H.aided_nonneg (A (w i))
      have hl := scalar_bound f hscalar (Star.lagrange_bound D i hx)
      refine (mul_le_mul hl (pow_le_pow_left₀ hp ha N) (pow_nonneg hp _) (Real.exp_nonneg _)).trans ?_
      rw [← Real.exp_nat_mul, ← Real.exp_add, ← Real.exp_nat_mul, Real.exp_le_exp]
      have hc := Star.credit_bound D R μ d N hμ i
      unfold Star.credit at hc
      linarith only [hc]
    _ ≤ _ := by
      rw [sum_const, card_univ, nsmul_eq_mul]
      exact mul_le_mul_of_nonneg_right (hb N) (by positivity)

end OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
end

/-! # Uniform estimates for prices of polynomial tensors on a valuation disk -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.ITensor

variable {K S : Type} [Field K] [Fintype S] [Nonempty S]

private theorem poly (v : AddValuation K (WithTop ℚ)) (P : Polynomial K) :
    ∃ q : ℚ, ∀ x y, 0 ≤ v x → 0 ≤ v y → ∀ m : ℚ, ↑m ≤ v (x - y) →
      ↑q ≤ v (P.eval x) ∧ ↑(q + m) ≤ v (P.eval x - P.eval y) := by
  induction P using Polynomial.induction_on with
  | C a =>
    by_cases ha : a = 0
    · exact ⟨0, by simp [ha]⟩
    obtain ⟨q, hq⟩ := WithTop.ne_top_iff_exists.mp (v.ne_top_iff.mpr ha)
    exact ⟨q, by simp [← hq]⟩
  | add A B ih ig =>
    obtain ⟨q, hq⟩ := ih
    obtain ⟨r, hr⟩ := ig
    refine ⟨min q r, fun x y hx hy m hm => ?_⟩
    obtain ⟨h, h'⟩ := hq x y hx hy m hm
    obtain ⟨k, k'⟩ := hr x y hx hy m hm
    simp only [Polynomial.eval_add]
    rw [add_sub_add_comm]
    constructor
    · exact v.map_le_add ((WithTop.coe_le_coe.mpr (min_le_left _ _)).trans h)
        ((WithTop.coe_le_coe.mpr (min_le_right _ _)).trans k)
    · exact v.map_le_add ((WithTop.coe_le_coe.mpr (by gcongr; exact min_le_left _ _)).trans h')
        ((WithTop.coe_le_coe.mpr (by gcongr; exact min_le_right _ _)).trans k')
  | monomial n a ih =>
    obtain ⟨q, hq⟩ := ih
    refine ⟨q, fun x y hx hy m hm => ?_⟩
    let P := Polynomial.C a * Polynomial.X ^ n
    obtain ⟨h, h'⟩ := hq x y hx hy m hm
    rw [pow_succ, ← mul_assoc]
    change ↑q ≤ v ((P * Polynomial.X).eval x) ∧
      ↑(q + m) ≤ v ((P * Polynomial.X).eval x - (P * Polynomial.X).eval y)
    simp only [Polynomial.eval_mul, Polynomial.eval_X]
    constructor
    · rw [v.map_mul]; exact h.trans (le_add_of_nonneg_right hx)
    · rw [show P.eval x * x - P.eval y * y =
        (P.eval x - P.eval y) * y + P.eval x * (x - y) by ring]
      apply v.map_le_add
      · rw [v.map_mul]; exact h'.trans (le_add_of_nonneg_right hy)
      · rw [v.map_mul, WithTop.coe_add]; exact add_le_add h hm

private theorem coordinate_bound [DecidableEq S] {R : Subring K}
    (f : ITensor R S →+* ℝ) (hf : Monotone f) (X : S → Type) [∀ s, Fintype (X s)]
    (a : (∀ s, X s) → K) :
    f (table R X a) ≤ ∑ i, f (scalar R S (a i)) := by
  classical
  let F i x := if x = i then a i else 0
  have h : (∑ i, F i) = a := by ext x; simp [F]
  calc
    _ = f (table R X (∑ i, F i)) := by rw [h]
    _ ≤ ∑ i, f (table R X (F i)) := table_sum X f hf _ _
    _ ≤ _ := Finset.sum_le_sum fun i _ => hf (table_single _ _ _ _)

variable {ν : AddValuation K (WithTop ℚ)}
variable {A : K → ITensor (integralRing ν) S} {d : ℕ}

theorem Family.uniform_bound (h : Family A d) :
    ∃ B > (0 : ℝ), ∀ (g : ITensor (integralRing ν) S →+* ℝ), Monotone g →
      (∀ (z : K) (r : ℚ), ν z = ↑r → g (scalar (integralRing ν) S z) = Real.exp (-(r : ℝ))) →
      ∀ x y : K, x ∈ integralRing ν → y ∈ integralRing ν → ∀ m : ℚ, ↑m ≤ ν (x - y) →
        g (A x) ≤ B ∧ |g (A x) - g (A y)| ≤ B * Real.exp (-(m : ℝ)) := by
  classical
  obtain ⟨X, _, P, _, he⟩ := h
  choose q hq using fun i => poly ν (P i)
  let B := ∑ i, Real.exp (-(q i : ℝ))
  have hB : 0 ≤ B := Finset.sum_nonneg fun _ _ => (Real.exp_pos _).le
  refine ⟨B + 1, by linarith, fun g hg hv x y hx hy m hm => ?_⟩
  let v (x : K) (i : ∀ s, X s) := (P i).eval x
  have ha : g (A x) ≤ B := by
    rw [he]
    refine (coordinate_bound g hg _ _).trans (Finset.sum_le_sum fun i _ => ?_)
    exact scalar_bound g hv (hq i x y hx hy m hm).1
  have diff (x y : K) (hx : x ∈ integralRing ν) (hy : y ∈ integralRing ν) (hm : ↑m ≤ ν (x - y)) :
      g (A x) - g (A y) ≤ B * Real.exp (-(m : ℝ)) := by
    have hb : g (table (integralRing ν) X (v x - v y)) ≤ B * Real.exp (-(m : ℝ)) := by
      unfold B
      rw [Finset.sum_mul]
      refine (coordinate_bound g hg _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      rw [← Real.exp_add, ← neg_add, ← Rat.cast_add]
      exact scalar_bound g hv (hq i x y hx hy m hm).2
    have hw := hg (table_add (integralRing ν) X (v x - v y) (v y))
    rw [sub_add_cancel, map_add, ← he, ← he] at hw
    linarith
  have hm' : ↑m ≤ ν (y - x) := by rwa [AddValuation.map_sub_swap]
  exact ⟨ha.trans (le_add_of_nonneg_right zero_le_one),
    ((abs_sub_le_iff.mpr ⟨diff x y hx hy hm, diff y x hy hx hm'⟩)).trans
      (mul_le_mul_of_nonneg_right (le_add_of_nonneg_right zero_le_one) (Real.exp_nonneg _))⟩

theorem Family.uniform_continuous (h : Family A d) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℚ, 0 < m ∧ ∀ (g : ITensor (integralRing ν) S →+* ℝ), Monotone g →
      (∀ (z : K) (r : ℚ), ν z = ↑r → g (scalar (integralRing ν) S z) = Real.exp (-(r : ℝ))) →
      ∀ x y : K, x ∈ integralRing ν → y ∈ integralRing ν → ↑m ≤ ν (x - y) → |g (A x) - g (A y)| ≤ ε := by
  obtain ⟨B, hB, hc⟩ := h.uniform_bound
  obtain ⟨n, hn⟩ := exists_nat_gt (B / ε)
  have hn' := (div_pos hB hε).trans hn
  refine ⟨n, by exact_mod_cast hn', fun g hg hs x y hx hy hm =>
    ((hc g hg hs x y hx hy _ hm).2).trans ?_⟩
  rw [Rat.cast_natCast, Real.exp_neg, ← div_eq_mul_inv, div_le_iff₀ (Real.exp_pos _), mul_comm]
  exact (div_le_iff₀ hε).mp (hn.le.trans (by linarith [Real.add_one_le_exp (n : ℝ)]))

end OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
end

/-! # Bounding the assisted cost throughout the valuation ring -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
open Prices

variable {K S U : Type} [Field K] [Fintype S] [Nonempty S] [Fintype U]
    {O : Subring K} {A : K → ITensor O (S ⊕ U)} {d : ℕ}

/-- A uniform bound at infinitely many integral nodes with unit differences
extends to every integral argument, even with joint closures of powers. -/
theorem Family.assisted_bound (h : Family A d) (f : ITensor O S →+* ℝ) (hf : Monotone f)
    {J : Type*} [Infinite J] (v : J → K) (hv : Function.Injective v)
    (hi : ∀ i, v i ∈ O) (hu : ∀ i j, (v i - v j)⁻¹ ∈ O)
    {r : ℝ} (hr : ∀ j, assisted (pad U) f (A (v j)) ≤ r) (x : K) (hx : x ∈ O) :
    assisted (pad U) f (A x) ≤ r := by
  let H := extensionData (U := U) f hf
  have hp := (H.aided_nonneg _).trans (hr (Classical.arbitrary J))
  refine H.test_with_loss _ hp (show 0 < (d : ℝ) + 1 by positivity) fun n _ s hs => ?_
  let w : Fin (n * d + 1) ↪ J := Fin.valEmbedding.trans (Infinite.natEmbedding J)
  have hl (i : Fin (n * d + 1)) : (Lagrange.basis Finset.univ (v ∘ w) i).eval x ∈ O := by
    simp only [Lagrange.basis, Lagrange.basisDivisor, Polynomial.eval_prod,
      Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_sub, Polynomial.eval_X]
    exact O.prod_mem fun j _ => O.mul_mem (hu _ _) (O.sub_mem hx (hi _))
  refine (h.test_nodes f hf n x hs (v ∘ w) (hv.comp w.injective) (by simp)).trans ?_
  calc
    _ ≤ ∑ _i : Fin (n * d + 1), r ^ n := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hz := H.aided_nonneg (A (v (w i)))
      have hb := hf (scalar_le_one O _ (hl i))
      rw [map_one] at hb
      exact (mul_le_of_le_one_left (pow_nonneg hz _) hb).trans (pow_le_pow_left₀ hz (hr _) _)
    _ ≤ _ := by
      rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
      apply mul_le_mul_of_nonneg_right _ (pow_nonneg hp n)
      push_cast
      linarith

end OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
end

/-! # Lifting simultaneous parameter tests to the integral ring -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
open Spectral Prices

variable {F K S I : Type} [Field F] [Field K] [Algebra F K]
    [Fintype S] [Nonempty S] {O : Subring K} (hv : constants F K ≤ O)

theorem fromBase_pad [DecidableEq S] (U : Type) [Fintype U] [DecidableEq U] (A : Tensor F S) :
    fromBase hv (Tensor.pad U A) = pad U (fromBase hv A) := by
  rw [← place_inl, place_fromBase, Tensor.place_inl]

theorem Family.list_prod {I : Type*} (A : I → K → ITensor O S) (h : ∀ i, ∃ d, Family (A i) d)
    (w : List I) : ∃ d, Family (fun x => (w.map (fun i => A i x)).prod) d := by
  induction w with
  | nil =>
    refine ⟨0, fun _ => Unit, inferInstance, fun _ => 1, by simp, fun _ => ?_⟩
    simp only [List.map_nil, List.prod_nil, Polynomial.eval_one]
    exact (scalar_one (S := S) (O := O)).symm
  | cons i w ih =>
    obtain ⟨d, hd⟩ := h i
    obtain ⟨e, he⟩ := ih
    exact ⟨d + e, hd.mul he⟩

def liftFamily (X : S → Type) [∀ s, Fintype (X s)] (A : (∀ s, X s) → Polynomial F)
    (x : K) : ITensor O S :=
  table O X (fun u => ((A u).map (algebraMap F K)).eval x)

theorem liftFamily_constant (X : S → Type) [∀ s, Fintype (X s)]
    (A : (∀ s, X s) → Polynomial F) (x : F) :
    liftFamily X A (algebraMap F K x) = fromBase hv (evalFamily X A x) := by
  unfold evalFamily liftFamily
  rw [fromBase_table]
  simp only [Polynomial.eval_map_apply]

/-- For a fixed integral parameter, a lifted price passes all product
tests if the original tests hold off a finite set in the infinite base. -/
theorem lift_shared [Infinite F] (f : Tensor F S →+* ℝ) (hf : Monotone f)
    (g : ITensor O S →+* ℝ) (hg : Monotone g) (he : ∀ A, g (fromBase hv A) = f A)
    (B : Finset F) (X : I → S ⊕ Unit → Type) [∀ i s, Fintype (X i s)]
    (P : ∀ i, (∀ s, X i s) → Polynomial F) (p : I → ℝ)
    (h : ∀ z ∉ B, ∀ w : List I, ∀ T, Tensor.pad Unit T ≤
      (w.map (fun i => evalFamily (X i) (P i) z)).prod → f T ≤ (w.map p).prod)
    (z : K) (hz : z ∈ O) :
    ∃ k : ITensor O (S ⊕ Unit) →+* ℝ, Monotone k ∧ (∀ T, k (pad Unit T) = g T) ∧
      ∀ i, k (liftFamily (X i) (P i) z) ≤ p i := by
  classical
  let A i : K → ITensor O (S ⊕ Unit) := liftFamily (X i) (P i)
  have hA i : ∃ d, Family (A i) d := of_polynomial _ _
  let H := extensionData (U := Unit) g hg
  apply (H.assisted_extension_iff _ p).mpr
  intro w
  obtain ⟨d, hd⟩ := Family.list_prod A hA w
  let J := (↑B : Set F)ᶜ
  let _ : Infinite J := B.finite_toSet.infinite_compl.to_subtype
  let v (j : J) := algebraMap F K j.val
  have hvi : Function.Injective v := fun _ _ h => Subtype.ext ((algebraMap F K).injective h)
  refine hd.assisted_bound g hg v hvi (fun i => hv ⟨i.val, rfl⟩) ?_ ?_ z hz
  · intro i j
    simp only [v, ← map_sub, ← map_inv₀]
    exact hv ⟨_, rfl⟩
  · intro i
    let T j := evalFamily (X j) (P j) i.val
    have ha : (w.map (fun j => A j (v i))).prod = fromBase hv (w.map T).prod := by
      erw [map_list_prod (fromBase hv), List.map_map]
      exact congrArg List.prod (List.map_congr_left fun j _ => liftFamily_constant hv _ _ _)
    rw [ha]
    exact (lift_assisted hv f g hg he hf _).trans
      ((Tensor.assisted_extension_iff f hf T p).mp ((Tensor.extension_iff f hf T p).mpr (h i.val i.property)) w)

end OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
end

/-! Generic constants maximize assisted values throughout the valuation disk. -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued.ITensor

open Prices Motion K0 Finset Filter
open scoped Classical

variable {E S U : Type} [Field E] [Fintype S] [Nonempty S] [Fintype U]

variable {A : K0 E → ITensor (integralRing (K0.val E)) (S ⊕ U)} {d : ℕ} (h : Family A d)
    (f : ITensor (integralRing (K0.val E)) S →+* ℝ) (hf : Monotone f)

include h hf

theorem Family.assisted_generic (x : K0 E) (hx : 0 ≤ val E x) (r : ℝ)
    (hr : r < assisted (pad U) f (A x)) :
    ∀ᶠ c : E in cofinite, r < assisted (pad U) f (A (C c)) := by
  rw [eventually_cofinite]
  by_contra hi
  let B := {c : E | ¬ r < assisted (pad U) f (A (C c))}
  let _ : Infinite B := (show B.Infinite from hi).to_subtype
  have hc (a : E) : C a ∈ integralRing (K0.val E) := by
    change 0 ≤ val E (C a)
    by_cases ha : a = 0 <;> simp [ha]
  apply hr.not_ge
  refine h.assisted_bound f hf (fun a : B => C a.val) (fun _ _ h => Subtype.ext (C.injective h))
    (fun a => hc a.val) ?_ (fun a => le_of_not_gt a.property) x hx
  intro i j
  rw [← map_sub, ← map_inv₀]
  exact hc _

theorem Family.assisted_max :
    ∀ᶠ c : E in cocountable, ∀ x : K0 E, 0 ≤ val E x →
      assisted (pad U) f (A x) ≤ assisted (pad U) f (A (C c)) := by
  have countable (p : E → ℚ → Prop) (hp : ∀ q, ∀ᶠ c in cocountable, p c q) :
      ∀ᶠ c in cocountable, ∀ q, p c q := by
    apply mem_cocountable.mpr
    have h := Set.countable_iUnion (fun q => mem_cocountable.mp (hp q))
    refine h.mono fun c hc => ?_
    change ¬ (∀ q, p c q) at hc
    obtain ⟨q, hq⟩ := not_forall.mp hc
    exact Set.mem_iUnion.mpr ⟨q, hq⟩
  let g x := assisted (pad U) f (A x)
  have hm : ∀ᶠ c : E in cocountable, ∀ r : ℚ, (∃ x, 0 ≤ val E x ∧ (r : ℝ) < g x) →
      (r : ℝ) < g (C c) := by
    apply countable
    intro r
    by_cases he : ∃ x, 0 ≤ val E x ∧ (r : ℝ) < g x
    · obtain ⟨x, hx, hr⟩ := he
      have hs := h.assisted_generic f hf x hx r hr
      have he' : ∀ᶠ c : E in cocountable, (r : ℝ) < g (C c) :=
        mem_cocountable.mpr (mem_cofinite.mp hs).countable
      exact he'.mono fun _ h _ => h
    · exact Eventually.of_forall fun _ h => (he h).elim
  refine hm.mono fun c hc x hx => ?_
  by_contra! h
  obtain ⟨r, hr, hr'⟩ := exists_rat_btwn h
  exact hr.not_gt (hc r ⟨x, hx, hr'⟩)

end OAI.LinearAlgebra.MatrixExponent.Valued.ITensor
end

/-! # Families of tensor products on a valuation disk -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Valued
open Spectral Prices Motion K0 ITensor Filter

variable {E K S U : Type} [Field E] [Field K] [Fintype S] [Fintype U] [Nonempty S] {O : Subring K}

theorem countable_tensor [Countable K] : Countable (Tensor K S) := by
  classical
  let B := Σ d : S → ℕ, ((∀ i, Fin (d i)) → K)
  let repr (b : B) := Tensor.ofRaw (Raw.ofTable (fun i => Fin (b.1 i)) b.2)
  have hs : Function.Surjective repr := by
    intro A
    refine Quotient.inductionOn A fun a => ?_
    let d s := Fintype.card (a.leg s)
    let f s : Fin (d s) ≃ a.leg s := (Fintype.equivFin _).symm
    let b : B := ⟨d, fun x => a.coeff (fun s => f s (x s))⟩
    refine ⟨b, Tensor.ofRaw_eq (Raw.equiv_coeff f ?_)⟩
    exact fun x => Raw.coeff_ofTable _ _ x
  exact hs.countable

namespace ITensor
variable {A : K → ITensor O S} {d : ℕ}

theorem Family.constant (A : ITensor O S) : ∃ d, Family (fun _ => A) d := by
  refine Quotient.inductionOn A fun a => ?_
  refine ⟨0, a.leg, inferInstance, fun i => Polynomial.C (a.coeff i), by simp, fun x => ?_⟩
  simp only [Polynomial.eval_C, table_coeff]
  rfl

theorem Family.affine (h : Family A d) (a b : K) : ∃ e, Family (fun s => A (a + b * s)) e := by
  obtain ⟨X, _, P, _, h⟩ := h
  let q := Polynomial.C a + Polynomial.C b * Polynomial.X
  have e (x : K) : q.eval x = a + b * x := by
    simp only [q, Polynomial.eval_add, Polynomial.eval_C, Polynomial.eval_mul, Polynomial.eval_X]
  simpa only [Polynomial.eval_comp, e, h] using of_polynomial (O := O) X (fun i => (P i).comp q)

theorem Family.place [Nonempty U] [DecidableEq S] [DecidableEq U]
    (h : Family A d) (e : S → U) : ∃ n, Family (fun x => ITensor.place e (A x)) n := by
  obtain ⟨X, _, P, _, hp⟩ := h
  let L u := ∀ i : Raw.Fiber e u, X i
  let R (a : ∀ u, L u) := P (fun s => a (e s) ⟨s, rfl⟩)
  have eq (x) : ITensor.place e (A x) = table O L (fun a => (R a).eval x) := by
    rw [hp]
    refine ofRaw_eq (equiv_coeff (fun _ => Equiv.refl _) fun z => ?_)
    erw [Raw.coeff_group, Raw.coeff_ofTable, Raw.coeff_ofTable]
    rfl
  simpa only [eq] using of_polynomial (O := O) L R

end ITensor

abbrev RingOf (E : Type) [Field E] : Subring (K0 E) := integralRing (val E)

theorem C_mem (c : E) : C c ∈ RingOf E := by
  change 0 ≤ val E (C c)
  by_cases h : c = 0 <;> simp [h]

/-- Countably many polynomial tests can be maximized simultaneously.
The additional supremum over j need not be attained. -/
theorem generic_bounds {I J : Type*} [Countable I] (f : ITensor (RingOf E) S →+* ℝ)
    (hf : Monotone f) (A : I → J → K0 E → ITensor (RingOf E) (S ⊕ U))
    (hA : ∀ i j, ∃ d, Family (A i j) d) :
    ∀ᶠ c : E in cocountable, ∀ i r, (∀ j, assisted (pad U) f (A i j (C c)) ≤ r) →
      ∀ j x, x ∈ RingOf E → assisted (pad U) f (A i j x) ≤ r := by
  have := cocountable_countable E
  apply eventually_countable_forall.mpr
  intro i
  let p j x := assisted (pad U) f (A i j x)
  have ht : ∀ᶠ c : E in cocountable, ∀ t : ℚ, (∃ j x, x ∈ RingOf E ∧ ↑t < p j x) →
      ∃ j, ↑t < p j (C c) := by
    apply eventually_countable_forall.mpr
    intro t
    by_cases h : ∃ j x, x ∈ RingOf E ∧ ↑t < p j x
    · obtain ⟨j, x, hx, ht⟩ := h
      obtain ⟨_, hj⟩ := hA i j
      exact (hj.assisted_max f hf).mono fun c hc _ => ⟨j, ht.trans_le (hc x hx)⟩
    · exact Eventually.of_forall fun _ hh => (h hh).elim
  refine ht.mono fun c hc r hr j x hx => ?_
  by_contra! h
  obtain ⟨t, h₁, h₂⟩ := exists_rat_btwn h
  obtain ⟨k, hk⟩ := hc t ⟨j, x, hx, h₂⟩
  exact (h₁.trans hk).not_ge (hr k)

end OAI.LinearAlgebra.MatrixExponent.Valued
end
