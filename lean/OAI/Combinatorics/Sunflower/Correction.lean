import OAI.Combinatorics.Sunflower.CorrectionSpec
import OAI.Combinatorics.Sunflower.Broadcast

/-! The error correction in one equality-test step. A row of the output contains
a proposed direction at each site. At a target this row and the external symbol
determine the row to read from the first broadcast, and its direction selects
the local map of the return broadcast. -/

open scoped Classical BigOperators
open OAI.LinearAlgebra.SpectralBooks OAI.LinearAlgebra.SpectralBooks.SiteTensor

noncomputable section

namespace OAI
namespace Combinatorics
namespace Sunflower

variable {I : Type*} [Fintype I] {A D : Type}

/-- A nonzero direction survives exactly when all its local labels agree with
the announced difference. -/
private theorem sum_label_eq_indicator [Fintype D]
    (K : Finset I) (hK : K.Nonempty) (code : D → A) (hc : Function.Injective code)
    (q : ∀ i, MaskLeg K D i) (z : A) :
    (∑ d : D, if code d = z then (if q = (fun _ _ => d) then (1 : ℂ) else 0) else 0) =
      if ∀ i (h : i ∈ K), code (q i h) = z then 1 else 0 := by
  classical
  obtain ⟨j,hj⟩ := hK
  by_cases ha : ∀ i (h : i ∈ K), code (q i h) = z
  · let d := q j hj
    have hd : code d = z := ha j hj
    have hq : q = fun _ _ => d := by
      funext i hi
      exact hc ((ha i hi).trans hd.symm)
    rw [ite_eq_left ha]
    rw [Finset.sum_eq_single d]
    · simp [hd, hq]
    · intro e _ he
      exact ite_eq_right (fun h => he (hc (h.trans hd.symm)))
    · simp
  · rw [ite_eq_right ha]
    apply Finset.sum_eq_zero
    intro d _
    by_cases hd : code d = z
    · have hn : q ≠ (fun _ _ => d) := by
        intro h
        apply ha
        intro i hi
        simpa [h] using hd
      simp [hd, hn]
    · simp [hd]

/-- Two common-label broadcasts implement the nonzero correction term.
The label decoder may omit a symbol, as it does for the omitted zero direction
in a binary matching. -/
theorem correction_maps_general [Fintype D]
    (P T : Finset I) (hT : T.Nonempty)
    (code : D → A) (hc : Function.Injective code)
    (decode : D → A → A) (delta : A → A → A)
    (hdecode : ∀ p x y, decode p y = x ↔ code p = delta x y)
    (R₁ Q₁ R₂ Q₂ : Raw.{0} I ℂ)
    (M : Control.Map (fun _ : I => A) R₁.Leg (fun i => Q₁.Leg i × MaskLeg T A i))
    (N : Control.Map (fun _ : I => A) R₂.Leg (fun i => Q₂.Leg i × MaskLeg P A i))
    (hM : ∀ x c, (∀ i ∈ P, c i = x) → ∀ o,
      Control.eval M c R₁.coeff o =
        Q₁.coeff (fun i => (o i).1) * (if (fun i => (o i).2) = (fun _ _ => x) then 1 else 0))
    (hN : ∀ x c, (∀ i ∈ T, c i = x) → ∀ o,
      Control.eval N c R₂.coeff o =
        Q₂.coeff (fun i => (o i).1) * (if (fun i => (o i).2) = (fun _ _ => x) then 1 else 0)) :
    ∃ W : Control.Map (fun _ : I => A) (R₁.mul R₂).Leg
      (fun i => (Q₁.mul Q₂).Leg i × MaskLeg (P ∪ T) D i),
      ∀ x y c, (∀ i ∈ P, c i = x) → (∀ i ∈ T, c i = y) → ∀ o,
        Control.eval W c (R₁.mul R₂).coeff o =
          (Q₁.mul Q₂).coeff (fun i => (o i).1) *
          ∑ p : D, if code p = delta x y then
            (if (fun i => (o i).2) = (fun _ _ => p) then 1 else 0) else 0 := by
  classical
  let left (i : I) (c : A) (q : MaskLeg (P ∪ T) D i) : MaskLeg T A i :=
    fun hi => decode (q (Finset.mem_union_right P hi)) c
  let right (i : I) (q : MaskLeg (P ∪ T) D i) : MaskLeg P A i :=
    fun hi => code (q (Finset.mem_union_left T hi))
  let control (i : I) (c : A) (q : MaskLeg (P ∪ T) D i) :=
    if hi : i ∈ T then code (q (Finset.mem_union_right P hi)) else c
  refine ⟨fun i c o a =>
    M i c (o.1.1, left i c o.2) a.1 *
      N i (control i c o.2) (o.1.2, right i o.2) a.2, ?_⟩
  intro x y c hP hT' o
  let q (i : I) := (o i).2
  let a₁ (i : I) := ((o i).1.1, left i (c i) (q i))
  let a₂ (i : I) := ((o i).1.2, right i (q i))
  let c₂ (i : I) := control i (c i) (q i)
  have hfac :
      Control.eval (fun i c o a =>
        M i c (o.1.1, left i c o.2) a.1 *
        N i (control i c o.2) (o.1.2, right i o.2) a.2) c (R₁.mul R₂).coeff o =
        Control.eval M c R₁.coeff a₁ * Control.eval N c₂ R₂.coeff a₂ := by
    exact contract_mul (fun i => M i (c i)) (fun i => N i (c₂ i))
      R₁.coeff R₂.coeff (fun i => (a₁ i, a₂ i))
  rw [hfac, hM x c hP]
  rw [sum_label_eq_indicator (P ∪ T) (hT.mono (Finset.subset_union_right)) code hc q]
  let z := delta x y
  have ht : ((fun i => (a₁ i).2) = fun _ _ => x) ↔
      ∀ i (hi : i ∈ T), code (q i (Finset.mem_union_right P hi)) = z := by
    constructor
    · intro hh i hi
      apply (hdecode _ x y).1
      rw [← hT' i hi]
      exact congrFun (congrFun hh i) hi
    · intro hh
      funext i hi
      change decode _ (c i) = x
      rw [hT' i hi]
      exact (hdecode _ x y).2 (hh i hi)
  have hp : ((fun i => (a₂ i).2) = fun _ _ => z) ↔
      ∀ i (hi : i ∈ P), code (q i (Finset.mem_union_left T hi)) = z := by
    constructor
    · exact fun hh i hi => congrFun (congrFun hh i) hi
    · exact fun hh => funext fun i => funext (hh i)
  have hu : (∀ i (hi : i ∈ P ∪ T), code (q i hi) = z) ↔
      ((∀ i (hi : i ∈ P), code (q i (Finset.mem_union_left T hi)) = z) ∧
        (∀ i (hi : i ∈ T), code (q i (Finset.mem_union_right P hi)) = z)) := by
    constructor
    · exact fun h => ⟨fun i hi => h i _, fun i hi => h i _⟩
    · rintro ⟨p,t⟩ i hi
      rcases Finset.mem_union.1 hi with hip | hit
      · exact p i hip
      · exact t i hit
  rw [if_congr ht rfl rfl]
  by_cases h : ∀ i (hi : i ∈ T), code (q i (Finset.mem_union_right P hi)) = z
  · have hc₂ : ∀ i ∈ T, c₂ i = z := by
      intro i hi
      simpa [c₂, control, hi] using h i hi
    rw [ite_eq_left h, hN z c₂ hc₂, if_congr hp rfl rfl]
    change _ = _ * (if ∀ i (hi : i ∈ P ∪ T), code (q i hi) = z then 1 else 0)
    rw [if_congr hu rfl rfl]
    rw [if_congr (and_iff_left h) rfl rfl]
    simp only [mul_one, mul_assoc, Raw.mul, a₁, a₂]
  · have hn : ¬ ∀ i (hi : i ∈ P ∪ T), code (q i hi) = z := fun H => h (hu.1 H).2
    rw [ite_eq_right h, ite_eq_right hn]
    simp only [mul_zero, zero_mul]

private theorem binary_decode {b : ℕ} (p : Binary.Direction b) (x y : Binary.Word b) :
    p.val + y = x ↔ p.val = x + y := by
  have bit : ∀ a v w : ZMod 2, a + w = v ↔ a = v + w := by decide
  exact ⟨fun h => funext fun i => (bit _ _ _).mp (congrFun h i),
    fun h => funext fun i => (bit _ _ _).mpr (congrFun h i)⟩

/-- Pairing the forward and return broadcasts produces the binary correction. -/
theorem correction_maps {J : Type} [Fintype J] [DecidableEq J] {b : ℕ}
    (P T : Finset J) (hT : T.Nonempty)
    (R₁ Q₁ R₂ Q₂ : Raw.{0} J ℂ)
    (h₁ : Broadcasts P T (Binary.Word (b+1)) R₁ Q₁)
    (h₂ : Broadcasts T P (Binary.Word (b+1)) R₂ Q₂) :
    CorrectionMaps P T b (R₁.mul R₂) (Q₁.mul Q₂) := by
  classical
  obtain ⟨M,hM⟩ := h₁
  obtain ⟨N,hN⟩ := h₂
  obtain ⟨W,hW⟩ := correction_maps_general (A := Binary.Word (b+1)) (D := Binary.Direction (b+1))
    P T hT Subtype.val Subtype.val_injective
    (fun p y => p.val + y) (· + ·) (binary_decode (b := b+1)) R₁ Q₁ R₂ Q₂ M N
    (fun x c hc o => by
      rw [hM x c hc o]
      split_ifs <;> rfl)
    (fun x c hc o => by
      rw [hN x c hc o]
      split_ifs <;> rfl)
  refine ⟨W, ?_⟩
  intro x y c hp ht o
  refine (hW x y c hp ht o).trans ?_
  apply congrArg (_ * ·)
  apply Finset.sum_congr rfl
  intro p _
  split_ifs <;> try rfl
  all_goals
    rename_i h₁ h₂
    first | exact False.elim (h₂ h₁) | exact False.elim (h₁ h₂)

private theorem nonzero_product {J : Type} [Fintype J] [Nonempty J] (X Y : Raw.{0} J ℂ)
    (hX : X.coeff ≠ 0) (hY : Y.coeff ≠ 0) : (X.mul Y).coeff ≠ 0 := by
  apply (ofRaw_eq_zero_iff _).not.mp
  rw [ofRaw_mul]
  exact mul_ne_zero ((ofRaw_eq_zero_iff _).not.mpr hX) ((ofRaw_eq_zero_iff _).not.mpr hY)

/-- The positive gap reduces the cost slope of the two broadcasts below the
price of the shared correction index once the fixed parameter is large enough. -/
theorem exists_correction {J : Type} [Fintype J] [Nonempty J] [DecidableEq J]
    (φ : normalizedSpectrum ((· ≤ ·) : TensorClass.{0} J ℂ → _ → Prop))
    (P T : Finset J) (hP : P.Nonempty) (hT : T.Nonempty) (hPT : Disjoint P T)
    {h : ℕ} (hh : 0 < h) (b : ℕ) :
    ∃ U V : Raw.{0} J ℂ, U.coeff ≠ 0 ∧ V.coeff ≠ 0 ∧ CorrectionMaps P T b U V ∧
      rawLogPrice φ 1 U - rawLogPrice φ 1 V ≤
        (maskDiagonalPrice φ 1 (P ∪ T) -
          (maskDiagonalPrice φ 1 P + maskDiagonalPrice φ 1 T - maskDiagonalPrice φ 1 (P ∪ T)) +
          12 / (h : ℝ)) * (b+1 : ℕ) + 2 * broadcastOverhead (Fintype.card J) h := by
  classical
  obtain ⟨R₁,Q₁,hR₁,hQ₁,hB₁,e₁⟩ :=
    exists_broadcast (A := Binary.Word (b+1)) φ P T hP hT hPT hh _ (Binary.card_word _)
  obtain ⟨R₂,Q₂,hR₂,hQ₂,hB₂,e₂⟩ :=
    exists_broadcast (A := Binary.Word (b+1)) φ T P hT hP hPT.symm hh _ (Binary.card_word _)
  refine ⟨_, _, nonzero_product _ _ hR₁ hR₂, nonzero_product _ _ hQ₁ hQ₂,
    correction_maps P T hT R₁ Q₁ R₂ Q₂ hB₁ hB₂, ?_⟩
  rw [rawLogPrice_mul φ 1 _ _ hR₁ hR₂, rawLogPrice_mul φ 1 _ _ hQ₁ hQ₂]
  rw [Finset.union_comm T P] at e₂
  linear_combination e₁ + e₂

end Sunflower
end Combinatorics
end OAI
