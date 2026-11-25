import OAI.Computability.NearSquareRoot.PrecisionPreparedPhase
import OAI.Computability.NearSquareRoot.PrecisionGridStream

/-! # Emitting prepared phase coefficients on the streamed multiplier's grid -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhaseTable

open IntegerMultiplication Code Grid Dusk Strip Staff Brief Star Carry FixedPoint

variable {J : Type} {s : Regime J}

private theorem integerPart {x : J → ℝ} (h : Blot s x) :
    ∃ v : J → S, s.Has v ∧ ∀ j, |(whole (v j) : ℝ) - x j| ≤ 1 := by
  obtain ⟨a,p,pos,val⟩ := h.ticket
  refine ⟨_, p.thenDo quotientP, fun j ↦ ?_⟩
  rw [← val]
  exact sq_close _ _ (pos j)

/-- Componentwise truncation moves a complex point by at most three halves
of a grid unit. This leaves room for the error in the phase supplied to it. -/
private theorem truncatePair (x : J → ℂ) (h : Curve s x) (f : J → ℕ) (F : Realizes s f) :
    ∃ v : J → Coef, s.Has v ∧ ∀ j, ‖toC (content (v j)) - x j * 2^(f j)‖ ≤ 3 / 2 := by
  have scale : Curve s (fun j ↦ (2 : ℂ)^(f j)) := by
    have h' := Curve.real (Blot.natural ((Figure.natural (r := s) 2).repeated F))
    push_cast at h'
    exact h'
  obtain ⟨re,im⟩ := h.mul scale
  obtain ⟨v,hv,ev⟩ := integerPart re
  obtain ⟨u,hu,eu⟩ := integerPart im
  refine ⟨fun j ↦ (v j,u j), hv.pair hu, fun j ↦ ?_⟩
  let d := toC (content (v j,u j)) - x j * 2 ^ f j
  have dr : |d.re| ≤ 1 := by simpa [d, toC, content] using ev j
  have di : |d.im| ≤ 1 := by simpa [d, toC, content] using eu j
  have sq := Complex.sq_norm d
  rw [Complex.normSq_apply] at sq
  have sr := sq_le_sq' (abs_le.mp dr).1 (abs_le.mp dr).2
  have si := sq_le_sq' (abs_le.mp di).1 (abs_le.mp di).2
  change ‖d‖ ≤ 3 / 2
  nlinarith

/-- A unit-modulus phase available at three extra accuracy bits can be emitted
in the exact signed-word width and precision consumed by the prefix pass. -/
theorem Prepared.toRecord {g : J → ℕ} {z : J → ℂ} (G : Realizes s g)
    (unit : ∀ j, ‖z j‖ = 1) (phase : Prepared s (fun j ↦ 70*g j + 3) z) :
    ∃ output : (j : J) → Record (g j), s.Has (fun j ↦ mark (output j)) ∧
      ∀ j, ‖FixedPoint.value (g j) (output j) - z j‖ ≤ 1/(2:ℝ)^(70*g j) := by
  obtain ⟨input, built, err⟩ := phase
  let n j := 70 * g j
  let w j := componentBits (g j)
  let f j := fractionBits (g j)
  have N : Realizes s n := (Realizes.fix 70).times G
  have W : Realizes s w := ((Realizes.fix 96).times G).plus (.fix 4)
  have F : Realizes s f := N.plus (.fix 1)
  let x j := meaning (n j + 3 + 2) (n j + 3 + 5) (input j)
  have hx : Curve s x := by
    have hrat := grainRat_realized ((N.plus (.fix 3)).plus (.fix 2)) input built
    have hc : Curve s (fun j ↦ toComplex (grainRat (n j+3+2) (input j))) := hrat
    simpa only [x, grainRat_value] using hc
  obtain ⟨v,hv,ev⟩ := truncatePair x hx f F
  have bound j : ‖x j‖ ≤ 2 := by
    have tr := norm_add_le (x j - z j) (z j)
    rw [sub_add_cancel, unit] at tr
    have small : 1/(2:ℝ)^(n j+3) ≤ 1 :=
      (div_le_one (by positivity)).mpr (one_le_pow₀ (by norm_num))
    linarith [show ‖x j - z j‖ ≤ _ from err j]
  have fits j : ‖toC (content (v j))‖ < (2:ℝ)^(w j) := by
    have tr := norm_add_le (toC (content (v j)) - x j * 2^f j) (x j * 2^f j)
    rw [sub_add_cancel, norm_mul, norm_pow, show ‖(2:ℂ)‖ = (2:ℝ) by norm_num] at tr
    have hw : f j + 3 ≤ w j := by dsimp [f,w,fractionBits,componentBits]; omega
    have pw := pow_le_pow_right₀ (by norm_num : (1:ℝ) ≤ 2) hw
    rw [pow_add] at pw
    norm_num at pw
    nlinarith [mul_le_mul_of_nonneg_right (bound j) (by positivity : 0 ≤ (2:ℝ)^f j),
      ev j, show 1 ≤ (2:ℝ)^f j from one_le_pow₀ (by norm_num)]
  have short' j := Grid.short _ (Grid.into _) (fits j)
  let out (j : J) := wrapMap (w j) (content (v j))
  have focus' j : focus (w j + 1) (content (v j)) := by
    have le : (2:ℤ)^w j ≤ 2^(w j+1) := pow_le_pow_right₀ (by norm_num) (by omega)
    exact ⟨(short' j).1.trans_le le,(short' j).2.trans_le le⟩
  have encode j : mark (out j) = spell (fit (tally (w j+1),v j)) := by
    rw [spellG _ (fit_r ..),fit_small _ _ (focus' j)]
  refine ⟨out, ?_, fun j ↦ ?_⟩
  · simp_rw [encode]
    exact ((Regime.Has.pair (W.plus (.fix 1)) hv).ez (fit_easy.compose spell_easy))
  have eval : FixedPoint.value (g j) (out j) = toC (content (v j)) / (2:ℂ)^f j := by
    unfold FixedPoint.value meaning out
    rw [recovers _ (short' j)]
  have delta : ‖FixedPoint.value (g j) (out j)-x j‖ ≤ (3/2)/(2:ℝ)^f j := by
    rw [eval, show toC (content (v j))/(2:ℂ)^f j - x j =
      (toC (content (v j))-x j*2^f j)/(2:ℂ)^f j by
      rw [sub_div, mul_div_cancel_right₀ _ (by norm_num)]]
    rw [norm_div, norm_pow, show ‖(2:ℂ)‖ = (2:ℝ) by norm_num]
    exact div_le_div_of_nonneg_right (ev j) (by positivity)
  refine (norm_sub_le_norm_sub_add_norm_sub _ (x j) _).trans
    ((add_le_add delta (err j)).trans ?_)
  change 3/2/((2:ℝ)^(n j+1)) + 1/2^(n j+3) ≤ 1/2^n j
  rw [pow_succ, pow_add]
  have hpos : 0 < (2:ℝ)^n j := by positivity
  field_simp
  linarith

attribute [local irreducible] componentBits fractionBits guardedK Prepared

/-- A complete local coefficient table in the physical order and exact record
layout taken by the guarded global tensor-prefix multiplication. -/
theorem Prepared.guardedRow {k n : J → ℕ} (K : Realizes s k) (N : Realizes s n)
    (z : (j : J) → Fin (n j) → ℂ) (unit : ∀ j i, ‖z j i‖ = 1)
    (hs : Prepared (signal n N) (fun t : Across n ↦ 70*guardedK (k t.1)+3)
      (fun t ↦ z t.1 t.2)) :
    ∃ v : (j : J) → Fin (n j) → Record (guardedK (k j)),
      s.Has (fun j ↦ List.ofFn fun i ↦ mark (k := componentBits (guardedK (k j))) (v j i)) ∧
      ∀ j i, ‖FixedPoint.value (guardedK (k j)) (v j i) - z j i‖ ≤ 1/(2:ℝ)^(70*guardedK (k j)) := by
  have G : Realizes s (fun j ↦ guardedK (k j)) := by
    unfold guardedK
    exact ((Realizes.fix 2).times K).plus (.fix 1)
  obtain ⟨v, h, err⟩ := Prepared.toRecord (s := signal n N)
    (g := fun t : Across n ↦ guardedK (k t.1)) (z := fun t ↦ z t.1 t.2)
    (landing n N _ G) (fun t ↦ unit t.1 t.2) hs
  exact ⟨fun j i ↦ v ⟨j,i⟩, harvest n N (fun j i ↦ mark (k := componentBits (guardedK (k j))) (v ⟨j,i⟩)) h,
    fun j i ↦ err ⟨j,i⟩⟩

end PhaseTable

end NearSquareRoot
end Computability
end OAI
