import OAI.Computability.VPVNP.CompressorExecutionCalendar
import OAI.Computability.VPVNP.CompressorLevelCounts
import OAI.Computability.VPVNP.CursorBranchBudget

/-!
# Uniform size bounds along partial descriptor runs

The next graph is determined by the current selected term. Its width bound
holds as soon as that term has been chosen, even when a later selector has
no admissible terms. The remaining calendar length pays for the growth of
the field widths at every such boundary.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PrefixLevelScale

open Compression CursorBounds CursorNetwork Filter

variable {R : Type*} [CommRing R] {a g b l : ℕ} {X : State a g}

/-- Bounds on the current state and on every branch reached after one more
selection. The terminal graph is included. -/
def Within (positions width : ℕ) : {a g : ℕ} → {X : State a g} →
    StateExecution R b l X → Prop
  | _, _, X, .done _ => X.positions ≤ positions ∧ X.maxWireWidth ≤ width
  | _, _, X, .more _ next => X.positions ≤ positions ∧ X.maxWireWidth ≤ width ∧
      ∀ i, Within positions width (next i)

theorem Within.current {P M : ℕ} {E : StateExecution R b l X} (h : Within P M E) :
    X.positions ≤ P ∧ X.maxWireWidth ≤ M := by
  cases E with
  | done => exact h
  | more => exact ⟨h.1, h.2.1⟩

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} {B : S.Templates}
variable {f : B.Entry → R} {hf : B.IsSolution f}

private theorem of_calendar (E : StateExecution R b l X) (o : PassOrigins B f hf E)
    (rec : E.Records) {C P M : ℕ} (hC : 0 < C) (bounded : E.Bounded C rec)
    (phases : List ExecutionCalendar.Phase) (follows : ExecutionCalendar.Follows E o phases)
    (positions : X.positions ≤ P) (width : C ^ phases.length * (X.maxWireWidth + 1) ≤ M) :
    Within P M E := by
  induction E generalizing phases with
  | done X =>
    have cur := Nat.le_mul_of_pos_left (X.maxWireWidth + 1) (Nat.pow_pos (n := phases.length) hC)
    exact ⟨positions, (Nat.le_succ _).trans (cur.trans width)⟩
  | @more _ _ _ _ graph p next ih =>
    cases phases with
    | nil => exact follows.elim
    | cons phase rest =>
      have cur := Nat.le_mul_of_pos_left (n := C ^ (rest.length + 1))
        (graph.maxWireWidth + 1) (Nat.pow_pos hC)
      have current := cur.trans width
      refine ⟨positions, (Nat.le_succ _).trans current, fun i ↦ ?_⟩
      apply ih i (o.2 i) (rec.2 i) (bounded.2 i) rest (follows.2 i)
        ((o.1.next_positions_le i).trans positions)
      have nxt := Nat.succ_le_succ (bounded.1 i).2.2
      have stepBound := nxt.trans (bounded.1 i).2.1
      simpa only [List.length_cons, pow_succ, Nat.mul_assoc] using
        (Nat.mul_le_mul_left (C ^ rest.length) stepBound).trans
          (by simpa only [List.length_cons, pow_succ, Nat.mul_assoc] using width)

theorem execute (T : ℕ) {lanes : ℕ} (h : T * S.laneBits ≤ lanes)
    (X : State (S.degreeExponent 0) lanes) {P M : ℕ} (positions : X.positions ≤ P)
    (width : B.growthConstant ^ T * (X.maxWireWidth + 1) ≤ M) :
    Within P M (B.execute f hf T h X) := by
  have bounded := (Procedure.repeat_recordBounds (B.recordBounds f hf) _ T lanes
    (Nat.add_sub_of_le h).symm X).1
  apply of_calendar (B.execute f hf T h X) (executeOrigins B f hf T h X) (B.records f hf T h X)
    (C := B.recordLimit) (le_max_left 1 _) bounded _ (ExecutionCalendar.execute_follows T h X)
    positions
  have count : (ExecutionCalendar.blocks S.steps T).length = (S.steps + 1) * T := by
    simp [ExecutionCalendar.blocks, ExecutionCalendar.oneBlock, Nat.mul_comm]
  rw [count, pow_mul]
  exact (Nat.mul_le_mul_right _ (Nat.pow_le_pow_left (le_max_right 2 _) T)).trans width

/-- The input-length threshold precedes the coefficient solution, the lane
split, and all partial choices of the actual descriptor program. -/
theorem eventually_execute (B : S.Templates) (u : PairExponents B.growthConstant)
    (b : ℕ) (hb : max S.laneBits 5 ≤ b) : ∀ᶠ n : ℕ in atTop,
    ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
      (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
      Within (initialPositions b n) n
        (B.execute f hf (blockCount (u.θ : ℝ) n) hT (pairInput S labels hD)) := by
  have pos := (Rat.cast_pos (K := ℝ)).mpr u.theta_pos
  have small := (Rat.cast_lt (K := ℝ)).mpr u.theta_lt
  norm_num at small
  have growth : 1 ≤ (B.growthConstant : ℝ) := by
    exact_mod_cast (show 1 ≤ B.growthConstant by linarith [B.growthConstant_ge_two])
  filter_upwards [cursorResource_bounds b S.laneBits pos.le (by linarith) growth u.growth
    (A := 1) (by norm_num) hb, eventually_ge_atTop 1] with n bounds hn
  intro base lanes labels hD hT A _ f hf
  apply execute _ hT _ (pairInput_positions S labels hD).le
  apply Nat.cast_le (α := ℝ) |>.mp
  push_cast
  have hwidth : ((pairInput S labels hD).maxWireWidth : ℝ) + 1 ≤ (initialWidth b n : ℝ) + 1 := by
    exact_mod_cast Nat.succ_le_succ (pairInput_maxWireWidth S labels hD)
  have hr : (n : ℝ) ^ (3 / 10 : ℝ) ≤ n := by
    simpa using Real.rpow_le_rpow_of_exponent_le (Nat.one_le_cast.mpr hn)
      (by norm_num : (3 / 10 : ℝ) ≤ 1)
  have resource := bounds.2.1
  rw [one_mul] at resource
  exact (mul_le_mul_of_nonneg_left hwidth (pow_nonneg (Nat.cast_nonneg _) _)).trans
    (resource.trans hr)

end CompressorRecords.PrefixLevelScale

end VPVNP
end Computability
end OAI
