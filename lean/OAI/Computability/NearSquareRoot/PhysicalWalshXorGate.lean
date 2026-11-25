import OAI.Computability.NearSquareRoot.PhysicalWalshXorOpcode
import OAI.Computability.NearSquareRoot.PhysicalWalshXorForest

/-! # Uniform physical program for an entire slot-to-slot XOR -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic
open IntegerMultiplication.Strip IntegerMultiplication.Staff IntegerMultiplication.Loom
open IntegerMultiplication.Packed NearSquareRoot.Space NearSquareRoot.Controlled
open NearSquareRoot.Controlled.PositionProgram XorReserve

abbrev instructions (k : ℕ) := XorSweep.program (k/3) (guardWidth k)

abbrev Input (P k : ℕ) (U : Type) := (Fin k → Bool) → Block 2 P → U → Bead

private abbrev Work {X : Type} (P k : X → ℕ) (U : X → Type) (x : X) :=
  {q // q ∈ instructions (k x)} × Input (P x) (k x) (U x)

/-- Dispatch all physically emitted opcodes on an arbitrary data state, using
one finite program. The controller constructs each opcode's frame from the
actual global header and the encoded opcode read by the schedule. -/
theorem gateStagesOn {ρ : ℝ} (hρ : 1/2 < ρ)
    {X : Type} {r : Regime X} (P k : X → ℕ) (hP : Realizes r P) (hk : Realizes r k)
    {U : X → Type} (u : (x:X) → Series (U x)) :
    ∃ D : ℕ, ∀ {Y : Type} (select : Y → X) (B m Q factor : Y → ℕ),
      (∀ y, (u (select y)).count = pack (B y) (m y)) → (∀ y, r.scale (select y) ≤ Q y) →
      (∀ y, 0 < m y) → (∀ y, payloadBits D (Q y) ≤ B y) →
      (∀ y, 2*Spindle.modes k (τ:=ρ) (select y) ≤ factor y) → (∀ y, factor y ≤ 2^P (select y)) →
      let V y := volume (P (select y)) (k (select y)) (B y) (m y)
      let T := (y:Y) × {q // q ∈ instructions (k (select y))} × Input (P (select y)) (k (select y)) (U (select y))
      BoundedTask (fun t:T => V t.1*(factor t.1+1)) (fun t => V t.1)
        (fun t => .fork (.fork (r.header (select t.1)) (send t.2.1.val)) (store (u (select t.1)) t.2.2))
        (fun t => store (u (select t.1)) (t.2.2 ∘ fun b =>
          act (guardWidth (k (select t.1))) b t.2.1.val)) := by
  let J := Sigma (Work P k U)
  let label (x:X) (s:Work P k U x) := send s.1.val
  have table := XorSweep.program_has (third_realizes hk) (guardWidth_realizes hk)
  have meter : Dom (fun s:J => r.scale s.1) (fun s => (label s.1 s.2).count) :=
    (table.extent.map (Sigma.fst : J → X)).mono fun s => (size_bel s.2.1.prop).le
  let rr := onboard r label meter
  have pref : Realizes rr (fun j:J => P j.1) := onboard_small label meter _ hP
  have width : Realizes rr (fun j:J => k j.1) := onboard_small label meter _ hk
  have op : rr.Has (fun j:J => j.2.1.val) := onboard_hat label meter
  obtain ⟨D,stage⟩ := opcodeOn (opcodeStage hρ) (fun j:J => P j.1) (fun j => k j.1)
    (fun j => j.2.1.val) pref width op (fun j => XorSweep.program_valid _ j.2.1.prop)
    (fun j => u j.1) (fun j => (u j.1).count) (fun _ => le_rfl) (fun j => j.2.2)
  refine ⟨D,fun select B m Q factor lengths scale pos low rate high => ?_⟩
  intro V T
  let choose (t:T) : J := ⟨select t.1,t.2⟩
  exact stage choose (fun t => B t.1) (fun t => m t.1) (fun t => Q t.1) (fun t => factor t.1)
    (fun t => lengths t.1) (fun t => scale t.1) (fun t => pos t.1) (fun t => low t.1)
    (fun t => rate t.1) (fun t => high t.1)

/-- An aligned XOR of the high native field into the middle native field,
preserving all spectators. Time includes the computed header forest and all
passes. Every opcode invocation reuses the same bounded workspace. -/
theorem boundedGateOn {ρ : ℝ} (hρ : 1/2 < ρ)
    {X : Type} {r : Regime X} (P k : X → ℕ) (hP : Realizes r P) (hk : Realizes r k)
    {U : X → Type} (u : (x:X) → Series (U x)) :
    ∃ D : ℕ, ∀ {Y : Type} (select : Y → X) (B m Q factor : Y → ℕ),
      (∀ y, (u (select y)).count = pack (B y) (m y)) → (∀ y, r.scale (select y) ≤ Q y) →
      (∀ y, 0 < m y) → (∀ y, payloadBits D (Q y) ≤ B y) →
      (∀ y, 2*Spindle.modes k (τ:=ρ) (select y) ≤ factor y) → (∀ y, factor y ≤ 2^P (select y)) →
      let V y := volume (P (select y)) (k (select y)) (B y) (m y)
      let T := (y:Y) × Input (P (select y)) (k (select y)) (U (select y))
      BoundedTask (fun t:T => (4+3*guardWidth (k (select t.1)))*(V t.1*(factor t.1+1))+1)
        (fun t => V t.1) (fun t => .fork (r.header (select t.1)) (store (u (select t.1)) t.2))
        (fun t => store (u (select t.1)) (t.2 ∘ directed (XorSweep.gate (k (select t.1)/3)))) := by
  obtain ⟨d,stages⟩ := gateStagesOn hρ P k hP hk u
  have table := XorSweep.program_has (third_realizes hk) (guardWidth_realizes hk)
  obtain ⟨e,fold⟩ := XorForest.boundedProgramOn k (fun x => guardWidth (k x)) table
  refine ⟨max d e,fun select B m Q factor lengths scale pos low rate high => ?_⟩
  intro V T
  have degree j y (hj : j ≤ max d e) : payloadBits j (Q y) ≤ B y :=
    (Nat.mul_le_mul_right (Nat.clog 2 (Q y+1)) hj).trans (low y)
  have reserve y : (r.scale (select y)+1)^e ≤ V y := by
    have cap := polynomial_le_pack (scale y) (pos y) (degree e y (le_max_right ..))
    apply cap.trans
    change pack (B y) (m y) ≤ volume (P (select y)) (k (select y)) (B y) (m y)
    rw [← rows_volume]
    exact (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos (k (select y)))).trans
      (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  exact fold select (fun y f => store (u (select y)) f) V factor 5
    (fun _ => by unfold guardWidth; omega) reserve
    (fun y f => store_size _ f (lengths y).le (pos y))
    (stages select B m Q factor lengths scale pos (fun y => degree d y (le_max_left ..)) rate high)

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
