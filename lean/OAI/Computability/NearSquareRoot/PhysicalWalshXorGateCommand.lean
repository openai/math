import OAI.Computability.NearSquareRoot.PhysicalWalshXorForestCommand
import OAI.Computability.NearSquareRoot.PhysicalWalshXorStageWorld

/-! # The named gate interpreter for a native Walsh XOR

The emitted program reads a forest of actual native instructions. Each
instruction enters the supplied stage with the original global header and
the current record array. The forest program and its degree are fixed once
for the entire joint parameter domain.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow
open IntegerMultiplication Code Adic Strip Staff Loom Packed
open Space Controlled Controlled.PositionProgram XorReserve CommonRegisters GeneratorSyntax Filter

section Geometry
variable {X : Type} (r : Regime X) (k : X → ℕ) (hk : Realizes r k)

include hk in
theorem instructionTable : r.Has (fun x => instructions (k x)) :=
  XorSweep.program_has (third_realizes hk) (guardWidth_realizes hk)

/-- The polynomial degree of the fixed forest setup, before specifying the opcode. -/
noncomputable def forestDegree : ℕ :=
  (XorForest.boundedProgramOnNamed k (fun x => guardWidth (k x)) (instructionTable r k hk)).choose

noncomputable def gateCmd (stage : Cmd) : Cmd :=
  XorForest.programCmd (XorForest.prepCmd (instructionTable r k hk)) stage

theorem gateCmd_effective {P : Type} [Primcodable P] {stage : P → Cmd} (hs : Effective ltr stage) :
    Effective ltr (fun p => gateCmd r k hk (stage p)) :=
  XorForest.programCmd_effective (effective_const _ _) hs

theorem gateCmd_within (R : ℕ) : ∃ S : ℕ, 0 < S ∧ ∀ stage : Cmd, Within R stage →
    Within S (gateCmd r k hk stage) := by
  obtain ⟨S,room,h₃,prep⟩ := ((eventually_ge_atTop R).and ((eventually_ge_atTop 3).and
    (RegisterSelect.within_eventually (XorForest.prepCmd (instructionTable r k hk))))).exists
  exact ⟨S,by omega,fun stage h => XorForest.programCmd_within h₃ prep (RegisterSelect.within_mono room stage h)⟩

end Geometry

/-- The complete XOR forest, operating on rows with arbitrary actual spectator data. -/
def GateAt {X : Type} (r : Regime X) (P k : X → ℕ) {U : X → Type} (u : (x:X) → Series (U x))
    (ρ : ℝ) (D : ℕ) (cmd : Cmd) : Prop :=
  ∀ {Y : Type} (select : Y → X) (B m Q factor : Y → ℕ),
      (∀ y, (u (select y)).count ≤ pack (B y) (m y)) → (∀ y, r.scale (select y) ≤ Q y) →
      (∀ y, 0 < m y) → (∀ y, payloadBits D (Q y) ≤ B y) →
      (∀ y, 2*Spindle.modes k (τ:=ρ) (select y) ≤ factor y) → (∀ y, factor y ≤ 2^P (select y)) →
      let V y := volume (P (select y)) (k (select y)) (B y) (m y)
      let T := (y:Y) × Input (P (select y)) (k (select y)) (U (select y))
      EffectiveBoundedTask.Runs cmd (fun t:T => (4+3*guardWidth (k (select t.1)))*(V t.1*(factor t.1+1))+1)
        (fun t => V t.1) (fun t => .fork (r.header (select t.1)) (store (u (select t.1)) t.2))
        (fun t => store (u (select t.1)) (t.2 ∘ directed (XorSweep.gate (k (select t.1)/3))))

/-- Preparing and folding the opcode forest gives the same source for every
restriction of the joint input domain and every certified reserve of cells. -/
theorem boundedGateOnNamed {X : Type} {r : Regime X} (P k : X → ℕ) (hk : Realizes r k)
    {U : X → Type} (u : (x:X) → Series (U x)) {ρ : ℝ} {d : ℕ} {stage : Cmd}
    (stages : StagesAt r P k u ρ d stage) :
    GateAt r P k u ρ (max d (forestDegree r k hk)) (gateCmd r k hk stage) := by
  intro Y select B m Q factor lengths scale pos low rate high V T
  have degree j y (hj : j ≤ max d (forestDegree r k hk)) : payloadBits j (Q y) ≤ B y :=
    (Nat.mul_le_mul_right (Nat.clog 2 (Q y+1)) hj).trans (low y)
  have reserve y : (r.scale (select y)+1)^(forestDegree r k hk) ≤ V y := by
    have cap := polynomial_le_pack (scale y) (pos y) (degree (forestDegree r k hk) y (le_max_right ..))
    apply cap.trans
    change pack (B y) (m y) ≤ volume (P (select y)) (k (select y)) (B y) (m y)
    rw [← rows_volume]
    exact (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos (k (select y)))).trans
      (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos _))
  exact (XorForest.boundedProgramOnNamed k (fun x => guardWidth (k x)) (instructionTable r k hk)).choose_spec
    select (fun y f => store (u (select y)) f) V factor 5
    (fun _ => by unfold guardWidth; omega) reserve
    (fun y f => store_size _ f (lengths y) (pos y))
    (stages select B m Q factor lengths scale pos (fun y => degree d y (le_max_left ..)) rate high)

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
