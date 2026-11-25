import OAI.Computability.NearSquareRoot.PhysicalWalshXorGate
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask

/-! # The runtime instruction and data seen by the native XOR opcode

Every input in the joint domain has an actual opcode from the computed XOR
forest and an arbitrary intermediate array. The type is fixed independently
of the code selected by the emitter and of its row-cost exponent.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow
open IntegerMultiplication Code Adic Strip Staff Loom Packed
open Space Controlled Controlled.PositionProgram XorReserve

abbrev OpWorld {X : Type} (P k : X → ℕ) (U : X → Type) :=
  (x : X) × {q // q ∈ instructions (k x)} × Input (P x) (k x) (U x)

section Descriptor
variable {X : Type} (r : Regime X) (P k : X → ℕ) (hk : Realizes r k) (U : X → Type)

private def opLabel (x:X) (z : {q // q ∈ instructions (k x)} × Input (P x) (k x) (U x)) :=
  send z.1.val

include hk in
private theorem opSize :
    Dom (fun s : OpWorld P k U => r.scale s.1) (fun s => (opLabel P k U s.1 s.2).count) := by
  have table := XorSweep.program_has (third_realizes hk) (guardWidth_realizes hk)
  exact (table.extent.map (Sigma.fst : OpWorld P k U → X)).mono fun s => (size_bel s.2.1.prop).le

/-- The physical instruction carries the joint global descriptor on its left. -/
def opRegime : Regime (OpWorld P k U) := onboard r (opLabel P k U) (opSize r P k hk U)

theorem opPrefix (hp : Realizes r P) : Realizes (opRegime r P k hk U) (fun j => P j.1) :=
  onboard_small _ (opSize r P k hk U) _ hp

theorem opWidth : Realizes (opRegime r P k hk U) (fun j => k j.1) :=
  onboard_small _ (opSize r P k hk U) _ hk

theorem opInstruction : (opRegime r P k hk U).Has (fun j => j.2.1.val) :=
  onboard_hat _ (opSize r P k hk U)

theorem opValid (v : OpWorld P k U) : WellFormed (k v.1) (guardWidth (k v.1)) v.2.1.val :=
  XorSweep.program_valid _ v.2.1.prop

end Descriptor

/-- A single named opcode command on every instruction of the forest. -/
def StagesAt {X : Type} (r : Regime X) (P k : X → ℕ) {U : X → Type}
    (u : (x:X) → Series (U x)) (ρ : ℝ) (D : ℕ) (stage : Cmd) : Prop :=
  ∀ {Y : Type} (select : Y → X) (B m Q factor : Y → ℕ),
      (∀ y, (u (select y)).count ≤ pack (B y) (m y)) → (∀ y, r.scale (select y) ≤ Q y) →
      (∀ y, 0 < m y) → (∀ y, payloadBits D (Q y) ≤ B y) →
      (∀ y, 2*Spindle.modes k (τ:=ρ) (select y) ≤ factor y) → (∀ y, factor y ≤ 2^P (select y)) →
      let V y := volume (P (select y)) (k (select y)) (B y) (m y)
      let T := (y:Y) × {q // q ∈ instructions (k (select y))} × Input (P (select y)) (k (select y)) (U (select y))
      EffectiveBoundedTask.Runs stage (fun t:T => V t.1*(factor t.1+1)) (fun t => V t.1)
        (fun t => .fork (.fork (r.header (select t.1)) (send t.2.1.val)) (store (u (select t.1)) t.2.2))
        (fun t => store (u (select t.1)) (t.2.2 ∘ fun b =>
          act (guardWidth (k (select t.1))) b t.2.1.val))

/-- The named opcode implementation on the actual joint domain may be restricted
to the arbitrary intermediate rows occurring in a chosen gate execution. -/
theorem gateStagesOnNamed {X : Type} {r : Regime X} (P k : X → ℕ) (hk : Realizes r k)
    {U : X → Type} (u : (x:X) → Series (U x)) {ρ : ℝ} {D : ℕ} {stage : Cmd}
    (opcode : ∀ {Y : Type} (take : Y → OpWorld P k U) (B m Q factor : Y → ℕ),
      (∀ y,(u (take y).1).count ≤ pack (B y) (m y)) →
      (∀ y,(opRegime r P k hk U).scale (take y) ≤ Q y) →
      (∀ y, 0 < m y) → (∀ y,payloadBits D (Q y) ≤ B y) →
      (∀ y,2*Spindle.modes (fun j : OpWorld P k U => k j.1) (τ:=ρ) (take y) ≤ factor y) →
      (∀ y,factor y ≤ 2^P (take y).1) →
      let V y := volume (P (take y).1) (k (take y).1) (B y) (m y)
      EffectiveBoundedTask.Runs stage (fun y => V y*(factor y+1)) V
        (fun y => .fork ((opRegime r P k hk U).header (take y)) (store (u (take y).1) (take y).2.2))
        (fun y => store (u (take y).1) ((take y).2.2 ∘
          fun b => act (guardWidth (k (take y).1)) b (take y).2.1.val))) :
    StagesAt r P k u ρ D stage := by
  intro Y select B m Q factor lengths scale pos low rate high V T
  let take (t:T) : OpWorld P k U := ⟨select t.1,t.2⟩
  exact opcode take (fun t => B t.1) (fun t => m t.1) (fun t => Q t.1) (fun t => factor t.1)
    (fun t => lengths t.1) (fun t => scale t.1) (fun t => pos t.1) (fun t => low t.1)
    (fun t => rate t.1) (fun t => high t.1)

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
