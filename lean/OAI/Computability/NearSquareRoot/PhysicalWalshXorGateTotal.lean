import OAI.Computability.NearSquareRoot.PhysicalWalshXorGateCommand

/-! # Totality of the emitted XOR instruction forest

At a fixed descriptor the instruction list and the possible finite arrays
are finite. Their maximum resource consumption therefore gives a common
arena for the named forest interpreter even without a rate certificate.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow
open IntegerMultiplication Code Adic Strip Staff Loom Packed Controlled Controlled.PositionProgram

/-- The opcode command returns the correctly permuted array for every
well-formed instruction emitted at this descriptor and every input array. -/
def StagesTotal {X : Type} (r : Regime X) (P k : X → ℕ) {U : X → Type}
    (u : (x:X) → Series (U x)) (cmd : Cmd) : Prop :=
  ∃ t s : OpWorld P k U → ℕ, EffectiveBoundedTask.Runs cmd t s
    (fun i => .fork (.fork (r.header i.1) (send i.2.1.val)) (store (u i.1) i.2.2))
    (fun i => store (u i.1) (i.2.2 ∘ fun b => act (guardWidth (k i.1)) b i.2.1.val))

/-- Unrestricted correctness of the complete named gate on its physical array. -/
def GateTotal {X : Type} (r : Regime X) (P k : X → ℕ) {U : X → Type}
    (u : (x:X) → Series (U x)) (cmd : Cmd) : Prop :=
  ∃ t s : ((x:X) × Input (P x) (k x) (U x)) → ℕ, EffectiveBoundedTask.Runs cmd t s
    (fun i => .fork (r.header i.1) (store (u i.1) i.2))
    (fun i => store (u i.1) (i.2 ∘ directed (XorSweep.gate (k i.1/3))))

/-- The very same program file used for the quantitative gate runs to
completion with arbitrary total opcodes. Bounds may depend on the descriptor. -/
theorem StagesTotal.gateTotal {X : Type} {r : Regime X} {P k : X → ℕ} (hk : Realizes r k)
    {U : X → Type} {u : (x:X) → Series (U x)} {cmd : Cmd} (h : StagesTotal r P k u cmd) :
    GateTotal r P k u (gateCmd r k hk cmd) := by
  classical
  obtain ⟨time,space,step⟩ := h
  let D := forestDegree r k hk
  let State (x:X) := Input (P x) (k x) (U x)
  let Job (x:X) := {q // q ∈ instructions (k x)} × State x
  let (x:X) : Fintype (U x) := Fintype.ofEquiv (Fin (u x).count) (u x).index.symm
  let (x:X) : Fintype (Block 2 (P x)) := Fintype.ofEquiv (Fin (2^P x)) (flatAddress 2 (P x)).symm
  let (x:X) : Fintype {q // q ∈ instructions (k x)} :=
    Fintype.subtype (instructions (k x)).toFinset (by simp)
  let size (x:X) (f:State x) := (store (u x) f).count
  let price (x:X) (j:Job x) := max (time ⟨x,j⟩) (space ⟨x,j⟩)
  let V (x:X) := max ((r.scale x+1)^D) (max (Finset.univ.sup (size x)) (Finset.univ.sup (price x)))
  have run (i : OpWorld P k U) : max (time i) (space i) ≤ V i.1 :=
    (Finset.le_sup (f:=price i.1) (Finset.mem_univ i.2)).trans ((le_max_right ..).trans (le_max_right ..))
  have box (x) (f:State x) : (store (u x) f).count ≤ 1*V x := by
    rw [one_mul]
    exact (Finset.le_sup (f:=size x) (Finset.mem_univ f)).trans ((le_max_left ..).trans (le_max_right ..))
  have forest := (XorForest.boundedProgramOnNamed k (fun x => guardWidth (k x))
    (instructionTable r k hk)).choose_spec id (fun x f => store (u x) f) V (fun _ => 0) 1
    (fun _ => by unfold guardWidth; omega) (fun _ => le_max_left ..) box
    (step.mono (fun i => (le_max_left ..).trans ((run i).trans (by simp))) (fun i => (le_max_right ..).trans (run i)))
  exact ⟨_,_,forest⟩

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
