import OAI.Computability.NearSquareRoot.PhysicalWalshXorCanonical
import OAI.Computability.NearSquareRoot.PhysicalWalshXorNativeStage
import OAI.Computability.NearSquareRoot.PhysicalWalshXorGateCommand

/-! # Canonical opcode dispatch through the complete native XOR forest

For fixed joint input geometry, replacing the canonical opcode program
changes a single source parameter. Its opcode, forest and row descriptors
are computed from the actual runtime header.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh.XorWindow

open IntegerMultiplication Code Adic Strip Staff Loom Packed
open Controlled Controlled.PositionProgram NamedPacked CommonRegisters GeneratorSyntax Filter

variable {X : Type} (r : Regime X) (P k : X → ℕ) (hP : Realizes r P) (hk : Realizes r k)
    {U : X → Type} (u : (x:X) → Series (U x))

private abbrev opCode (j : OpWorld P k U) := j.2.1.val
private abbrev opData (j : OpWorld P k U) := j.2.2

/-- Prefix reading the canonical (width,opcode) packet on each prefix row. -/
noncomputable def canonicalPrep : Cmd :=
  (nativeRowsFromCanonical (opRegime r P k hk U) _ _ (opPrefix r P k hk U hP) (opWidth r P k hk U)
    (opCode P k (U:=U)) (opInstruction r P k hk U) (opValid P k U)
    (fun j => u j.1) (opData P k)).choose

/-- The single stage that the native XOR calls for each emitted instruction. -/
noncomputable def stageCmd (native : Cmd) : Cmd :=
  windowCmd (opRegime r P k hk U) _ _ (opPrefix r P k hk U hP) (opWidth r P k hk U)
    (fun j => u j.1) (opCode P k (U:=U)) (opData P k) ((canonicalPrep r P k hP hk u).join native)

theorem stageCmd_effective {T : Type} [Primcodable T] {native : T → Cmd} (h : Effective ltr native) :
    Effective ltr (fun t => stageCmd r P k hP hk u (native t)) :=
  windowCmd_effective (opRegime r P k hk U) _ _ (opPrefix r P k hk U hP) (opWidth r P k hk U)
    (fun j => u j.1) (opCode P k (U:=U)) (opData P k) ((effective_const ltr (canonicalPrep r P k hP hk u)).join h)

theorem stageCmd_within (n : ℕ) : ∃ b,0 < b ∧ ∀ c : Cmd, Within n c →
    Within b (stageCmd r P k hP hk u c) := by
  have room := windowCmd_within (opRegime r P k hk U) _ _ (opPrefix r P k hk U hP) (opWidth r P k hk U)
    (fun j => u j.1) (opCode P k (U:=U)) (opData P k)
  obtain ⟨b,pos,le,pre,scan⟩ := ((eventually_gt_atTop (0:ℕ)).and ((eventually_ge_atTop n).and
    ((RegisterSelect.within_eventually (canonicalPrep r P k hP hk u)).and room))).exists
  exact ⟨b,pos,fun c h => scan _ ⟨pre,RegisterSelect.within_mono le c h⟩⟩

/-- Every intermediate store is permuted by its decoded instruction. -/
theorem stagesFromCanonical {native : Cmd} {ρ : ℝ} (h : OpAt native ρ id) :
    ∃ D, StagesAt r P k u ρ D (stageCmd r P k hP hk u native) := by
  have prep := (nativeRowsFromCanonical (opRegime r P k hk U) _ _ (opPrefix r P k hk U hP)
    (opWidth r P k hk U) (opCode P k (U:=U)) (opInstruction r P k hk U) (opValid P k U)
    (fun j => u j.1) (opData P k)).choose_spec.1 native ρ h
  obtain ⟨D,run⟩ := opcodeOnNamed (opRegime r P k hk U) _ _ (opPrefix r P k hk U hP)
    (opWidth r P k hk U) (fun j => u j.1) (opCode P k (U:=U)) (opData P k) prep
  exact ⟨D,gateStagesOnNamed P k hk u (D:=D) run⟩

/-- An aligned XOR on the complete physical window for any certified
canonical opcode program. The program source is independent of its degree. -/
theorem gateFromCanonical {native : Cmd} {ρ : ℝ} (h : OpAt native ρ id) :
    ∃ D, GateAt r P k u ρ D (gateCmd r k hk (stageCmd r P k hP hk u native)) := by
  obtain ⟨d,stage⟩ := stagesFromCanonical r P k hP hk u h
  exact ⟨_,boundedGateOnNamed P k hk u stage⟩

end PhysicalWalsh.XorWindow

end NearSquareRoot
end Computability
end OAI
