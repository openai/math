import OAI.Computability.NearSquareRoot.PhysicalWalshCompileInteriorNativeFamily
import OAI.Computability.NearSquareRoot.PhysicalWalshFrontSquare

/-! # Named large-field XOR gates at a degree-independent threshold -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileInterior

open IntegerMultiplication Code PhysicalWalsh PhysicalWalshNode PhysicalWalsh.XorThreshold
open Controlled Interior GeneratorSyntax CommonRegisters

/-- The branch predicate is read from the descriptor and is independent of
the fixed native command's proof of a workspace bound. -/
def SquareNative (ρ : ℝ) (cmd : Cmd) : Prop :=
  ∀ a W, 4 ≤ a → NativeOn a W ρ (FrontDispatch.squareFits a) cmd

/-- The virtual cost width pays a fixed interpreter's reserve on every
square-log large field. No extra cells appear in the physical record array. -/
theorem squareNativeOfGate {ρ : ℝ} (upper : ρ ≤ 1) {D : ℕ} {c : Cmd} (gate : WorldGate ρ D c) :
    SquareNative ρ (XorWindow.duskCmd c) := by
  intro a W ha
  apply nativeOfGateOn gate a W (D^2) ha
  · intro s large
    apply XorSquare.reserve_le_extra
    have h := payload_le_suffix (A:=a+1) (D:=FrontDispatch.squareDegree (a+1) s)
      (Q:=Header.scale (a+1) s) (L:=L (a+1) s) (by omega) large
    simpa only [XorSquare.cut,FrontDispatch.squareDegree,payloadBits,pow_two,B,
      show a+1-4=a-3 by omega] using h
  · intro s large
    exact factor_le_prefix upper large (Nat.le_add_left ..)

/-- Effective candidate files and an absolute register cutoff suffice at
the native interface. The (potentially varying) degree does not enter the
source program or its branch predicate. -/
theorem squareNativeFamily {J : Type} [Primcodable J] {ρ : J → ℝ} (le : ∀ j, ρ j ≤ 1)
    {gate : J → Cmd} (effective : Effective ltr gate) (R : ℕ) (regs : ∀ j, Within R (gate j))
    (ok : ∀ j, ∃ D, WorldGate (ρ j) D (gate j)) :
    Effective ltr (fun j => XorWindow.duskCmd (gate j)) ∧ ∃ K, 0 < K ∧
      ∀ j, Within K (XorWindow.duskCmd (gate j)) ∧ SquareNative (ρ j) (XorWindow.duskCmd (gate j)) := by
  obtain ⟨K,hK,w⟩ := XorWindow.duskCmd_within R
  exact ⟨XorWindow.duskCmd_effective effective,K,hK,fun j =>
    ⟨w _ (regs j),(ok j).elim (fun _ run => squareNativeOfGate (le j) run)⟩⟩

/-- Extend the actual parameterized opcode commands through the native
instruction forest, record packing, and record unpacking. -/
theorem squareNativeStageFamily {J : Type} [Primcodable J] {ρ : J → ℝ} (le : ∀ j, ρ j ≤ 1)
    {c : J → Cmd} (effective : Effective ltr c) (R : ℕ) (regs : ∀ j, Within R (c j))
    (ok : ∀ j, ∃ D, XorWindow.StagesAt PhysicalWalshCompileInteriorHeader.nativeRegime
      worldPrefix worldBits worldRow (ρ j) D (c j)) :
    let cmd j := XorWindow.duskCmd (XorWindow.gateCmd PhysicalWalshCompileInteriorHeader.nativeRegime worldBits nativeWidth (c j))
    Effective ltr cmd ∧ ∃ K, 0 < K ∧ ∀ j, Within K (cmd j) ∧ SquareNative (ρ j) (cmd j) := by
  obtain ⟨S,_,hS⟩ := XorWindow.gateCmd_within PhysicalWalshCompileInteriorHeader.nativeRegime worldBits nativeWidth R
  apply squareNativeFamily le (XorWindow.gateCmd_effective PhysicalWalshCompileInteriorHeader.nativeRegime worldBits
    nativeWidth effective) S (fun j => hS _ (regs j))
  intro j
  obtain ⟨d,run⟩ := ok j
  exact ⟨_,XorWindow.boundedGateOnNamed worldPrefix worldBits nativeWidth worldRow run⟩

end PhysicalWalshCompileInterior

end NearSquareRoot
end Computability
end OAI
