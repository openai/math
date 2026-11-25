import OAI.Computability.NearSquareRoot.PhysicalWalshCompileInteriorEnds
import OAI.Computability.NearSquareRoot.PhysicalWalshCompileInteriorNativeFamily
import OAI.Computability.NearSquareRoot.PhysicalWalshXorDuskTotal
import OAI.Computability.NearSquareRoot.PhysicalWalshXorCanonicalTotal

/-! # Total execution of the native Walsh core on every reached shape -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileInterior

open IntegerMultiplication Code Strip Space PhysicalWalsh PhysicalWalshNode Interior SwapPrefix
open PhysicalWalshCompileSwapRulers (World)
open PhysicalWalshCompileInteriorHeader (nativeRegime)

/-- Reindex the terminating native gate to actual padded signed-record lanes.
Only the positive-level geometry is used. The finite-code source and physical
input and output encodings coincide with the cost-sensitive native pass. -/
theorem nativeTotalOfGate {gate : Cmd}
    (ok : XorWindow.GateTotal nativeRegime worldPrefix worldBits worldRow gate)
    (a W : ℕ) (ha : 4 ≤ a) (pred : Shape → Prop) :
    NativeTotalOn a W pred (XorWindow.duskCmd gate) := by
  let I := {t : XorInput W // pred t.shape}
  let s (i : I) := i.val.shape
  let pick (i : I) : World := ⟨a,W,0,0,0,s i⟩
  let stride (t : World) := S t.a t.shape
  let width (t : World) := t.shape.w
  let x (i : I) := extend (a+1) W (s i) i.val.row
  have positive (i : I) : 0 < stride (pick i) := Nat.mul_pos (s i).suff_pos (Nat.two_pow_pos _)
  have pass := XorWindow.duskOfGateTotal nativeRegime worldPrefix worldSlot stride width ok pick positive x
  obtain ⟨time,space,C,hc⟩ := pass
  refine ⟨time,space,C,fun i env park base room => ?_⟩
  have h := hc i env park base room
  change BoundedFits env _ (pile 0 (.fork (rawHeader a W (s i))
    (send (stream (rows a W (s i)*S a (s i)) (x i)))) park)
    (pile 0 (send (stream (rows a W (s i)*S a (s i)) (moved (a:=a) i.val))) park) _ _ _ at h
  rw [rows_mul_S (W:=W) ha i.val.positive] at h
  exact h

/-- A total physical address-stage file induces a total recursive front
gate independently of the outer tuple's exponent and reserve certificate. -/
theorem nativeTotalOfStage {stage : Cmd}
    (ok : XorWindow.StagesTotal nativeRegime worldPrefix worldBits worldRow stage)
    (a W : ℕ) (ha : 4 ≤ a) (pred : Shape → Prop) :
    NativeTotalOn a W pred (XorWindow.duskCmd (XorWindow.gateCmd nativeRegime worldBits nativeWidth stage)) :=
  nativeTotalOfGate (ok.gateTotal nativeWidth) a W ha pred

open Controlled.PositionProgram
open PhysicalWalshCompileInteriorHeader (nativeP)

/-- A terminating canonical row opcode gives totality on every reached
Walsh shape, even when the outer candidate's claimed reserve is too small
to prove its sharper rate. -/
theorem nativeTotalOfCanonical {cmd : Cmd}
    (ok : ∃ time : Call id → ℕ, EffectiveTask.Runs cmd time Call.input Call.output)
    (a W : ℕ) (ha : 4 ≤ a) (pred : Shape → Prop) :
    NativeTotalOn a W pred (XorWindow.duskCmd (XorWindow.gateCmd nativeRegime worldBits nativeWidth
      (XorWindow.stageCmd nativeRegime worldPrefix worldBits nativeP nativeWidth worldRow cmd))) :=
  nativeTotalOfGate (XorWindow.gateTotalFromCanonical nativeRegime worldPrefix worldBits nativeP nativeWidth worldRow ok)
    a W ha pred

/-- Any coarse opcode certificate is sufficient for functional correctness
of the full native Dusk command on actual inputs. -/
theorem nativeTotalOfOpAt {cmd : Cmd} {ρ : ℝ} (ok : OpAt cmd ρ id)
    (a W : ℕ) (ha : 4 ≤ a) (pred : Shape → Prop) :
    NativeTotalOn a W pred (XorWindow.duskCmd (XorWindow.gateCmd nativeRegime worldBits nativeWidth
      (XorWindow.stageCmd nativeRegime worldPrefix worldBits nativeP nativeWidth worldRow cmd))) :=
  nativeTotalOfGate (XorWindow.gateTotalFromOpAt nativeRegime worldPrefix worldBits nativeP nativeWidth worldRow ok)
    a W ha pred

end PhysicalWalshCompileInterior

end NearSquareRoot
end Computability
end OAI
