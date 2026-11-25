import OAI.Hierarchy.DescentDonorGatherRAM
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! # Complete native donor geometry on all input registers -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM
open DescentSixParty.Chronology DescentSIMDLookup ProtocolRAM
open Computability.VPVNP.BurstRAM ThreeFlat.RAM PhysicalProcedure

def phase (tabs : Tables6) (inputs : Fields) (rom : Banks) (out H J M w : ℕ) : NativePhase w :=
  ⟨program tabs inputs rom out H J M w,clocks tabs inputs H J M,after tabs inputs rom out H J M,
    cheap_seq (@scan_cheap _ _ _ _) (@scan_cheap _ _ _ _)⟩

/-- Every packed batch is scanned once even when the earlier terrain, matcher
or static donor bytes carry an invalid code. Only the protected layout is used. -/
theorem phase_any (s : DepotRAM.Shape) (t : Tables6) (f : Fields) (rom : Banks) (out H J M w : ℕ)
    (fit : FitsInputs s t f M rom.source.base w) (finish : Fits rom (totalBits s) (outputBits s) M H J w out)
    (m : Memory w) : (phase t f rom out H J M w).Runs m := by
  let n:=H*chunks J M
  let mid:=ProtocolRAM.image rom.source.base n (gather t f) m
  have top : rom.source.base+n≤out := (Nat.add_le_add_left finish.srcSize _).trans finish.source.2.2
  have raw : (gather t f).Fits w rom.source.base:=⟨fit.final.apply,fit.final.right,fit.final.shift,fit.final.left⟩
  have words : (lookup rom).Fits w out := by simp [lookup,ProtocolRAM.Expr.Fits,finish.source,finish.mask,finish.dictionary]
  have first:=@scan_exec w rom.source.base n (gather t f) m raw (top.trans_lt (by have:=finish.output;omega))
  have second:=@scan_exec w out n (lookup rom) mid words finish.output
  have cost : 4+n*(2*(lookup rom).work+4)=4+44*n := by rw [lookup_work];ring
  rw [cost] at second
  intro P R K mach pc reg pub exit rom₀ advice cfg raw₀ enter same
  exact Procedure.Exec.then first second mach pc reg pub exit rom₀ advice cfg raw₀ enter same

end Hierarchy.DescentRawCablePanel.DepotRAM

end OAI
