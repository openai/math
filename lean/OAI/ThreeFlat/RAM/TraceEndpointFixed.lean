import OAI.ThreeFlat.RAM.TraceEndpointROM
import OAI.ThreeFlat.RAM.TraceSuffixPublic

namespace OAI
/-! # Fixed public-word instruction stream for the genuinely paired H leaf -/

namespace ThreeFlat.RAM.TraceEndpointROM
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalPrelude
open Diagonal Diagonal.TraceBitHeader
open scoped Fin.CommRing

def fixed (W : ℕ) : Term W params 4 := program W (TraceSuffixOracle.fixedOracle W params oracleSlot)

theorem fixed_binds (W : ℕ) : (fixed W).binds≤1000234 := by
  have h := endpointProgram_size W rawSlot (TraceSuffixOracle.fixedOracle W params oracleSlot)
    (dimSlot 0) (dimSlot 1) (dimSlot 2)
  rw [TraceSuffixOracle.fixedOracle_binds_eq] at h
  exact h

variable {F : Type*} [Fintype F] [Field F] {w W p r k p' r' k' g : ℕ} (I : Image F w)

theorem fixed_source (tick : Machine w p r k) (H : Machine w p' r' k') (extra : Fin g→Bool)
    (room : SelfAdvice.Fits w p k p' k' g I.advice) (db pb tb codeBase : ℕ)
    (s : TraceBucketAtom.Layout) (original : Fin 1→Word W) (S T low : ℕ)
    (m : Memory W) (par : Fin I.parameters→Bool) (t : ℕ) (past : 2*I.endpointBits≤t) (hw : 0<w)
    (mount : TraceSuffixOracle.Mounted I (TraceSuffixOracle.locations w p k p' k' db pb tb codeBase)
      (fun j => (m j).val) (SelfAdvice.description tick H extra) par)
    (zero : (m 0).val=0) (one : (m 1).val=1)
    (fit : TraceSuffixOracle.Bounds W (TraceSuffixOracle.layout I
      (TraceSuffixOracle.locations w p k p' k' db pb tb codeBase)) t) :
    let o := TraceSuffixOracle.layout I (TraceSuffixOracle.locations w p k p' k' db pb tb codeBase)
    let pub := data s original (fun j => (o.fields j : Word W)) S T low
    (TraceSuffixOracle.fixedOracle W params oracleSlot).eval pub m (fun _ => (t : Word W)) =
      (publicAt I codeBase (NativeTrace.executable H) (SelfAdvice.description tick H extra) par t).toNat := by
  intro o pub
  exact TraceSuffixOracle.fixedOracle_eval_publicAt I tick H extra room db pb tb codeBase oracleSlot pub m par t past hw mount
    (fun j => data_oracle s original _ S T low j) zero one fit


end ThreeFlat.RAM.TraceEndpointROM

end OAI
