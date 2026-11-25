import OAI.Hierarchy.TaggedWideControlDense
import OAI.Hierarchy.TaggedWideCPUBill

namespace OAI
/-! # Exact control-circuit price of a mounted RAM procedure -/
noncomputable section
namespace Hierarchy.Tagged.WideControlJoin
open ThreeFlat Routing Diagonal TraceRows TraceBanks
open ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory ProtocolRAM TaggedShorterControlHistory
open ProbeStage.Native
open scoped Classical BigOperators
namespace Gate

/-- Cost of the very CPU network present in the board, with its hidden workspace compacted. -/
theorem ofProcedure_bill {F : Type*} [Field F] {h W S f u : ℕ} (P : Procedure W) (ret start : Word W)
    (addr : Fin u→Word W) (m N : ℕ) (word : 3≤W+1) (labels : P.labels+3≤2^(W+1))
    (hs : S≤2^W) (clock : f+u≤2^(W+1)) (textBound : text P≤N) (cheap : CheapCode P)
    (width : W+1≤4*(h+1)) (height : m≤2*h) (fits : S+(f+u)≤2^m) :
    let G := ofProcedure P ret start addr m word labels hs clock
    (G.hardware (F:=F)).cells+(G.hardware (F:=F)).internal+Fintype.card G.Pin ≤
      20000000*2^m*(h+1)*(N+1)^2 :=
  native_control_bill_width (F:=F) P ret start N textBound cheap word width height labels
    (hs.trans (Nat.pow_le_pow_right (by decide) (Nat.le_succ _))) clock fits (wide ∘ addr)

/-- Observing the complete paid address range uses the original native bill with one
readout per address. Reading individual fields and flag bits adds no circuit cells. -/
theorem denseProcedure_bill {F : Type*} [Field F] {h W S f U : ℕ} (P : Procedure W) (ret start : Word W)
    (extent : U≤2^W) (m N : ℕ) (word : 3≤W+1) (labels : P.labels+3≤2^(W+1))
    (hs : S≤2^W) (clock : f+U≤2^(W+1)) (textBound : text P≤N) (cheap : CheapCode P)
    (width : W+1≤4*(h+1)) (height : m≤2*h) (fits : S+(f+U)≤2^m) :
    let G := denseProcedure P ret start extent m word labels hs clock
    (G.hardware (F:=F)).cells+(G.hardware (F:=F)).internal+Fintype.card G.Pin ≤
      20000000*2^m*(h+1)*(N+1)^2 :=
  ofProcedure_bill (F:=F) P ret start (denseAddr extent) m N word labels hs clock textBound cheap width height fits

end Gate
end Hierarchy.Tagged.WideControlJoin

end
end OAI
