import OAI.Hierarchy.TaggedWideMountedBill
import OAI.Hierarchy.TaggedWideControlJoin
import OAI.Hierarchy.TaggedWideControlDense
import OAI.Hierarchy.TaggedWideAdmission
import OAI.Hierarchy.TaggedWideCPUBill
import OAI.Hierarchy.TaggedWideHeader

namespace OAI
/-! # Actual calendar admission and paid bytecode on the dual CPU board -/

noncomputable section
namespace Hierarchy.Tagged.WideControlJoin
open ThreeFlat Routing Diagonal TraceRows TraceBanks
open ThreeFlat.RAM PhysicalProcedure
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMMemory
open AdaptiveProbe ProtocolRAM ProtocolRAM.Calendar ProbeStage ProbeStage.Native
open TaggedShorterControlHistory
open scoped Classical BigOperators Fin.CommRing



variable {F : Type*} [Field F] {z d k jobs q goods S clock m : ℕ}
local notation "W" => wordBits z d copies

/-- The first CPU is the genuine Boot→checked admission program on every authentic selector. -/
theorem boot_gate (C : Chart W q goods) (markets : Fin jobs→Market z d k) (flag : ℕ)
    (layout : Boot.Layout markets S) (hd : 1≤d) (π : Equiv.Perm (Fin (2^z)))
    (words : Boot.Tape z d) (auth : ∀i : Fin (2^z),words i.val=((π i).val:Word W))
    (ready : mounted C (events C.mesh) (Boot.booted markets S words)) (order : ProtocolRAM.Calendar.separated C (events C.mesh))
    (fit : (historyFlag C (events C.mesh)).Fits W flag) (room : flag+1<2^W)
    (st : Word W) (ww : 3≤W+1) (labels : (Boot.program C flag).labels+3≤2^(W+1))
    (hs : S≤2^W) (timed : clock+1≤2^(W+1)) (size : S+(clock+1)≤2^m) (record : W+1≤4*m)
    (fuel : subdivisionConstant d*2^z+checkedCost C+2<clock) :
    let A := Gate.ofProcedure (Boot.program C flag) (flag:Word W) st (fun _ : Fin 1=>(flag:Word W))
      m ww labels hs timed
    A.observed (Boot.header markets S words) (A.zeroFlag (F:=F) (0 : Fin 1)) =
      if admissible C (events C.mesh) (Boot.booted markets S words) then 1 else 0 := by
  intro A
  refine (prefix_observed (F:=F) A (Boot.header markets S words) (0 : Fin 1)).trans ?_
  exact observed_admission C markets flag layout hd π words auth ready order fit room st ww labels hs timed
    size record fuel

/-- Both CPU gates can share these same actual header bits, including the constant high bit. -/
theorem boot_header {V : Type} (markets : Fin jobs→Market z d k)
    (raw : (V→Bool)→Boot.Tape z d) (source : ℕ→Fin W→V⊕Bool)
    (reads : ∀ x a j,TraceWords.bits (raw x a) j=Sum.elim x id (source a j)) :
    ∃ wire : (Fin S × Fin (W+1))→V⊕Bool, ∀ x : V→Bool, ∀ i : Fin S × Fin (W+1),
      Sum.elim x id (wire i)=TraceWords.bits (wide (Boot.header markets S (raw x) i.1.val)) i.2 := by
  obtain ⟨wire,hw⟩ := WideHeader.cpu_wiring markets S raw source reads
  exact ⟨Function.uncurry wire,fun x i=>(hw x i.1 i.2).symm⟩

end Hierarchy.Tagged.WideControlJoin

end
end OAI
