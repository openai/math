import OAI.Hierarchy.ProtocolRAMDateSpillRankRun

namespace OAI
/-! # Dated spill readings retained after the control and role passes -/
noncomputable section
open scoped Fin.CommRing
namespace Hierarchy.ProtocolRAM.DateSpill.RankTape
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard
open ProtocolRAMDateSpillRank ProtocolRAMTurnReplayed Calendar

variable {h d k K W : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
    {place : Site h d k→Fin K} {A : RankTape} {B : Mount (S:=S) π place A.edges}
    {o : CoreRoute.Orders h d k} {j : ℕ} {archive final : Memory W}

/-- Retaining the rank page also retains its original physical input and edge ranks. -/
theorem Observation.after (seen : Observation A B o j archive final) (out : Memory W)
    (keep : ∀x<(A.page j).offsetsStart,out x=final x) : Observation A B o j archive out := by
  obtain ⟨before,printed,rank,prior,amount,frame⟩:=seen.stored
  exact ⟨before,printed,rank,prior,amount,fun x hx=>(keep x hx).trans (frame x hx)⟩

/-- The intermediate source of the authentic single-date rank instructions contains
the same overflow word for every original commodity as the all-dates input. -/
theorem Observation.read_overflow (seen : Observation A B o j archive final)
    (core : A.core=coreCount o) (liveBank : (A.overflow j).Fits W A.first) :
    ∃before, RankRead B o (A.page j).rankStart (A.overflow j) before final ∧
      (∀i, RouteSettlement.actual (A.overflow j) before i=RouteSettlement.actual (A.overflow j) archive i) ∧
      (∀x<A.first,before x=archive x) ∧
      ∀i : Fin A.old,before ((A.page j).amount.base+i.val)=
        ((A.page j).term A.kind A.index).eval archive (i.val:Word W) := by
  obtain ⟨before,rank,prior,amount⟩:=Observation.read A B o seen core
  refine ⟨before,rank,?_,prior,amount⟩
  intro i
  exact congrArg Fin.val (prior _ ((Nat.add_lt_add_left
    (Nat.mod_lt (i:Word W).val liveBank.1) (A.overflow j).base).trans_le liveBank.2.2))

end Hierarchy.ProtocolRAM.DateSpill.RankTape
end

end OAI
