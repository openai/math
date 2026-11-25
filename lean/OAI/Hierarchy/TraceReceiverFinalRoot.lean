import OAI.Hierarchy.TraceReceiverMapReturn

namespace OAI
/-! # Actual compiled S12 records and S13 headers in the map writer's return state -/
noncomputable section
namespace Hierarchy.TraceReceiverForward
open ThreeFlat Diagonal PhysicalStage RAM
open Computability.VPVNP.BurstRAM PrivateRAM HistoryContraction TickTerminalRoot HistoryTerminalTape
open HistoryStageBody.Physical HistoryCompiledRows HistoryCommandTable TraceFactorReceiver
open scoped Fin.CommRing Classical BigOperators

variable {F Pins : Type} [Field F] [Fintype F] {w u p suffix n d l : ℕ}
variable (P : Source F Pins w u p suffix n d l)
set_option quotPrecheck false
local notation "W" => 64*w
local notation "B" => GridReceiverBanks.base w
local notation "D" => GridReceiverBanks.tasks w
local notation "S" => TickWorkspace.base u
local notation "count" => S 18+1
local notation "ranged" => TraceReceiverTasks.rangeImage (D).current count (GridReceiverBanks.commands w) 0 7 (P.images n)

theorem Source.final_root_bounds (i : Fin n) :
    let v:=P.value i
    let ord:=P.O.id (P.site i)
    S 12≤v.stream ∧ v.stream+4*v.net.cells≤S 13 ∧ S 13+8*ord+4≤S 14 := by
  intro v ord
  let z:=P.original i
  let V:=HistoryStageBody.Physical.volume u
  have it:=(P.O.ord (P.site i)).isLt
  have lim:=z.nodesFit
  have idx : ord<V:=by change P.O.layer.first+(P.O.ord (P.site i)).val<_;omega
  have room:=TraceReceiverRootRetain.slot_room z.large
  obtain ⟨a,b,c⟩:=address_limits (seedCount:=P.seeds) (i:=ord) (ext:=0) z.large (z.records i) (Nat.zero_le _)
  have once:=Nat.mul_le_mul_right (V^2) (show ord+1≤V by omega)
  have size : (ord+1)*V^2≤TickWorkspace.stride u:=by
    have cube:=room.2
    change V^3≤_ at cube
    nlinarith only [once,cube]
  have entryCount:=room.1
  have low:=TickWorkspace.apart (u:=u) (by decide : 12<13)
  have high:=TickWorkspace.apart (u:=u) (by decide : 13<14)
  have source : v.stream=streamAt u P.seeds ord:=z.stream
  change S 12≤v.stream ∧ v.stream+4*(P.value i).net.cells≤S 13 ∧ _
  rw [source]
  change (ord+1)*(volume u)^2 ≤ TickWorkspace.stride u at size
  change ord < volume u at idx
  have upper : endsAt u P.seeds ord ≤ S 12+(ord+1)*(volume u)^2 := by
    simpa only [Nat.add_zero] using c
  exact ⟨(Nat.le_add_right _ _).trans a,
    b.trans (upper.trans ((Nat.add_le_add_left size (S 12)).trans low)), by
      omega⟩

theorem Source.ranged_node (i : Fin n) :
    let v:=P.value i
    let node:=S 13+8*P.O.id (P.site i)
    readNode ranged (node:Word W)=⟨(v.stream:Word W),P.ports i,v.net.cells,v.net.internal⟩ := by
  intro v node
  have q:=P.original i
  have room:=(P.final_root_bounds i).2.2
  obtain ⟨bank,roof,gap⟩:=Gather.grid_window P.large P.age
  have higher:=TickWorkspace.apart (u:=u) (by decide : 14<45)
  have lower:=TickWorkspace.apart (u:=u) (by decide : 10<13)
  have frame (j : Fin 4) : ranged (node+j.val)=P.initial (node+j.val) := by
    have jj:=j.isLt
    refine (P.ranged_low _ (by change S 13+8*_+j.val<B;omega)).trans ?_
    apply P.final_observations.2.2.2.2
    exact Or.inl (Or.inl (by change S 10≤S 13+8*_+j.val ∧ S 13+8*_+j.val<S 14;omega))
  have chart:=q.cache.header
  have s:=congrArg HistoryStageRoot.Result.stream chart
  have p:=congrArg HistoryStageRoot.Result.pins chart
  have r:=congrArg HistoryStageRoot.Result.rows chart
  have b:=congrArg HistoryStageRoot.Result.bits chart
  have castWord {a : Word W} {v : ℕ} (eqn : a.val=v) : a=(v:Word W):=
    (Fin.cast_val_eq_self _).symm.trans (congrArg (fun x:ℕ=>(x:Word W)) eqn)
  apply Issued.read_node node v.stream (P.ports i) v.net.cells v.net.internal _ (by omega)
  · exact (show ranged node=P.initial node by simpa using frame 0).trans (castWord s)
  · exact (frame 1).trans (castWord (p.trans q.localPins))
  · exact (frame 2).trans (castWord r)
  · exact (frame 3).trans (castWord b)

theorem Source.final_rows (i : Fin n) :
    Records P.tag (P.value i).net (P.value i).stream (P.images n) := by
  intro r c
  have rt:=r.isLt
  have ct:=c.isLt
  have geom:=P.final_root_bounds i
  have older:=TickWorkspace.apart (u:=u) (by decide : 10<12)
  have newer:=TickWorkspace.apart (u:=u) (by decide : 13<14)
  exact (P.final_observations.2.2.2.2 _
    (Or.inl (Or.inl (by constructor <;> omega)))).trans ((P.original i).cache.rows r c)

end Hierarchy.TraceReceiverForward
end

end OAI
