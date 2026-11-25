import OAI.Hierarchy.TraceReceiverMapReplay
import OAI.Hierarchy.TraceReceiverGatherRoom

namespace OAI
/-! # Native execution of all terminal maps in the single receiving machine -/
noncomputable section
namespace Hierarchy.TraceReceiverForward
open ThreeFlat Diagonal PhysicalStage RAM
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr DescriptorScan PhysicalProcedure HistoryContraction
open RAM.TickTerminalRoot RAM.HistoryTerminalTape HistoryStageBody.Physical
open scoped Classical Fin.CommRing BigOperators

variable {F Pins : Type} [Field F] [Fintype F] {w u p suffix n d l : ℕ}
variable (P : Source F Pins w u p suffix n d l)

theorem Source.countdown_val :
    (countdown (W:=64*w) P.arena).val=TickWorkspace.base u 18+4 := by
  obtain ⟨bank,roof,slots⟩:=TraceFactorReceiver.Gather.grid_window P.large P.age
  have below:=TickWorkspace.apart (u:=u) (by decide : 18<45)
  change ((TickWorkspace.base u 18+4 : ℕ) : Word (64*w)).val = TickWorkspace.base u 18+4
  exact Fin.val_cast_of_lt (by omega)

private theorem Source.raw_agrees (i : Fin n) :
    Reached u (GridReceiverBanks.base w) (GridReceiverBanks.tasks w).tasks n
      P.initial (decrease P.arena (P.images i.val)) := by
  intro a ha
  have hc : a≠TickWorkspace.base u 18+4 := by
    obtain ⟨bank,roof,slots⟩:=TraceFactorReceiver.Gather.grid_window P.large P.age
    have low:=TickWorkspace.apart (u:=u) (by decide : 14<18)
    have above:=TickWorkspace.apart (u:=u) (by decide : 18<45)
    rcases ha with (h|h|h)|h|h
    all_goals first | omega | (change GridReceiverBanks.base w+GridReceiverBanks.gap w≤a ∧ _ at h;omega)
  simp only [decrease,writeMemory,P.countdown_val,ite_eq_right hc]
  exact (P.invariant i.val i.isLt.le).same a ha

/-- All information used to mount a selected root is recovered from its true
task and its retained S13 record. This applies even to an empty local pin set. -/
theorem Source.bounds (i : Fin n) :
    TraceReceiverTasks.MapBounds P.arena (GridReceiverBanks.tasks w).tasks (GridReceiverBanks.mapHeader w)
      (P.dst i.val) (P.len i.val) (P.images i.val) := by
  let D:=GridReceiverBanks.tasks w
  let hdr:=GridReceiverBanks.mapHeader w
  let raw:=decrease P.arena (P.images i.val)
  let loc:=TickWorkspace.base u 13+8*P.O.id (P.site i)
  let addr:=((D.tasks+5*i.val:ℕ):Word (64*w))
  let pub:=P.original i
  have it:=i.isLt
  have hist:=P.invariant i.val it.le
  obtain ⟨rb,halves,compact,cache⟩:=P.iteration i
  obtain ⟨bank,roof,slots⟩:=TraceFactorReceiver.Gather.grid_window P.large P.age
  obtain ⟨hf,hb,df,sf,apart⟩:=TraceFactorReceiver.Gather.save_room (arity:=P.ports) P.large P.age i P.pinSum
  have countFit:=P.countFits
  have nj:=P.jobs
  have dEq : P.dst i.val=D.maps+Tree.before P.ports i := congrArg (D.maps+·) (scanned_at P.ports i)
  have lEq : P.len i.val=P.ports i := by simp [Source.len,extent,it]
  have ordv : raw (TickWorkspace.base u 18)=(i.val:Word (64*w)) := by
    have z : raw (TickWorkspace.base u 18)=P.images i.val (TickWorkspace.base u 18) := by
      simp only [raw,decrease,writeMemory,P.countdown_val,ite_eq_right (show TickWorkspace.base u 18≠TickWorkspace.base u 18+4 by omega)]
    exact z.trans (Fin.ext (hist.controls.ordinal.trans (Fin.val_cast_of_lt (it.trans countFit)).symm))
  have headWord : (P.arena.control:Word (64*w)).val=TickWorkspace.base u 18 := Fin.val_cast_of_lt (by
    have z:=P.page;change TickWorkspace.base u 18<_;omega)
  have taskId : TraceReceiverMapSave.taskWord D.tasks P.arena.control raw=addr := by
    simp only [TraceReceiverMapSave.taskWord,headWord,ordv,addr,Nat.cast_add,Nat.cast_mul,Nat.cast_ofNat]
  have word (j : Fin 5) : (addr+(j.val:Word (64*w))).val=D.tasks+5*i.val+j.val := by
    have fits : D.tasks+5*i.val+j.val < 2^(64*w) := by
      have z:=j.isLt
      change GridReceiverBanks.base w+GridReceiverBanks.gap w+5*i.val+j.val<_
      omega
    change (((D.tasks+5*i.val:ℕ):Word (64*w))+(j.val:Word (64*w))).val=_
    rw [←Nat.cast_add,Fin.val_cast_of_lt fits]
  have sameTask (j : Fin 5) : raw (addr+(j.val:Word (64*w))).val=P.initial (addr+(j.val:Word (64*w))).val := by
    rw [word]
    apply P.raw_agrees i _ (Or.inr (Or.inr ?_))
    change D.tasks ≤ D.tasks+5*i.val+j.val ∧ D.tasks+5*i.val+j.val < D.tasks+5*n
    have := j.isLt
    constructor <;> omega
  have task : HistoryCommandTable.readTask raw addr=HistoryCommandTable.readTask P.initial addr := by
    unfold HistoryCommandTable.readTask
    congr 1
    · exact sameTask 0
    · exact sameTask 1
    · exact sameTask 2
    · exact sameTask 3
    · exact sameTask 4
  have tchild : (HistoryCommandTable.readTask raw addr).child=(loc:Word (64*w)) :=
    congrArg HistoryCommandTable.Task.child (task.trans (P.task i))
  have tmap : (HistoryCommandTable.readTask raw addr).pinMap=(P.dst i.val:Word (64*w)) := by
    rw [dEq]
    exact congrArg HistoryCommandTable.Task.pinMap (task.trans (P.task i))
  have wide:=(TraceReceiverRootRetain.slot_room pub.large).1
  have nodeLimit:=pub.nodesFit
  have idx : P.O.id (P.site i)<volume u := by
    change P.O.layer.first+(P.O.ord (P.site i)).val<_
    have ji:=(P.O.ord (P.site i)).isLt
    omega
  have locRoom : loc+1<TickWorkspace.base u 14 := by
    have bas:=TickWorkspace.apart (u:=u) (by decide : 13<14)
    dsimp [loc];omega
  have fitLoc : loc+1<2^(64*w) := by
    have zz:=TickWorkspace.apart (u:=u) (by decide : 14<45);omega
  have rawChild : raw (D.tasks+5*i.val)=(loc:Word (64*w)) := by
    have read := tchild
    change raw (addr+0).val=_ at read
    simpa using ((congrArg raw (word 0)).symm.trans read)
  have rawPin : (HistoryCommandTable.readNode raw (loc:Word (64*w))).pins=(P.len i.val:Word (64*w)) := by
    change raw ((loc:Word (64*w))+1).val=_
    have plus : ((loc:Word (64*w))+1).val=loc+1 := by
      rw [←Nat.cast_one (R:=Word (64*w)),←Nat.cast_add,Fin.val_cast_of_lt fitLoc]
    rw [plus]
    have old := congrArg HistoryStageRoot.Result.pins pub.cache.header
    have addrLow:=TickWorkspace.apart (u:=u) (by decide : 10<13)
    have retain : raw (loc+1)=P.initial (loc+1) := P.raw_agrees i _ (Or.inl (Or.inl ⟨by dsimp [loc];omega,locRoom⟩))
    have value : (P.initial (loc+1)).val=P.ports i := old.trans pub.localPins
    rw [retain,lEq]
    exact (Fin.cast_val_eq_self _).symm.trans (congrArg (fun k:ℕ=>(k:Word (64*w))) value)
  refine ⟨hf,by simpa only [dEq] using hb,?_,?_,?_,?_,rb,?_,?_,?_⟩
  · simpa only [dEq,lEq] using df
  · rw [lEq]
    exact sf
  · apply Or.inl
    rw [dEq,lEq]
    exact apart
  · exact TraceFactorReceiver.Gather.save_sample_room P.large P.age i P.jobs raw loc ordv rawChild locRoom
  · intro j
    apply TraceReceiverRootBounds.kept_high compact P.page
    have ab:=TickWorkspace.apart (u:=u) (by decide : 18<45)
    change TickWorkspace.base u 18+4≤GridReceiverBanks.base w+24+j.val
    omega
  · change (HistoryCommandTable.readTask raw (TraceReceiverMapSave.taskWord D.tasks P.arena.control raw)).pinMap=_
    rw [taskId];exact tmap
  · change (HistoryCommandTable.readNode raw (HistoryCommandTable.readTask raw (TraceReceiverMapSave.taskWord D.tasks P.arena.control raw)).child).pins=_
    rw [taskId,tchild];exact rawPin

/-- Execute the receiver's actual finite program from its mounted input data;
the proof does not require a separate per-iteration bounds or counter witness. -/
theorem Source.run :
    let D:=GridReceiverBanks.tasks w
    (TraceReceiverTasks.maps (64*w) P.arena D.tasks (GridReceiverBanks.mapHeader w)).Spec (·=P.initial)
      (fun _ out=>out=P.images n)
      (4+7*n+∑ j ∈ Finset.range n,let k:=n-(j+1)
        TraceReceiverTasks.mapStepCost P.arena D.tasks (GridReceiverBanks.mapHeader w) (P.len k) (P.images k)) := by
  intro D
  obtain ⟨bank,roof,slots⟩:=TraceFactorReceiver.Gather.grid_window P.large P.age
  have below:=TickWorkspace.apart (u:=u) (by decide : 18<45)
  apply TraceReceiverTasks.maps_run
  · rw [P.countdown_val,P.counts.2.2.2.2,Fin.val_cast_of_lt P.countFits]
  · intro i hi
    exact P.bounds ⟨i,hi⟩
  · apply Or.inl
    rw [P.countdown_val]
    change TickWorkspace.base u 18+4<GridReceiverBanks.base w+24
    omega
  · intro i _
    apply Or.inl
    rw [P.countdown_val]
    change TickWorkspace.base u 18+4<GridReceiverBanks.base w+2*GridReceiverBanks.gap w+scanned P.ports i
    omega
  · intro i hi
    exact TraceReceiverRootBounds.counter (P.iteration ⟨i,hi⟩).2.2.1 P.page

/-- Counts and all archived, selected and task words after the last native
root, including the empty selected set. -/
theorem Source.final_observations :
    (P.images n (TickWorkspace.base u 18)).val=n ∧
    (P.images n (TickWorkspace.base u 18+1)).val=n ∧
    (P.images n (TickWorkspace.base u 18+2)).val=∑ i,P.rows i ∧
    (P.images n (TickWorkspace.base u 18+3)).val=∑ i,P.bits i ∧
    Reached u (GridReceiverBanks.base w) (GridReceiverBanks.tasks w).tasks n P.initial (P.images n) := by
  have h:=P.invariant n le_rfl
  exact ⟨h.controls.ordinal,h.controls.count,h.controls.rowsRead.trans (scanned_end P.rows),
    h.controls.bitsRead.trans (scanned_end P.bits),h.same⟩

/-- Every physical parent pin in the final task's persistent map equals
the source computed from the actual endpoint or incident wire. -/
theorem Source.saved (ext : ∀ z,Fin (P.L.ext z)→Fin p) (fits : suffix+P.X.widthSum≤p)
    (i : Fin n) (j : Fin (P.ports i))
    (origin : ∀ k : Fin (P.L.ext (P.site i)),
      (P.value i).endpoint (k.cast (P.original i).external.symm)=2+(ext (P.site i) k).val) :
    P.images n (P.dst i.val+j.val)=
      ((2+(P.L.ports.physicalSource ext (TraceReceiverTerminalMap.shared P.X suffix fits) (P.site i) j).val:ℕ):Word (64*w)) := by
  let D:=GridReceiverBanks.tasks w
  let hdr:=GridReceiverBanks.mapHeader w
  let a:=P.dst i.val+j.val
  let before:=P.images i.val
  let ini:=P.seeded i.val
  let after:=P.images (i.val+1)
  obtain ⟨_,halves,compact,cache⟩:=P.iteration i
  have ix:=P.index i (P.invariant i.val i.isLt.le)
  let pub:=P.original i
  have one := TraceReceiverRootBounds.cached_saved_pin compact P.page P.X P.L (P.site i) ext
    suffix (P.dst i.val) (P.O.id (P.site i)) fits halves (P.value i) P.tag ix cache pub.localPins pub.external origin j
  have ew : P.len i.val=P.ports i := by simp [Source.len,extent,i.isLt]
  have one' : after a=
      ((2+(P.L.ports.physicalSource ext (TraceReceiverTerminalMap.shared P.X suffix fits)
        (P.site i) j).val : ℕ) : Word (64*w)) := by
    change fillSegment (P.dst i.val) (P.len i.val)
      (fun z=>output P.arena ini (P.arena.map+(z-P.dst i.val))) (output P.arena ini) (P.dst i.val+j.val)=_
    rw [ew]
    exact one
  have hi:=i.isLt
  have ji:=j.isLt
  obtain ⟨bank,roof,slots⟩:=TraceFactorReceiver.Gather.grid_window P.large P.age
  have low := TickWorkspace.apart (u:=u) (by decide : 18<45)
  have big : TickWorkspace.base u 18+4<a := by
    change TickWorkspace.base u 18+4<GridReceiverBanks.base w+2*GridReceiverBanks.gap w+scanned P.ports i.val+j.val
    omega
  have header : hdr+3≤a := by
    change GridReceiverBanks.base w+24+3≤GridReceiverBanks.base w+2*GridReceiverBanks.gap w+scanned P.ports i.val+j.val
    omega
  have frame : P.images n a=after a := by
    apply TraceReceiverTasks.maps_frame P.arena D.tasks hdr P.dst P.len P.initial (by omega)
    · rw [P.countdown_val];omega
    · exact Or.inr header
    · intro k ik kn
      let t : Fin n:=⟨k,kn⟩
      have order : i<t := by change i.val<k;omega
      have sep := Tree.before_end_le P.ports order
      change a<P.dst k ∨ _
      apply Or.inl
      change D.maps+scanned P.ports i.val+j.val<D.maps+scanned P.ports t.val
      rw [scanned_at,scanned_at]
      omega
    · intro k ik kn
      exact TraceReceiverRootBounds.kept_high (P.iteration ⟨k,kn⟩).2.2.1 P.page a big.le
  exact frame.trans one'

end Hierarchy.TraceReceiverForward
end

end OAI
