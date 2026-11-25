import OAI.Hierarchy.TraceReceiverFinalRoot

namespace OAI
/-! # The actual returned map/command memory opens the weighted field evaluator -/
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
local notation "G" => GridReceiverBanks.gap w
local notation "D" => GridReceiverBanks.tasks w
local notation "regCursor" => GridReceiverBanks.cursor w
local notation "cmd" => GridReceiverBanks.commands w
local notation "S" => TickWorkspace.base u
local notation "count" => S 18+1
local notation "ranged" => TraceReceiverTasks.rangeImage (D).current count cmd 0 7 (P.images n)
local notation "out" => Issued.image regCursor cmd (D).tasks n ranged
local notation "tag" => (fun t : (Fin 3→Bool)→F=>(Fintype.equivFin _ t).val)

omit [Field F] [Fintype F] in
private theorem same_network {a b : ℕ} (A : BitNetwork F a) (T : BitNetwork F b) (h : a=b)
    (ident : HEq A T) :
    A.cells=T.cells ∧ A.internal=T.internal ∧
    ∀ (wordWidth start : ℕ) (f : ((Fin 3→Bool)→F)→ℕ) (m : Memory wordWidth),Records f A start m→Records f T start m := by
  subst b
  cases eq_of_heq ident
  exact ⟨rfl,rfl,fun _ _ _ _ e=>e⟩

theorem Source.rows_room : 4*(∑ i,P.rows i)≤TickWorkspace.stride u := by
  by_cases empty : n=0
  · subst n;simp
  · let i : Fin n:=⟨0,by omega⟩
    let pub:=P.original i
    exact TraceReceiverRootBounds.total_room P.rows (by have:=pub.large;omega) pub.count pub.records

/-- The original compiled network of each chronological root is identified
by its heterogeneous assembly theorem. Pin addresses are exactly the physical
extension and incidence mapping used by the selected terminal writer. -/
theorem Source.prepared (nets : ∀ i,BitNetwork F (P.ports i)) (wires : ∀ i,Fin (P.ports i)→Fin p)
    (pin : Fin p→Bool) (H : ℕ) (ext : ∀ z,Fin (P.L.ext z)→Fin p)
    (fits : suffix+P.X.widthSum≤p) (canonical : P.tag=tag)
    (network : ∀ i,HEq (P.value i).net (nets i))
    (connected : ∀ (i : Fin n) (j : Fin (P.ports i)),wires i j=
      P.L.ports.physicalSource ext (TraceReceiverTerminalMap.shared P.X suffix fits) (P.site i) j)
    (origin : ∀ (i : Fin n) (k : Fin (P.L.ext (P.site i))),
      (P.value i).endpoint (k.cast (P.original i).external.symm)=2+(ext (P.site i) k).val)
    (fieldTables : ∀ f,tag f<2^W) (hidden : ∀ i,(nets i).internal≤G)
    (inputRoom : BitLayout.cellsBase p H≤S 9) (actualInput : ∀ a<BitLayout.cellsBase p H,
      P.initial a=TickMountedPins.memory pin a)
    (parent : readNode ranged ((D).parent:Word W)=⟨((S 9:ℕ):Word W),p,0,0⟩)
    (start : out regCursor=(cmd:Word W)) (last : out (regCursor+1)=((cmd+7*n:ℕ):Word W))
    (totalRows : out (S 18+2)=((∑ i,P.rows i:ℕ):Word W))
    (totalBits : out (S 18+3)=((∑ i,P.bits i:ℕ):Word W)) :
    Gather.Prepared nets (ctrl:=regCursor) (control:=S 18) (H:=H) (atCmd:=cmd) wires pin
      (S 9) (List.ofFn (Gather.rootSpan (S 9) fun i=>(nets i).cells)) out := by
  have N (i : Fin n):=same_network (P.value i).net (nets i) (P.original i).localPins (network i)
  have rows : P.rows=(fun i=>(nets i).cells):=funext (fun i=>(N i).1)
  have bits : P.bits=(fun i=>(nets i).internal):=funext (fun i=>(N i).2.1)
  have vol:=P.rows_room
  have jobs:=P.jobs
  obtain ⟨bank,roof,gap⟩:=Gather.grid_window P.large P.age
  have younger:=TickWorkspace.apart (u:=u) (by decide : 9<18)
  have bound:=TickWorkspace.apart (u:=u) (by decide : 18<45)
  have cursorEq : regCursor=B+32:=rfl
  have cmdEq : cmd=B+9*G:=rfl
  rw [rows] at vol
  apply Gather.prepared_of_issued nets wires pin (S 9) regCursor (S 18) H cmd out
    (by rw [cursorEq,cmdEq];omega) (by rw [cmdEq];omega) (by rw [cursorEq];omega)
    (by omega) (by rw [cursorEq];omega) inputRoom start last
  · constructor
    · simpa [forest,BitNetwork.restrictPins,rows] using totalRows
    · simpa [forest,BitNetwork.restrictPins,bits] using totalBits
  · exact fun a ha=>(P.returned_low a (ha.trans_le inputRoom)).trans (actualInput a ha)
  · intro i
    let v:=P.value i
    let node:=S 13+8*P.O.id (P.site i)
    have bound:=P.final_root_bounds i
    apply Gather.issued_terminal nets wires tag P.large P.age count (P.images n) i node v.stream
      jobs vol P.pinSum (hidden i) fieldTables bound.1 (by
        change (P.value i).stream+4*(nets i).cells≤S 14
        rw [←(N i).1]
        exact bound.2.1.trans ((Nat.le_add_right (S 13) (TickWorkspace.stride u)).trans
          (TickWorkspace.apart (u:=u) (by decide : 13<14))))
    · apply (P.ranged_task i).trans
      rw [←rows,←bits]
      exact P.task i
    · have eqn:=P.ranged_node i
      simpa only [(N i).1,(N i).2.1] using eqn
    · exact parent
    · exact (N i).2.2 W v.stream tag (P.images n) (canonical ▸ P.final_rows i)
    · intro j
      have read:=P.saved ext fits i j (origin i)
      rw [←connected] at read
      convert read using 1
      rw [Source.dst,scanned_at]

end Hierarchy.TraceReceiverForward
end

end OAI
