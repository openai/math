import OAI.Hierarchy.ProtocolRAMNativeReserveSink
import OAI.Hierarchy.ProtocolRAMReserveReconciliation
import OAI.Hierarchy.ProtocolRAMCalendarBootLayout
import OAI.Hierarchy.ProtocolRAMCalendarInstalled
import OAI.Hierarchy.ProtocolRAMCalendarDepletedSink

namespace OAI
/-! # The installed calendar and terminal reporter from a single finite private header -/

namespace Hierarchy.ProtocolRAM.Calendar

open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.Native AdaptiveProbe
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators

noncomputable section
variable {w r edges : ℕ} {I J : Type*} [Fintype I] [Fintype J]
variable {core : I→List (Fin edges)} {center : J→List (Fin edges)}

namespace Sink

/-- The actual rows published after installing the remaining stock on the prescribed routes. -/
def terminalRows (s : Sink r edges) (m : Memory w) (e : Fin r≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→ℕ) : Fin edges→ProtocolRAMEmit.Row :=
  reportedRows [] (RouteSettlement.fields s.banks s.geometry) (RouteSettlement.output s.banks s.source m e ci cj)

def terminalImage (s : Sink r edges) (m : Memory w) (e : Fin r≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→ℕ) :=
  (report s.table edges s.owners (RouteSettlement.fields s.banks s.geometry)).apply
    (RouteSettlement.output s.banks s.source m e ci cj)

omit [Fintype I] [Fintype J] in
theorem output_eq_emitted (s : Sink r edges) (m : Memory w) (e : Fin r≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→ℕ) :
    s.output m e ci cj=ProtocolRAMEmit.emitted s.destination (s.terminalRows m e ci cj) (s.terminalImage m e ci cj) := rfl

theorem terminal_width (s : Sink r edges) (m : Memory w) (e : Fin r≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→ℕ) (i : Fin edges) (fit : edges≤ s.banks.width.size) (bound : edges≤2^w)
    (space : s.banks.width.base+edges≤ s.source)
    (room : (m (s.banks.width.base+i.val)).val +
      (routeLoad core (fun j=>RouteSettlement.actual s.banks.stock m (ci j)) i+
       routeLoad center (fun j=>RouteSettlement.actual s.banks.reserved m (cj j)-
         RouteSettlement.actual s.banks.used m (cj j)) i)<2^w) :
    (s.terminalRows m e ci cj i).width =
      (m (s.banks.width.base+i.val)).val+routeLoad core (fun j=>RouteSettlement.actual s.banks.stock m (ci j)) i+
      routeLoad center (fun j=>RouteSettlement.actual s.banks.reserved m (cj j)-RouteSettlement.actual s.banks.used m (cj j)) i :=
  RouteSettlement.reported_width s.banks s.source m e ci cj s.geometry i fit bound space room

omit [Fintype I] [Fintype J] in
theorem terminal_field (s : Sink r edges) (m : Memory w) (e : Fin r≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→ℕ) (i : Fin edges) (j : Fin 7) (other : j≠4)
    (fits : (s.geometry j).Fits w s.banks.width.base) (space : s.banks.width.base+edges≤ s.source) :
    (s.terminalRows m e ci cj i).field j=((s.geometry j).eval m (i.val:Word w)).val :=
  RouteSettlement.geometry_read s.banks s.source m e ci cj s.geometry i j other fits space

omit [Fintype I] [Fintype J] in
theorem terminal_words (s : Sink r edges) (m : Memory w) (e : Fin r≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→ℕ) (i : Fin edges) (j : Fin 3) :
    let out := s.output m e ci cj
    let row := s.terminalRows m e ci cj i
    out (s.destination+3*i.val+j.val)=(row.field (ProtocolRAMEmit.endpointFields j):Word w) ∧
    out (s.destination+3*edges+3*i.val+j.val)=(row.field (ProtocolRAMEmit.metricFields j):Word w) ∧
    out (s.destination+6*edges+3*i.val+j.val)=(row.field (ProtocolRAMEmit.gateFields j):Word w) :=
  ProtocolRAMEmit.emitted_read s.destination (s.terminalRows m e ci cj) (s.terminalImage m e ci cj) i j

end Sink



namespace Whole
variable {z d k q goods : ℕ}
variable (c : Mesh) (finish : ℝ) (prices : PhasePrice)
variable (format : Attempt→Format z d k q goods) (feeds : Boundary→List CommodityColumn)

def attempts := (events c).filterMap fun
  | .attempt a => some a
  | .feed _ => none

/-- Every installed purchase uses its actual time, signed price, sampler and stock source.
Feed boundaries require no extra threshold or sampler table. -/
def markets (i : Fin (attempts c).length) : Market z d k :=
  let a := (attempts c)[i.val]
  (format a).atTime c finish prices a

theorem market_at {a : Attempt} (occurs : Event.attempt a∈events c) :
    ∃ i : Fin (attempts c).length, markets c finish prices format i=(format a).atTime c finish prices a := by
  have member : a∈attempts c := List.mem_filterMap.mpr ⟨.attempt a,occurs,rfl⟩
  obtain ⟨i,hit⟩ := List.mem_iff_get.mp member
  exact ⟨i,congrArg (fun a=>(format a).atTime c finish prices a) hit⟩

local notation "C" => installed c finish prices format feeds
local notation "V" => markets c finish prices format
local notation "W" => wordBits z d copies

def program (flag : ℕ) (s : Sink r edges) := (subdivisionProgram z d).seq (complete C flag s)

def ticks (s : Sink r edges) := subdivisionConstant d*2^z+(checkedCost C+s.clock)

theorem cheap (flag : ℕ) (s : Sink r edges) : CheapCode (program c finish prices format feeds flag s) :=
  @cheap_seq W (subdivisionProgram z d) (complete C flag s)
    (subdivision_cheap z d) (complete_cheap C flag s)

theorem program_text (flag : ℕ) (s : Sink r edges) :
    text (program c finish prices format feeds flag s) =
      text (subdivisionProgram z d)+(15+((events (C).mesh).map (eventText C)).sum+
        rowText (historyFlag C (events (C).mesh))+sinkText s) := by
  rw [program,text_seq,text_complete]

theorem text_bound (flag : ℕ) (s : Sink r edges) :
    text (program c finish prices format feeds flag s) ≤
      (53+15000*rounds d)*2^z+(15+((events (C).mesh).map (eventText C)).sum+
        rowText (historyFlag C (events (C).mesh))+sinkText s) := by
  rw [program_text]
  exact Nat.add_le_add_right (subdivision_program_size z d) _

omit [Fintype I] [Fintype J] in
/-- The whole native procedure maps the genuine finite header to precisely the three
emitted terminal arrays. This is the prefix consumed by the pruning scan. -/
theorem exec {size : ℕ} (layout : Boot.Layout V size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (words : Boot.Tape z d)
    (authentic : ∀i : Fin (2^z),words i.val=((π i).val:Word W)) (flag : ℕ) (s : Sink r edges)
    (e : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ)
    (scheduled : mounted C (events (C).mesh) (Boot.booted V size words))
    (fit : (historyFlag C (events (C).mesh)).Fits W flag) (room : flag+1<2^W)
    (sink : s.Mounted (checkedOut C flag (Boot.booted V size words)) e ci cj) :
    (program c finish prices format feeds flag s).Exec
      (Computability.VPVNP.RAMMemory.initialMemory size (Boot.header V size words))
      (s.output (checkedOut C flag (Boot.booted V size words)) e ci cj)
      (ticks c finish prices format feeds s) :=
  Procedure.Exec.then (Boot.start V layout hd π words authentic).1
    (complete_exec C flag s e ci cj (Boot.booted V size words) scheduled fit room sink)

omit [Fintype I] [Fintype J] in
/-- The final return instruction reads the authentic pre-settlement admission flag
in the same memory that holds the reported records. -/
theorem run {size : ℕ} (layout : Boot.Layout V size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (words : Boot.Tape z d)
    (authentic : ∀i : Fin (2^z),words i.val=((π i).val:Word W)) (flag : ℕ) (s : Sink r edges)
    (e : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ) (state : Word W)
    (scheduled : mounted C (events (C).mesh) (Boot.booted V size words)) (ord : separated C (events (C).mesh))
    (fit : (historyFlag C (events (C).mesh)).Fits W flag) (room : flag+1<2^W)
    (sink : s.Mounted (checkedOut C flag (Boot.booted V size words)) e ci cj)
    (earlier : flag<s.banks.width.base ∧ flag<s.table ∧ flag<s.destination) :
    let initial := Computability.VPVNP.RAMMemory.initialMemory size (Boot.header V size words)
    let M := machine (program c finish prices format feeds flag s) (flag:Word W)
    let out := s.output (checkedOut C flag (Boot.booted V size words)) e ci cj
    ∃ t≤ticks c finish prices format feeds s+2, ∃ term,
      advance M.program t (M.program.start state) initial=some (term,out) ∧
      M.program.step term=.finish (some (out flag)) ∧
      (out flag=0 ↔ admissible C (events (C).mesh) (Boot.booted V size words)) := by
  dsimp only
  let pre := checkedOut C flag (Boot.booted V size words)
  let out := s.output pre e ci cj
  obtain ⟨t,ht,term,ran,halt⟩ := machine_run (program c finish prices format feeds flag s)
    (flag:Word W) state (Boot.initial V size words) out _ (exec c finish prices format feeds
      layout hd π words authentic flag s e ci cj scheduled fit room sink)
  rw [Fin.val_cast_of_lt (by omega : flag<2^W)] at halt
  refine ⟨t,ht,term,ran,halt,?_⟩
  rw [s.frame pre e ci cj flag earlier.1 earlier.2.1 earlier.2.2 sink.sourceRoom]
  exact checked_read C flag _ scheduled ord (by have := sink.wide; omega)


omit [Fintype I] [Fintype J] in
/-- Construct the reserve and final reporter inputs from the actual archived owner
and debit words of each chronological event. Injectivity is local to one event;
the same resource can receive one debit in each of the different events. -/
theorem Reconciliation.of_history {slots count stages fuel payload : ℕ}
    (s : Sink r edges) (a : ReserveUse.Archive) (m : Memory w)
    (rows : Fin stages→Type*) [∀t,Fintype (rows t)] (owner : ∀t,rows t↪Fin count)
    (units : ∀t,rows t→ℕ) (rank : (Σ t,rows t)≃Fin slots)
    (e : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→Fin count)
    (ports : s.Before m e ci (fun j=>(cj j).val))
    (ordered : s.banks.reserved.base+count≤ s.banks.used.base)
    (scratch : s.banks.used.base+count≤a.scratch) (end_ : a.scratch+2*slots<2^w)
    (refs : (ReserveUse.word a s.banks).Fits w s.banks.reserved.base)
    (kind : ∀i : Fin slots, a.kind.read m ((2*i.val:ℕ):Word w)=0 ∧
      a.kind.read m ((2*i.val+1:ℕ):Word w)≠0)
    (ids : ∀i : Fin slots,a.history.read m (a.pointer.read m ((2*i.val:ℕ):Word w))=
      ((owner (rank.symm i).1 (rank.symm i).2).val:Word w))
    (debits : ∀i : Fin slots,a.history.read m (a.pointer.read m ((2*i.val+1:ℕ):Word w))=
      (units (rank.symm i).1 (rank.symm i).2:Word w))
    (usedSize : count≤ s.banks.used.size) (reserveSize : count≤ s.banks.reserved.size)
    (elapsed : stages≤fuel) (bounded : ∀ t v,units t v≤payload) (width : fuel*payload<2^w) :
    Reconciliation s a (fuel*payload) (fun i=>owner (rank.symm i).1 (rank.symm i).2)
      (fun i=>units (rank.symm i).1 (rank.symm i).2) e ci cj m :=
  ⟨⟨ordered,scratch,end_,refs,ReserveUse.loaded_of_archive a s.banks _ _ m kind ids debits⟩,
    ports,usedSize,reserveSize,ReserveUse.funded_history rows owner units rank elapsed bounded,width⟩

omit [Fintype I] [Fintype J] in
theorem Reconciliation.of_padded_history {slots count stages fuel payload : ℕ}
    (s : Sink r edges) (a : ReserveUse.Archive) (m : Memory w)
    (rows : Fin stages→Type*) [∀t,Fintype (rows t)] (owner : ∀t,rows t→Fin count)
    (units : ∀t,rows t→ℕ) (rank : (Σ t,rows t)≃Fin slots)
    (e : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→Fin count)
    (ports : s.Before m e ci (fun j=>(cj j).val))
    (ordered : s.banks.reserved.base+count≤ s.banks.used.base)
    (scratch : s.banks.used.base+count≤a.scratch) (end_ : a.scratch+2*slots<2^w)
    (refs : (ReserveUse.word a s.banks).Fits w s.banks.reserved.base)
    (kind : ∀i : Fin slots, a.kind.read m ((2*i.val:ℕ):Word w)=0 ∧
      a.kind.read m ((2*i.val+1:ℕ):Word w)≠0)
    (ids : ∀i : Fin slots,a.history.read m (a.pointer.read m ((2*i.val:ℕ):Word w))=
      ((owner (rank.symm i).1 (rank.symm i).2).val:Word w))
    (debits : ∀i : Fin slots,a.history.read m (a.pointer.read m ((2*i.val+1:ℕ):Word w))=
      (units (rank.symm i).1 (rank.symm i).2:Word w))
    (usedSize : count≤ s.banks.used.size) (reserveSize : count≤ s.banks.reserved.size)
    (elapsed : stages≤fuel) (bounded : ∀ t v,units t v≤payload) (positive : ∀ t i j, 0<units t i → 0<units t j → owner t i=owner t j → i=j)
    (width : fuel*payload<2^w) :
    Reconciliation s a (fuel*payload) (fun i=>owner (rank.symm i).1 (rank.symm i).2)
      (fun i=>units (rank.symm i).1 (rank.symm i).2) e ci cj m :=
  ⟨⟨ordered,scratch,end_,refs,ReserveUse.loaded_of_archive a s.banks _ _ m kind ids debits⟩,
    ports,usedSize,reserveSize,ReserveUse.funded_padded rows owner units rank elapsed bounded positive,width⟩

namespace Controller

variable {jobs : ℕ}

def program (z d : ℕ) (ctl : Chart (wordBits z d copies) q goods) (flag : ℕ) (s : Sink r edges) (a : ReserveUse.Archive) (count n reserve : ℕ) :=
  (subdivisionProgram z d).seq (reconcile ctl flag s a count n reserve)

def ticks (z d : ℕ) (ctl : Chart (wordBits z d copies) q goods) (s : Sink r edges) (count n : ℕ) :=
  subdivisionConstant d*2^z+((checkedCost ctl+(19+12*count+160*n))+s.clock)

theorem cheap (ctl : Chart W q goods) (flag : ℕ) (s : Sink r edges) (a : ReserveUse.Archive) (count n reserve : ℕ) :
    CheapCode (program z d ctl flag s a count n reserve) :=
  @cheap_seq W (subdivisionProgram z d) (reconcile ctl flag s a count n reserve)
    (subdivision_cheap z d) (reconcile_cheap ctl flag s a count n reserve)

theorem text_eq (ctl : Chart W q goods) (flag : ℕ) (s : Sink r edges) (a : ReserveUse.Archive) (count n reserve : ℕ) :
    text (program z d ctl flag s a count n reserve) =
      text (subdivisionProgram z d)+
        (15+((events ctl.mesh).map (eventText ctl)).sum+rowText (historyFlag ctl (events ctl.mesh))+
        (listText (ReserveUse.columns a s.banks count n reserve)+22)+sinkText s) := by
  have scatter : text (ProtocolRAMWeightedScatter.program W a.scratch n)=22 := rfl
  simp only [program,reconcile,ReserveUse.native,text_seq,text_checked,text_passes,scatter,text_sink]

attribute [local irreducible] Procedure.Exec

omit [Fintype I] [Fintype J] in
theorem exec (v : Fin jobs → Market z d k) (ctl : Chart W q goods) {size n count : ℕ} (layout : Boot.Layout v size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (words : Boot.Tape z d)
    (authentic : ∀i : Fin (2^z),words i.val=((π i).val:Word W)) (flag : ℕ) (s : Sink r edges)
    (a : ReserveUse.Archive) (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    (e : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→Fin count)
    (scheduled : mounted ctl (events ctl.mesh) (Boot.booted v size words))
    (fit : (historyFlag ctl (events ctl.mesh)).Fits W flag) (room : flag+1<2^W)
    (actual : Reconciliation s a reserve site debit e ci cj (checkedOut ctl flag (Boot.booted v size words))) :
    let committed := ReserveUse.output a s.banks reserve site debit (checkedOut ctl flag (Boot.booted v size words))
    (program z d ctl flag s a count n reserve).Exec
      (Computability.VPVNP.RAMMemory.initialMemory size (Boot.header v size words))
      (s.output committed e ci (fun j=>(cj j).val))
      (ticks z d ctl s count n) := by
  dsimp only
  have sunk := actual.ports.mounted a reserve site debit actual.archive actual.usedSize actual.reserveSize
    actual.funded actual.word
  have tail := reconcile_exec ctl flag s a reserve site debit e ci (fun j=>(cj j).val)
    (Boot.booted v size words) scheduled fit room actual.archive sunk
  rw [ReserveUse.clock_eq] at tail
  exact Procedure.Exec.then (Boot.start v layout hd π words authentic).1 tail

omit [Fintype I] [Fintype J] in
theorem run (v : Fin jobs → Market z d k) (ctl : Chart W q goods) {size n count : ℕ} (layout : Boot.Layout v size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (words : Boot.Tape z d)
    (authentic : ∀i : Fin (2^z),words i.val=((π i).val:Word W)) (flag : ℕ) (s : Sink r edges)
    (a : ReserveUse.Archive) (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    (e : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→Fin count) (state : Word W)
    (scheduled : mounted ctl (events ctl.mesh) (Boot.booted v size words)) (ord : separated ctl (events ctl.mesh))
    (fit : (historyFlag ctl (events ctl.mesh)).Fits W flag) (room : flag+1<2^W)
    (actual : Reconciliation s a reserve site debit e ci cj (checkedOut ctl flag (Boot.booted v size words)))
    (below : flag<s.banks.reserved.base ∧ flag<s.banks.used.base ∧ flag<a.scratch ∧
      flag<s.banks.width.base ∧ flag<s.table ∧ flag<s.destination) :
    let initial := Computability.VPVNP.RAMMemory.initialMemory size (Boot.header v size words)
    let committed := ReserveUse.output a s.banks reserve site debit (checkedOut ctl flag (Boot.booted v size words))
    let M := machine (program z d ctl flag s a count n reserve) (flag:Word W)
    let out := s.output committed e ci (fun j=>(cj j).val)
    ∃ t≤ticks z d ctl s count n+2, ∃ term,
      advance M.program t (M.program.start state) initial=some (term,out) ∧
      M.program.step term=.finish (some (out flag)) ∧
      (out flag=0 ↔ admissible ctl (events ctl.mesh) (Boot.booted v size words)) := by
  dsimp only
  let committed := ReserveUse.output a s.banks reserve site debit (checkedOut ctl flag (Boot.booted v size words))
  let out := s.output committed e ci (fun j=>(cj j).val)
  have ranPrefix := exec v ctl layout hd π words authentic flag s a reserve site
    debit e ci cj scheduled fit room actual
  obtain ⟨t,ht,term,ran,halt⟩ := machine_run (program z d ctl flag s a count n reserve)
    (flag:Word W) state (Boot.initial v size words) out _ ranPrefix
  rw [Fin.val_cast_of_lt (by omega : flag<2^W)] at halt
  refine ⟨t,ht,term,ran,halt,?_⟩
  obtain ⟨res,used,scratch,width,table,dest⟩ := below
  rw [reconcile_frame ctl flag s a reserve site debit e ci (fun j=>(cj j).val) (Boot.booted v size words)
    flag res used scratch width table dest actual.ports.width]
  exact checked_read ctl flag _ scheduled ord (by have := actual.ports.wide; omega)

end Controller

def reconciled (flag : ℕ) (s : Sink r edges) (a : ReserveUse.Archive) (count n reserve : ℕ) :=
  (subdivisionProgram z d).seq (reconcile C flag s a count n reserve)

def reconciledTicks (s : Sink r edges) (count n : ℕ) :=
  subdivisionConstant d*2^z+((checkedCost C+(19+12*count+160*n))+s.clock)

theorem reconciled_cheap (flag : ℕ) (s : Sink r edges) (a : ReserveUse.Archive) (count n reserve : ℕ) :
    CheapCode (reconciled c finish prices format feeds flag s a count n reserve) :=
  @cheap_seq W (subdivisionProgram z d) (reconcile C flag s a count n reserve)
    (subdivision_cheap z d) (reconcile_cheap C flag s a count n reserve)

theorem reconciled_text (flag : ℕ) (s : Sink r edges) (a : ReserveUse.Archive) (count n reserve : ℕ) :
    text (reconciled c finish prices format feeds flag s a count n reserve) =
      text (subdivisionProgram z d)+
        (15+((events (C).mesh).map (eventText C)).sum+rowText (historyFlag C (events (C).mesh))+
        (listText (ReserveUse.columns a s.banks count n reserve)+22)+sinkText s) := by
  have scatter : text (ProtocolRAMWeightedScatter.program W a.scratch n)=22 := rfl
  simp only [reconciled,reconcile,ReserveUse.native,text_seq,text_checked,text_passes,scatter,text_sink]

omit [Fintype I] [Fintype J] in
theorem reconciled_exec {size n count : ℕ} (layout : Boot.Layout V size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (words : Boot.Tape z d)
    (authentic : ∀i : Fin (2^z),words i.val=((π i).val:Word W)) (flag : ℕ) (s : Sink r edges)
    (a : ReserveUse.Archive) (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    (e : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→Fin count)
    (scheduled : mounted C (events (C).mesh) (Boot.booted V size words))
    (fit : (historyFlag C (events (C).mesh)).Fits W flag) (room : flag+1<2^W)
    (actual : Reconciliation s a reserve site debit e ci cj (checkedOut C flag (Boot.booted V size words))) :
    let committed := ReserveUse.output a s.banks reserve site debit (checkedOut C flag (Boot.booted V size words))
    (reconciled c finish prices format feeds flag s a count n reserve).Exec
      (Computability.VPVNP.RAMMemory.initialMemory size (Boot.header V size words))
      (s.output committed e ci (fun j=>(cj j).val))
      (reconciledTicks c finish prices format feeds s count n) :=
  Controller.exec V C layout hd π words authentic flag s a reserve site debit e ci cj scheduled fit room actual

omit [Fintype I] [Fintype J] in
theorem reconciled_run {size n count : ℕ} (layout : Boot.Layout V size) (hd : 1≤d)
    (π : Equiv.Perm (Fin (2^z))) (words : Boot.Tape z d)
    (authentic : ∀i : Fin (2^z),words i.val=((π i).val:Word W)) (flag : ℕ) (s : Sink r edges)
    (a : ReserveUse.Archive) (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    (e : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→Fin count) (state : Word W)
    (scheduled : mounted C (events (C).mesh) (Boot.booted V size words)) (ord : separated C (events (C).mesh))
    (fit : (historyFlag C (events (C).mesh)).Fits W flag) (room : flag+1<2^W)
    (actual : Reconciliation s a reserve site debit e ci cj (checkedOut C flag (Boot.booted V size words)))
    (below : flag<s.banks.reserved.base ∧ flag<s.banks.used.base ∧ flag<a.scratch ∧
      flag<s.banks.width.base ∧ flag<s.table ∧ flag<s.destination) :
    let initial := Computability.VPVNP.RAMMemory.initialMemory size (Boot.header V size words)
    let committed := ReserveUse.output a s.banks reserve site debit (checkedOut C flag (Boot.booted V size words))
    let M := machine (reconciled c finish prices format feeds flag s a count n reserve) (flag:Word W)
    let out := s.output committed e ci (fun j=>(cj j).val)
    ∃ t≤reconciledTicks c finish prices format feeds s count n+2, ∃ term,
      advance M.program t (M.program.start state) initial=some (term,out) ∧
      M.program.step term=.finish (some (out flag)) ∧
      (out flag=0 ↔ admissible C (events (C).mesh) (Boot.booted V size words)) :=
  Controller.run V C layout hd π words authentic flag s a reserve site debit e ci cj state scheduled ord fit room actual below

end Whole
end
end Hierarchy.ProtocolRAM.Calendar

end OAI
