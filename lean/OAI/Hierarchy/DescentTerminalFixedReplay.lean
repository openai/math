import OAI.Hierarchy.DescentExteriorSnapshotArea
import OAI.Hierarchy.DescentExteriorSnapshotSeed
import OAI.Hierarchy.DescentTerminalPacketHomeInstall
import OAI.Hierarchy.DescentTerminalCohortFrames
import OAI.Hierarchy.DescentTerminalExecUnique

namespace OAI
/-! The dated replay, stable frozen census and public-home scan on one original memory. -/
namespace Hierarchy.DescentTerminalFixedReplay
open DescentExteriorReplay DescentTerminalPacketHomeRAM ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical
noncomputable section
set_option quotPrecheck false

/-- The calendar, sizes and immutable initial vertex numbers determine every instruction. -/
structure Calendar (k : ℕ) where
  snapshots : Snapshots k
  age : ℕ
  frozenBits : ℕ
  cohortBits : ℕ
  ports : ℕ
  j : ℕ
  rest : ℕ
  kept : ℕ
  hosts : ℕ
  seed : Fin (ports*2^frozenBits) → ℕ

namespace Calendar
variable {k : ℕ} (C : Calendar k) (start censusAt : ℕ)
def cohorts := C.ports*2^C.frozenBits
def packets := C.ports*2^(C.j+C.rest)
def scratch := C.snapshots.scratchAt start C.frozenBits C.age
def packetStart := C.snapshots.freshAt start C.frozenBits C.cohorts C.age
def lastPage := C.snapshots.lastAt start C.frozenBits C.cohorts C.age
def homes := (Expansion.layout (C.packetStart start) C.packets (C.lastPage start)).dest
def packetEnd := Expansion.stop (C.packetStart start) C.packets
def stop := DescentTerminalCohortArena.stop censusAt C.frozenBits C.cohortBits C.cohorts C.hosts
variable {w : ℕ} (room : C.stop censusAt<2^w)
local notation "A" => C.snapshots
local notation "n" => C.cohorts
local notation "s" => C.scratch start
local notation "f" => C.frozenBits
local notation "p0" => C.packetStart start
local notation "last_" => C.lastPage start
local notation "hop_" => (A).hop start f s n
local notation "begin_" => ((A).program w start f C.age).seq (Snapshots.seedProgram w s C.seed)
local notation "steps_" => steps w n (schedule hop_ C.age)
local notation "sort_" => DescentTerminalCohortArena.machine censusAt f C.cohortBits n C.hosts room last_
local notation "homes_" => Expansion.fixedProgram w p0 C.ports C.j C.rest C.kept last_
local notation "fee" => DescentTerminalCohortArena.ticks censusAt f C.cohortBits n C.hosts room last_

def program : Procedure w := ((begin_).seq ((steps_).seq sort_)).seq homes_
def cost := ((A).clocks f C.age+(4+10*n)+(clocks n (schedule hop_ C.age)+fee))+(8+38*C.packets)

variable (ordered : C.packetEnd start≤censusAt) (positive : 0<C.hosts)
variable (rank : ∀t<C.age,∀b : Bank,C.snapshots.compact t=some b → b.Fits w (C.scratch start))

theorem addresses :
    start≤ s ∧ s≤p0 ∧ p0≤C.packetEnd start ∧ censusAt≤C.stop censusAt ∧
    (last_).base+(last_).size=p0 := by
  have first : start≤ s:=(A).start_mono start f (Nat.zero_le C.age)
  have middle : s≤p0:=Nat.le_add_right ..
  have end_ : p0≤C.packetEnd start:=by unfold packetEnd Expansion.stop;omega
  have sortStart : censusAt≤C.stop censusAt:=by
    unfold stop DescentTerminalCohortArena.stop DescentTerminalCohortArena.tallyBase
      DescentTerminalCohortArena.indexBase DescentTerminalPacketSlotRAM.out DescentTerminalCohortArena.order
    repeat' apply Nat.le_add_right_of_le
    exact Nat.le_refl _
  refine ⟨first,middle,end_,sortStart,?_⟩
  change s+C.age*Snapshots.stride n+Snapshots.stride n=s+(C.age+1)*Snapshots.stride n
  rw [Nat.succ_mul,Nat.add_assoc]

private theorem stage_outside (m : Memory w) {a : ℕ} (after : p0≤a) :
    stage hop_ n m C.age a=m a := by
  have all (t:ℕ) (live:t≤C.age) : stage hop_ n m t a=m a:=by
    induction t with
    | zero=>rfl
    | succ t ih =>
      have roof : s+(t+1)*Snapshots.stride n+Snapshots.stride n≤p0 := by
        change _≤ s+(C.age+1)*Snapshots.stride n
        rw [Nat.add_assoc,←Nat.succ_mul]
        exact Nat.add_le_add_left (Nat.mul_le_mul_right _ (Nat.succ_le_succ live)) _
      have enough : n≤Snapshots.stride n:=(Nat.le_succ _).trans (Nat.le_pow_clog (by decide) _)
      have eqn : (hop_ t).dest.base=s+(t+1)*Snapshots.stride n:=rfl
      change result n (hop_ t) _ a=m a
      unfold DescentExteriorReplay.result
      rw [ProtocolRAMGeneratedWrite.frame_image _ _ _ _ a (.inr (by rw [eqn];omega))]
      exact ih (by omega)
  exact all C.age le_rfl

include ordered positive rank in
set_option maxHeartbeats 1600000 in
set_option maxRecDepth 8000 in
/-- The exact instruction count and both frames apply also to arbitrary contents of the source tapes. -/
theorem execute (m : Memory w) :
    ∃out,(C.program start censusAt room).Exec m out (C.cost start censusAt room) ∧
      CheapCode (C.program start censusAt room) ∧
      ∀a,a<start ∨ C.stop censusAt≤a → out a=m a := by
  obtain ⟨start0,scratch0,packet0,census0,lastEnd⟩:=C.addresses start censusAt
  have source0 : p0<2^w:=(packet0.trans (ordered.trans census0)).trans_lt room
  have sizeN : n+1≤Snapshots.stride n:=Nat.le_pow_clog (by decide) _
  have initial : s+Snapshots.stride n≤p0 := by
    apply Nat.add_le_add_left
    exact Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have printed:=(A).run start f m C.age (scratch0.trans_lt source0)
  let lit:=(A).image start f m C.age
  let init:=Snapshots.seedImage s C.seed lit
  let traveled:=stage hop_ n init C.age
  have placed:=Snapshots.seed_run s C.seed lit (initial.trans_lt source0)
  have moves:=stage_control («n»:=n) hop_ C.age init ((A).rooms w start f s n C.age le_rfl source0 rank)
  have lastFit : (last_).Fits w censusAt:=by
    refine ⟨Nat.two_pow_pos _,?_,lastEnd.le.trans (packet0.trans ordered)⟩
    change Snapshots.stride n < 2^w;omega
  obtain ⟨sorted,runSort,cheapSort,sortFrame⟩:=DescentTerminalCohortArena.any_frame
    censusAt f C.cohortBits n C.hosts room last_ traveled positive lastFit
  let L:=Expansion.layout p0 C.packets last_
  let loaded:=DescentStaticWordColumn.image p0 (Expansion.calendarWord C.ports C.j C.rest C.kept) sorted C.packets
  let out:=DescentTerminalPacketHomeRAM.after L C.packets loaded
  have packetRoom:=Expansion.room («n»:=C.packets) (K:=0) (w:=w) p0 last_ lastEnd.le (Nat.zero_le _) (ordered.trans_lt (census0.trans_lt room))
  have padded : C.packets≤DescentTerminalPrimitiveArena.pad C.packets:=DescentTerminalPrimitiveArena.covered _
  have cap : p0+C.packets<2^w:=by
    have : p0+DescentTerminalPrimitiveArena.pad C.packets+DescentTerminalPrimitiveArena.pad C.packets≤censusAt:=ordered
    omega
  have indices : (DescentStaticWordColumn.program w p0
      (Expansion.calendarWord C.ports C.j C.rest C.kept) C.packets).Exec sorted loaded (4+10*C.packets) := by
    exact DescentStaticWordColumn.mount p0 C.packets _ sorted cap
  have looked:=DescentTerminalPacketHomeRAM.run («n»:=C.packets) (K:=0) L packetRoom loaded
  have runtime: (4+10*C.packets)+(4+28*C.packets)=8+38*C.packets:=by omega
  have homeRun : (homes_).Exec sorted out (8+38*C.packets) := by
    rw [←runtime]
    exact Procedure.Exec.then (by exact @indices) looked.1
  refine ⟨out,?_,?_,?_⟩
  · exact Procedure.Exec.then
      (Procedure.Exec.then (Procedure.Exec.then printed.1 placed.1) (Procedure.Exec.then moves.1 (by exact @runSort)))
      (by exact @homeRun)
  · have firstCheap : CheapCode begin_ :=
      @cheap_seq w ((A).program w start f C.age) (Snapshots.seedProgram w s C.seed) printed.2 placed.2.1
    have replayCheap : CheapCode ((steps_).seq sort_) :=
      @cheap_seq w steps_ sort_ moves.2 (by exact @cheapSort)
    have homeCheap : CheapCode homes_ :=
      @cheap_seq w (DescentStaticWordColumn.program w p0
        (Expansion.calendarWord C.ports C.j C.rest C.kept) C.packets)
        (DescentTerminalPacketHomeRAM.program L w C.packets)
        (DescentStaticWordColumn.cheap w p0 _ C.packets) looked.2
    exact @cheap_seq w ((begin_).seq ((steps_).seq sort_)) homes_
      (@cheap_seq w begin_ ((steps_).seq sort_) (by exact @firstCheap) (by exact @replayCheap))
      (by exact @homeCheap)
  · intro a outside
    have packetAway : a<p0 ∨ C.packetEnd start≤a:=by rcases outside with h|h <;> omega
    have sortAway : a<censusAt ∨ C.stop censusAt≤a:=by rcases outside with h|h <;> omega
    have e : C.packetEnd start=p0+DescentTerminalPrimitiveArena.pad C.packets+DescentTerminalPrimitiveArena.pad C.packets:=rfl
    have kept : out a=sorted a:=
      (DescentTerminalPacketHomeRAM.frame («n»:=C.packets) L loaded
        (by change a<p0+DescentTerminalPrimitiveArena.pad C.packets ∨ p0+DescentTerminalPrimitiveArena.pad C.packets+C.packets≤a; rcases packetAway with h|h <;> omega)).trans
      (DescentStaticWordColumn.frame p0 C.packets _ sorted a (by rcases packetAway with h|h <;> omega))
    rw [kept,sortFrame a sortAway]
    have fromReplay : traveled a=init a:=by
      rcases outside with low|high
      · exact (A).stage_frame start f s n init C.age a (low.trans_le start0)
      · exact C.stage_outside start init (by omega)
    have fromSeed : init a=lit a:=DescentStaticWordColumn.frame s n _ lit a
      (by rcases outside with low|high <;> omega)
    exact (fromReplay.trans fromSeed).trans ((A).image_frame start f m C.age a
      (by
        change a<start ∨ s≤a
        exact outside.imp_right (fun high => scratch0.trans (packet0.trans (ordered.trans (census0.trans high))))))

/-- The unique halt image of this fixed CPU. It is independent of the proof of numerical room. -/
def memory (m : Memory w) : Memory w :=
  if h : ∃out,(C.program start censusAt room).Exec m out (C.cost start censusAt room)
  then Classical.choose h else m

include ordered positive rank in
theorem exec_memory (m : Memory w) :
    (C.program start censusAt room).Exec m (C.memory start censusAt room m) (C.cost start censusAt room) ∧
    CheapCode (C.program start censusAt room) ∧
    ∀a,a<start ∨ C.stop censusAt≤a → C.memory start censusAt room m a=m a := by
  obtain ⟨out,run,cheap,frame⟩:=C.execute start censusAt room ordered positive rank m
  have saved : ∃o,(C.program start censusAt room).Exec m o (C.cost start censusAt room):=⟨out,run⟩
  have canonical : (C.program start censusAt room).Exec m (C.memory start censusAt room m) (C.cost start censusAt room):=by
    rw [memory, dite_eq_left saved]
    exact Classical.choose_spec saved
  have equal:=ProtocolRAM.exec_unique _ _ _ _ canonical run
  exact ⟨canonical,cheap,equal.symm ▸ frame⟩

theorem read_memory {m : Memory w} {Q : Memory w → Prop}
    (published : ∃o,(C.program start censusAt room).Exec m o (C.cost start censusAt room) ∧ Q o) :
    Q (C.memory start censusAt room m) := by
  obtain ⟨out,run,reads⟩:=published
  have saved : ∃o,(C.program start censusAt room).Exec m o (C.cost start censusAt room):=⟨out,run⟩
  unfold memory
  rw [dite_eq_left saved]
  exact (ProtocolRAM.exec_unique _ _ _ _ run (Classical.choose_spec saved)) ▸ reads


end Calendar
end
end Hierarchy.DescentTerminalFixedReplay

end OAI
