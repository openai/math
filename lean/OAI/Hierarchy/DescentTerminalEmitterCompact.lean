import OAI.Hierarchy.DescentTerminalAddressBanks
import OAI.Hierarchy.DescentTerminalEmitterSpace
import OAI.Hierarchy.DescentTerminalEmitterAllocation
import OAI.Hierarchy.DescentTerminalAddressInput
import OAI.Hierarchy.DescentTerminalEmitterSources

namespace OAI
/-! # Terminal allocation with inherited physical banks and a single compact literal shelf -/
namespace Hierarchy.DescentTerminalEmitter.Compact
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentTerminalEmitterSources
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

def Earlier (base : ℕ) (c : Columns) : Prop := ∀j b,c j=.attained b → b.base+b.size≤base

/-- Only the purchased literal columns occupy the static shelf. Physical banks
written by a flight may instead reside at larger addresses. -/
theorem literal_end (base : ℕ) (c : Columns) (j : Fin 43) {n : ℕ} (isLiteral : c j=.literal n) :
    (view base c j).base+(view base c j).size≤ shelfEnd base c := by
  have final:=ProtocolRAMPortRanks.prefix_end (fun i=>size (c i)) Fin.val j
  change offsetAt (fun i=>size (c i)) j+size (c j)≤wordsBought c at final
  rw [isLiteral] at final
  simpa only [view,isLiteral,Bank.size,shelfEnd,size,Nat.add_assoc] using Nat.add_le_add_left final base

theorem sources_below (base : ℕ) (c : Columns) (prior : Earlier base c) (j : Fin 43) :
    (view base c j).base+(view base c j).size≤ shelfEnd base c := by
  cases h:c j with
  | attained b=>
    have below:=prior j b h
    simpa [view,h,shelfEnd] using below.trans (Nat.le_add_right base (wordsBought c))
  | literal n=>exact literal_end base c j h

theorem sources_at_flight (base : ℕ) (c : Columns) (flightWords : ℕ)
    (reached : Earlier (flightEnd base c flightWords) c) (j : Fin 43) :
    (view base c j).base+(view base c j).size≤flightEnd base c flightWords := by
  cases h:c j with
  | attained b=>simpa only [view,h] using reached j b h
  | literal n=>exact (literal_end base c j h).trans (Nat.le_add_right (shelfEnd base c) flightWords)

/-- No value can be passed to the literal table builder for an attained column,
whose corresponding finite word type is empty. -/
abbrev Literals (c : Columns) := (j : Fin 43) → Fin (size (c j)) → ℕ

variable (base : ℕ) (c : Columns) (fixed : Literals c)
local notation "flatWords" => columnData (fun j=>size (c j)) fixed

def install (w : ℕ) := DescentStaticWordColumn.program w base flatWords (wordsBought c)
def loaded {w : ℕ} (m : Memory w) := DescentStaticWordColumn.image base flatWords m (wordsBought c)

private theorem mount_facts {w : ℕ} (base count : ℕ) (data : ℕ → ℕ) (m : Memory w)
    (room : base+count < 2^w) :
    (DescentStaticWordColumn.program w base data count).Exec m
      (DescentStaticWordColumn.image base data m count) (4+10*count) ∧
    CheapCode (DescentStaticWordColumn.program w base data count) ∧
    (∀a,a<base ∨ base+count≤a → DescentStaticWordColumn.image base data m count a=m a) := by
  refine ⟨?_, ?_, ?_⟩
  · exact @DescentStaticWordColumn.mount w base count data m room
  · exact @DescentStaticWordColumn.cheap w base data count
  · exact @DescentStaticWordColumn.frame w base count data m

theorem load {w : ℕ} (m : Memory w) (room : shelfEnd base c<2^w) :
    (install base c fixed w).Exec m (loaded base c fixed m) (4+10*wordsBought c) ∧
    CheapCode (install base c fixed w) ∧
    (∀a,a<base ∨ shelfEnd base c≤a→loaded base c fixed m a=m a) :=
  @mount_facts w base (wordsBought c) flatWords m room

theorem labels (w : ℕ) : DescentStaticWordColumn.names (install base c fixed w)=15*(wordsBought c+1) :=
  DescentStaticWordColumn.names_mount ..

theorem bank_read {w : ℕ} (m : Memory w) (room : shelfEnd base c<2^w) (j : Fin 43) {n : ℕ}
    (isLiteral : c j=.literal n) (u : Fin (size (c j))) :
    (view base c j).read (loaded base c fixed m) (u.val:Word w)=(fixed j u:Word w) := by
  have final:=ProtocolRAMPortRanks.prefix_end (fun i=>size (c i)) Fin.val j
  change offsetAt (fun i=>size (c i)) j+size (c j)≤wordsBought c at final
  have lim:=u.isLt
  have addr:offsetAt (fun i=>size (c i)) j+u.val<wordsBought c:=by omega
  have word:u.val<2^w:=by unfold shelfEnd at room;omega
  have width:(view base c j).size=size (c j):=by simp [view,isLiteral,size,Bank.size]
  have start:(view base c j).base=base+offsetAt (fun i=>size (c i)) j:=by simp [view,isLiteral]
  rw [Bank.read,width,start,Fin.val_natCast,Nat.mod_eq_of_lt word,Nat.mod_eq_of_lt lim,Nat.add_assoc]
  have hit:=DescentStaticWordColumn.read base (wordsBought c) flatWords m addr
  simpa only [loaded,columnData_at] using hit

/-- An attained bank below or above the installed interval keeps its original
word at every query, including wrapped bank indices. -/
theorem attained_frame {w : ℕ} (m : Memory w) (room : shelfEnd base c<2^w)
    (j : Fin 43) {b : Bank} (was : c j=.attained b)
    (apart : b.base+b.size≤base ∨ shelfEnd base c≤b.base) (u : Word w) :
    (view base c j).read (loaded base c fixed m) u=b.read m u := by
  have lt:=Nat.mod_lt u.val (show 0<b.size from Nat.two_pow_pos _)
  have away : b.base+u.val%b.size<base ∨ shelfEnd base c≤b.base+u.val%b.size := by
    rcases apart with earlier|later <;> omega
  have frame := (load base c fixed m room).2.2 (b.base+u.val%b.size) away
  simpa only [view,was,Bank.read] using frame

theorem attained_read {w : ℕ} (m : Memory w) (room : shelfEnd base c<2^w) (prior : Earlier base c)
    (j : Fin 43) {b : Bank} (was : c j=.attained b) (u : Word w) :
    (view base c j).read (loaded base c fixed m) u=b.read m u :=
  attained_frame base c fixed m room j was (.inl (prior j b was)) u

variable (s : Shape) (i f flightWords : ℕ) (plane : DescentTerminalDataPlane.Layout)
    (ext : DescentTerminalDenseHeaderRAM.Layout) (blankFmt : ℕ)
local notation "start" => flightEnd base c flightWords
local notation "slabs" => Allocation.endAt s i f start

def layout := Allocation.layout s i f start (view base c) plane ext blankFmt

private theorem shelf_fits {w : ℕ} (bound : slabs<2^w) : shelfEnd base c<2^w :=
  (Nat.le_add_right (shelfEnd base c) flightWords).trans_lt
    ((Nat.le_add_right start (10*Allocation.slab s i f)).trans_lt bound)

/-- The logical emitter begins when all scheduled flights have finished. Their
newly issued index, width, event, and control banks fit anywhere below that point. -/
theorem flightAllocation {w : ℕ} (reached : Earlier start c) (fits : slabs<2^w)
    (flights : DescentTerminalDataPlane.Room s.plane plane w)
    (widths : DescentTerminalDenseHeaderRAM.Fits ext w s.plane.headerRows) :
    Room s (layout base c s i f flightWords plane ext blankFmt) w :=
  Allocation.inner_room s i f start (view base c) (sources_at_flight base c flightWords reached)
    fits plane ext blankFmt flights widths

theorem allocation {w : ℕ} (prior : Earlier base c) (fits : slabs<2^w)
    (flights : DescentTerminalDataPlane.Room s.plane plane w)
    (widths : DescentTerminalDenseHeaderRAM.Fits ext w s.plane.headerRows) :
    Room s (layout base c s i f flightWords plane ext blankFmt) w :=
  Allocation.inner_room s i f start (view base c)
    (fun j=>(sources_below base c prior j).trans (Nat.le_add_right _ _)) fits plane ext blankFmt flights widths

theorem event_bank {b : Bank} (actual : c 40=.attained b) :
    (layout base c s i f flightWords plane ext blankFmt).leaf.event=b := by
  change view base c 40=b
  simp [view,actual]

set_option maxHeartbeats 1600000 in
set_option maxRecDepth 4096 in
theorem readings_layout :
    let L:=layout base c s i f flightWords plane ext blankFmt
    readings L.indices.tapes L.formats.tapes L.book L.route L.leaf=view base c := by
  funext j
  fin_cases j <;> rfl

/-- The final absolute-address bound suffices for both the genuine terminal machine and
the one-time immutable installer. A branch may supply arbitrary attained memory on entry. -/
theorem certified {w:ℕ} (m:Memory w) (prior:Earlier base c) (bound:slabs<2^w)
    (flights:DescentTerminalDataPlane.Room s.plane plane w)
    (widths:DescentTerminalDenseHeaderRAM.Fits ext w s.plane.headerRows) :
    Room s (layout base c s i f flightWords plane ext blankFmt) w ∧
    (install base c fixed w).Exec m (loaded base c fixed m) (4+10*wordsBought c) ∧
    CheapCode (install base c fixed w) ∧
    DescentStaticWordColumn.names (install base c fixed w)=15*(wordsBought c+1) ∧
    (∀j b,c j=.attained b→∀u:Word w,(view base c j).read (loaded base c fixed m) u=b.read m u) ∧
    (∀j n,c j=.literal n→∀u:Fin (size (c j)),
      (view base c j).read (loaded base c fixed m) (u.val:Word w)=(fixed j u:Word w)) := by
  have room := shelf_fits base c s i f flightWords bound
  have run:=load base c fixed m room
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact allocation base c s i f flightWords plane ext blankFmt prior bound flights widths
  · exact @run.1
  · exact @run.2.1
  · exact labels base c fixed w
  · exact fun j _ was u=>attained_read base c fixed m room prior j was u
  · exact fun j _ was u=>bank_read base c fixed m room j was u

/-- Install the one literal shelf and reserve the emitter for the end of the flight.
Only an existing bank whose entry value is requested needs to be disjoint from the install.
Banks produced after this installation are subject solely to the attained-address limit. -/
theorem flightCertified {w:ℕ} (m:Memory w) (reached:Earlier start c) (bound:slabs<2^w)
    (flights:DescentTerminalDataPlane.Room s.plane plane w)
    (widths:DescentTerminalDenseHeaderRAM.Fits ext w s.plane.headerRows) :
    Room s (layout base c s i f flightWords plane ext blankFmt) w ∧
    (install base c fixed w).Exec m (loaded base c fixed m) (4+10*wordsBought c) ∧
    CheapCode (install base c fixed w) ∧
    DescentStaticWordColumn.names (install base c fixed w)=15*(wordsBought c+1) ∧
    (∀a,a<base ∨ shelfEnd base c≤a→loaded base c fixed m a=m a) ∧
    (∀j b,c j=.attained b→b.base+b.size≤base ∨ shelfEnd base c≤b.base→
      ∀u:Word w,(view base c j).read (loaded base c fixed m) u=b.read m u) ∧
    (∀j n,c j=.literal n→∀u:Fin (size (c j)),
      (view base c j).read (loaded base c fixed m) (u.val:Word w)=(fixed j u:Word w)) := by
  have room := shelf_fits base c s i f flightWords bound
  have run:=load base c fixed m room
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact flightAllocation base c s i f flightWords plane ext blankFmt reached bound flights widths
  · exact @run.1
  · exact @run.2.1
  · exact labels base c fixed w
  · exact run.2.2
  · exact fun j _ was apart u=>attained_frame base c fixed m room j was apart u
  · exact fun j _ was u=>bank_read base c fixed m room j was u

end
end Hierarchy.DescentTerminalEmitter.Compact

end OAI
