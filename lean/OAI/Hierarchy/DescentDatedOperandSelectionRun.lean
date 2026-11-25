import OAI.Hierarchy.DescentDatedOperandMux
import OAI.Hierarchy.DescentOperandFamilyBook

namespace OAI
/-! # A dated operand selection computes its key from earlier physical words -/
namespace Hierarchy.DescentDatedOperandSelectionRun
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentSixParty.Chronology
open DescentPackedFlowBatch DescentDatedAddressBook ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {K n a : ℕ} (l : DescentDatedOperandMux.Layout)
variable (F : Fin K → (Fin n → Cell a) → Cell l.keyBits)
variable (which : Fin l.pages → Fin K) (args : Fin l.pages → Fin n → Expr) (head : Fin l.pages → Fin l.candidates → Expr)

def nextAddress (l : DescentDatedOperandMux.Layout) (K n a base : ℕ) :=
  DescentOperandFamilyBook.endAddress K n a l.lanes base

def endAddress (l : DescentDatedOperandMux.Layout) (K n a base : ℕ) :=
  DescentDatedOperandMux.endAddress l (nextAddress l K n a base)

def boot (base w : ℕ) : NativePhase w :=
  ⟨DescentOperandFamilyBook.program F l.lanes base w,DescentOperandFamilyBook.ticks K n a l.lanes,
    DescentOperandFamilyBook.image F l.lanes base,@DescentStaticWordColumn.cheap w base _ _⟩

def key (base : ℕ) (j : Fin l.pages) := DescentOperandFamilyBook.expr F l.lanes base (which j) (args j)

def phase (base w : ℕ) : NativePhase w :=
  (boot l F base w).seq
    (DescentDatedOperandMux.phase l (key l F which args base) head (nextAddress l K n a base) w)

def bank (l : DescentDatedOperandMux.Layout) (K n a base : ℕ) (j : Fin l.pages) :=
  DescentDatedOperandMux.bank l (nextAddress l K n a base) j

theorem span (base : ℕ) : endAddress l K n a base=base+endAddress l K n a 0 := by
  simp only [endAddress,nextAddress,DescentDatedOperandMux.endAddress,DescentDatedOperandMux.start,
    DescentOperandFamilyBook.endAddress,Nat.zero_add,Nat.add_assoc]

theorem reaches (base : ℕ) : nextAddress l K n a base≤endAddress l K n a base := by
  exact (Nat.le_add_right ..).trans (Nat.le_add_right ..)

variable {w base : ℕ} (fit : ∀j i,(args j i).Fits w base) (old : ∀j i,(head j i).Fits w base)
    (room : endAddress l K n a base<2^w)

include fit old room in
theorem any (m : Memory w) :
    (phase l F which args head base w).Runs m ∧
      ∀i,i<base ∨ endAddress l K n a base ≤ i → (phase l F which args head base w).image m i=m i := by
  let mid:=(boot l F base w).image m
  have space: nextAddress l K n a base<2^w:=(reaches l base).trans_lt room
  have warm:=DescentOperandFamilyBook.any F l.lanes base m space
  have step:=DescentDatedOperandMux.any l (key l F which args base) head
    (fun j=>DescentOperandFamilyBook.expr_fits F l.lanes base (which j) (args j) (fit j) space)
    (fun j i=>ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) (old j i)) room mid
  have warmRun:(boot l F base w).Runs m:=warm.1
  refine ⟨NativePhase.seq_runs _ _ m warmRun step.1,?_⟩
  intro i side
  cases side with
  | inl pre=>exact (step.2 i (.inl (pre.trans_le (Nat.le_add_right ..)))).trans (warm.2.2.1 i (.inl pre))
  | inr post=>exact (step.2 i (.inr post)).trans (warm.2.2.1 i (.inr ((reaches l base).trans post)))

include fit old room in
theorem emitted (m : Memory w) (dead : ∀j,F j (fun _=>0)=0)
    (x : Fin l.pages → Fin l.hosts → Fin l.groups → Fin n → Cell a)
    (y : Fin l.pages → Fin l.candidates → Fin l.hosts → Fin l.groups → Cell l.fieldBits)
    (operands : ∀j i,Source (args j i) (fun h g=>x j h g i) l.lanes m)
    (candidates : ∀j i,Source (head j i) (y j i) l.lanes m) (j : Fin l.pages) :
    Reads (bank l K n a base j) (fun h g=>DescentResetStemMux.pick (F (which j) (x j h g)) (fun i=>y j i h g))
      l.lanes ((phase l F which args head base w).image m) := by
  let mid:=(boot l F base w).image m
  have space: nextAddress l K n a base<2^w:=(reaches l base).trans_lt room
  have mount:=DescentOperandFamilyBook.any F l.lanes base m space
  have keys (p : Fin l.pages):=DescentOperandFamilyBook.issued F dead l.lanes base (which p) (args p) m (x p) (fit p)
    (operands p) space
  have retained (p : Fin l.pages) (i : Fin l.candidates) : Source (head p i) (y p i) l.lanes mid :=fun r=>
    (ProtocolRAM.eval_below _ _ m mid (old p i) (fun z hz=>mount.2.2.1 z (.inl hz))).trans (candidates p i r)
  exact DescentDatedOperandMux.emitted l (key l F which args base) head (fun p=>(keys p).1)
    (fun p i=>ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right ..) (old p i)) room
    mid (fun p h g=>F (which p) (x p h g)) y (fun p=>(keys p).2) retained j

theorem physical_cost (base w u v : ℕ) (inputs : ∀p i,(args p i).work≤u) (values : ∀p i,(head p i).work≤v) :
    let top:=nextAddress l K n a base
    let job:=DescentDatedOperandMux.job l (key l F which args base) head top
    let cost:=1+l.candidates*((14+n*(u+11))+v+22)
    let familyWords:=DescentOperandFamilyBook.words K n a l.lanes
    let tables:=DescentDatedOperandMux.tables l
    (phase l F which args head base w).ticks≤(4+10*familyWords)+(4+10*tables+job.clocks cost) ∧
      DescentStaticWordColumn.names (phase l F which args head base w).program≤
        15*(familyWords+1)+(15*(tables+1)+job.textSize cost) := by
  intro top job cost familyWords tables
  have meter:=DescentDatedOperandMux.physical_cost l (key l F which args base) head top w (14+n*(u+11)) v
    (fun p=>DescentOperandFamilyBook.expr_work F l.lanes base (which p) (args p) u (inputs p)) values
  refine ⟨Nat.add_le_add_left meter.1 _,?_⟩
  change DescentStaticWordColumn.names ((boot l F base w).program.seq _)≤_
  rw [DescentStaticWordColumn.names_seq]
  exact Nat.add_le_add (Book.names (DescentOperandFamilyBook.gates F) (DescentOperandFamilyBook.unit n a) l.lanes w base).le meter.2

end
end Hierarchy.DescentDatedOperandSelectionRun

end OAI
