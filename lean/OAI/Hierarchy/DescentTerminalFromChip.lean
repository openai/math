import OAI.Hierarchy.DescentTerminalChipValidity
import OAI.Hierarchy.DescentTerminalFromRows

namespace OAI
/-! # From the reached terminal descriptor header to the writable host observation columns -/
namespace Hierarchy.DescentTerminalChipRuntime
open DescentTerminalRAM DescentTerminalReadout DescentTerminalPorts DescentTerminalHost
open DescentTerminalLast DescentTerminalChipPins DescentTerminalProposalCheck
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {A T I : Type} [Fintype I] {K W q p w slots bins rows word : ℕ}
local notation "N" => K*W
local notation "d" => q*(W*p)
local notation "Bits" => Inputs K W q p
local notation "Raw" => RowBit rows word→Bool
local notation "All" => Choice (A⊕Bits) rows word→Bool

structure Columns where
  seed : I→ℕ
  seedFlag : ℕ
  exteriorFlag : ℕ
  whole : Bank
  tail : Bank
  keyBits : ℕ

def Columns.tape (D : Columns (I:=I)) (P : Layout) («N» : ℕ) : Tape where
  whole:=D.whole
  tail:=D.tail
  keys:=⟨P.keys,D.keyBits⟩
  flags:=![⟨D.seedFlag,0⟩,⟨D.exteriorFlag,0⟩,⟨P.xCheck+«N»,0⟩,⟨P.yCheck+«N»,0⟩]

def erased (choice : All) : A→Bool := fun a=>choice (.inl (.inl a))
def proposal (choice : All) : Bits→Bool := fun b=>choice (.inl (.inr b))
def poolBits (choice : All) : Raw := fun b=>choice (.inr b)

variable (D : Columns (I:=I)) (P : Layout) (L : Banks)
  (rm : Room P L w (K*W) slots) (room : q*(W*p)≤w) (pos : 0<w)
  (old : (RowBit rows word→Bool)→(A→Bool)→Option T) (s : T→(RowBit rows word→Bool) → Content K W q p)
  (total : T→ℕ) (count : T→I→ℕ) (keyFor : T→(RowBit rows word→Bool)→Fin slots→Fin bins)
  (m : (Choice (A⊕Inputs K W q p) rows word→Bool)→Memory w)

def finalChoice (pay : Raw) (z : A⊕Bits→Bool) :=
  extend old (fun t x=>(s t x).witness room) pay z

theorem choice_once (oldOnce : ∀raw t,∃!z,old raw z=some t) (raw : Raw) (t : T) :
    ∃!z,finalChoice room old s raw z=some t := extend_unique _ _ oldOnce raw t

/-- Actual inputs that precede the fixed terminal RAM scans. The selected
control branch supplies literal format/gate/source words. For a failed
prefix only its sticky observation matters. -/
structure Current : Prop where
  seedLow : ∀i,D.seed i<P.first
  totalLow : D.whole.base<P.first ∧ D.tail.base<P.first
  flagLow : D.seedFlag<P.first ∧ D.exteriorFlag<P.first
  admitted : ∀z,(m z D.seedFlag=0 ∧ m z D.exteriorFlag=0) ↔
    ∃t,old (poolBits z) (erased z)=some t
  seed : ∀z t,old (poolBits z) (erased z)=some t→∀i,m z (D.seed i)=(count t i:Word w)
  mass : ∀z t,old (poolBits z) (erased z)=some t→
    (m z D.whole.base).val=total t/word ∧ (m z D.tail.base).val=total t%word
  observed : ∀z t,old (poolBits z) (erased z)=some t→Chips P L (s t (poolBits z)) (m z) (proposal z)
  scalar : ∀z t,old (poolBits z) (erased z)=some t→
    (s t (poolBits z)).accepts w (proposal z)→∀i,(key L).eval (m z) (i.val:Word w)=((keyFor t (poolBits z) i).val:Word w)

def finished (z : All) := finalMem P L N slots (m z)

variable (h : Current D P L old s total count keyFor m)
include rm pos h in
omit [Fintype I] in
theorem input_cells :
    InputCells (D.tape P N) (finished (slots:=slots) P L m) (finalChoice room old s) total count keyFor D.seed := by
  constructor
  · intro z t x seen i
    obtain ⟨ok,_⟩:=(extend_iff ..).1 seen
    exact (lower P L (m (Sum.elim z x)) (h.seedLow i)).trans (h.seed (Sum.elim z x) t ok i)
  · intro z t x seen
    obtain ⟨ok,_⟩:=(extend_iff ..).1 seen
    exact (congrArg Fin.val (lower P L (m (Sum.elim z x)) h.totalLow.1)).trans (h.mass (Sum.elim z x) t ok).1
  · intro z t x seen
    obtain ⟨ok,_⟩:=(extend_iff ..).1 seen
    exact (congrArg Fin.val (lower P L (m (Sum.elim z x)) h.totalLow.2)).trans (h.mass (Sum.elim z x) t ok).2
  · intro z t x seen i
    obtain ⟨ok,valid⟩:=(extend_iff ..).1 seen
    exact (key_read P L rm (m (Sum.elim z x)) i).trans
      (h.scalar (Sum.elim z x) t ok (((s t x).valid_iff room _).2 valid) i)
  · intro z x
    let b:All:=Sum.elim z x
    let out:=finished (slots:=slots) P L m b
    change (∀i:Fin 4,out ((D.tape P N).flags i).base=0) ↔ _
    have all : (∀i:Fin 4,out ((D.tape P N).flags i).base=0) ↔
        (m b D.seedFlag=0 ∧ m b D.exteriorFlag=0) ∧ (out (P.xCheck+N)=0 ∧ out (P.yCheck+N)=0) := by
      have a : out D.seedFlag=m b D.seedFlag:=lower P L (m b) h.flagLow.1
      have e : out D.exteriorFlag=m b D.exteriorFlag:=lower P L (m b) h.flagLow.2
      constructor
      · intro q;exact ⟨⟨a.symm.trans (q 0),e.symm.trans (q 1)⟩,q 2,q 3⟩
      · rintro ⟨⟨u,v⟩,y,z⟩ i
        fin_cases i
        · exact a.trans u
        · exact e.trans v
        · exact y
        · exact z
    rw [all,h.admitted b]
    constructor
    · rintro ⟨⟨t,ok⟩,pair⟩
      have valid:=(witnessed P L (s t x) rm room pos (m b) (proposal b) (h.observed b t ok)).1 pair
      exact ⟨t,(extend_iff ..).2 ⟨ok,valid⟩⟩
    · rintro ⟨t,seen⟩
      obtain ⟨ok,valid⟩:=(extend_iff ..).1 seen
      exact ⟨⟨t,ok⟩,(witnessed P L (s t x) rm room pos (m b) (proposal b) (h.observed b t ok)).2 valid⟩

attribute [local irreducible] program clocks finalMem Procedure.seq

set_option maxHeartbeats 800000 in
include rm in
theorem combined_run (Q : Procedure w) (initial : All→Memory w) (t : ℕ)
    (reach : ∀z,Q.Exec (initial z) (m z) t) (cheap : CheapCode Q) :
    (∀z,(Q.seq (program P L w N slots)).Exec (initial z) (finished (slots:=slots) P L m z) (t+clocks N slots)) ∧
    CheapCode (Q.seq (program P L w N slots)) :=
  ⟨fun z=>@Procedure.Exec.then w Q (program P L w N slots) (initial z) (m z)
      (finalMem P L N slots (m z)) t (clocks N slots) (reach z) (run P L rm (m z)).1,
    @cheap_seq w Q (program P L w N slots) cheap (run P L rm (fun _=>0)).2⟩

end
end Hierarchy.DescentTerminalChipRuntime

end OAI
