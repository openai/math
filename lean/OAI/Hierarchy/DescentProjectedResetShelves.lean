import OAI.Hierarchy.DescentResetCatalog
import OAI.Hierarchy.DescentDatedImage
import OAI.Hierarchy.DescentFallbackGLWindow

namespace OAI
/-! # Physically extract all signed, local, and neighbor-readable reset fields -/
namespace Hierarchy.DescentSixParty.Chronology.Shelf
open DescentPackedColony.Phase.Arena ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ}

/-- The entire immutable table and its read protection are part of this stage's program. -/
def ofImage (I : Image w) (band : I.low≤I.stop) (room : I.stop<2^w) : Shelf w where
  program:=I.program
  ticks:=4+10*I.length
  image:=I.output
  cheap:=I.hardware.1
  first:=I.low
  limit:=I.stop
  fits:=band
  runs:=fun m=>(I.issue m (by unfold Image.length;omega)).1
  frame:=fun m=>(I.issue m (by unfold Image.length;omega)).2.2
  below:=by
    intro m n agree a hi
    have fits : I.low+I.length<2^w:=by unfold Image.length;omega
    by_cases lo : I.low≤a
    · exact ((I.issue n fits).2.1 a lo hi).trans ((I.issue m fits).2.1 a lo hi).symm
    · exact ((I.issue n fits).2.2 a (.inl (by omega))).trans
        ((agree a hi).trans ((I.issue m fits).2.2 a (.inl (by omega))).symm)

end
end Hierarchy.DescentSixParty.Chronology.Shelf

namespace Hierarchy.DescentFallbackPeriod.Projected
open DescentSIMDLookup DescentPackedColony DescentPackedColony.Phase.Arena DescentPackedFallbackTree.Image
open DescentSixParty.Chronology DescentSixParty.Chronology.Shelf
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M field w K : ℕ}

/-- `plus=1` makes a present neighboring zero distinguishable from the absent-neighbor code. -/
structure Query where
  source : Bank
  bytes : ℕ
  slots : ℕ
  index : Fin slots
  plus : ℕ

def Query.loBits (q : Query) := q.bytes*q.slots
def Query.tab (q : Query) (field : ℕ) : Cell q.loBits→Cell field :=
  project (field:=field) (bytes:=q.bytes) q.index q.plus
def Query.reader (q : Query) (first H G M : ℕ) : Banks :=
  banks q.loBits q.source first (Nat.clog 2 (H*chunks G M)) M
def Query.out (q : Query) (first H G M : ℕ) :=
  first+2^(q.loBits*M)+2^(Nat.clog 2 (H*chunks G M))
def Query.stop (q : Query) (first H G M : ℕ) := q.out first H G M+H*chunks G M
def Query.literals (q : Query) (first H G M field w : ℕ) : Image w :=
  ⟨first,q.out first H G M,
    header (q.tab field) H G M w first (fun _=>0)⟩

structure Query.Room (q : Query) (first H G M field w : ℕ) : Prop where
  prior : q.source.Fits w first
  rows : H*chunks G M≤q.source.size
  packed : M*max q.loBits field≤w/2
  top : q.stop first H G M<2^w

private theorem Query.le_out (q : Query) (first H G M : ℕ) : first ≤ q.out first H G M :=
  (Nat.le_add_right first (2^(q.loBits*M))).trans (Nat.le_add_right ..)

theorem Query.safe (q : Query) (first : ℕ) (room : q.Room first H G M field w) :
    Fits (q.reader first H G M) q.loBits field M H G w (q.out first H G M) := by
  have first_le : first≤q.out first H G M:=q.le_out first H G M
  have endWord : q.out first H G M<2^w := (Nat.le_add_right ..).trans_lt room.top
  have dictEnd : first+2^(q.loBits*M)≤q.out first H G M:=Nat.le_add_right ..
  have maskEnd : (q.reader first H G M).mask.base+(q.reader first H G M).mask.size=q.out first H G M:=rfl
  have dictFits : (q.reader first H G M).dictionary.Fits w (q.out first H G M) := by
    exact ⟨Nat.two_pow_pos _,(show 2^(q.loBits*M)≤q.out first H G M from
      (Nat.le_add_left ..).trans dictEnd).trans_lt endWord,dictEnd⟩
  have maskFits : (q.reader first H G M).mask.Fits w (q.out first H G M) := by
    exact ⟨Nat.two_pow_pos _,((Nat.le_add_left ..).trans maskEnd.le).trans_lt endWord,maskEnd.le⟩
  exact ⟨⟨room.prior.1,room.prior.2.1,room.prior.2.2.trans first_le⟩,dictFits,maskFits,
    room.rows,rfl,Nat.le_pow_clog (by decide) _,room.top,room.packed⟩

def Query.job (q : Query) (first : ℕ) (room : q.Room first H G M field w) : Shelf w :=
  let I:=q.literals first H G M field w
  let n:=H*chunks G M
  let fit:=q.safe first room
  let endWord : q.out first H G M<2^w:=(Nat.le_add_right ..).trans_lt room.top
  (Shelf.ofImage I (q.le_out first H G M) endWord).seq
    (Shelf.ofScan (q.out first H G M) n (lookup (q.reader first H G M))
      ⟨⟨fit.dictionary,fit.source,trivial⟩,fit.mask,trivial⟩ fit.output)

theorem Query.bounds (q : Query) (first : ℕ) (room : q.Room first H G M field w) :
    (q.job first room).first=first ∧ (q.job first room).limit=q.stop first H G M := by
  have f : first≤q.out first H G M:=q.le_out first H G M
  change min first (q.out first H G M)=_ ∧ max (q.out first H G M) (q.stop first H G M)=_
  exact ⟨min_eq_left f,max_eq_right (Nat.le_add_right ..)⟩

theorem Query.read (q : Query) (first : ℕ) (room : q.Room first H G M field w)
    (X : Fin H→Fin G→Fin q.slots→Cell q.bytes) (mem : Memory w)
    (source : Reads q.source (fun h g=>encode q.bytes q.slots (X h g)) M mem) :
    ∀p : Row H G M,(q.job first room).image mem (q.out first H G M+(row H G M p).val)=
        ((data (fun h g=>((X h g q.index).val+q.plus:Cell field)) p).val:Word w) := by
  let I:=q.literals first H G M field w
  let B:=q.reader first H G M
  let mid:=I.output mem
  have fit:=q.safe first room
  have small : I.low+I.length<2^w:=by
    change first+(q.out first H G M-first)<2^w
    have lower := q.le_out first H G M
    have upper : q.out first H G M < 2^w := (Nat.le_add_right ..).trans_lt room.top
    omega
  obtain ⟨_,printed,frame⟩:=I.issue mem small
  have held : Reads B.source (fun h g=>encode q.bytes q.slots (X h g)) M mid := by
    intro p
    have lt:=(row H G M p).isLt.trans_le room.rows
    exact (frame _ (.inl ((Nat.add_lt_add_left lt _).trans_le room.prior.2.2))).trans (source p)
  have words:=resident_header (q.tab field) q.source first (Nat.clog 2 (H*chunks G M)) H G M w (fun _=>0)
  have real : resident (q.tab field) B H G M mid := by
    constructor
    · intro i
      have upper:=i.isLt
      exact (printed _ (Nat.le_add_right ..) ((Nat.add_lt_add_left upper first).trans_le (Nat.le_add_right ..))).trans (words.1 i)
    · intro i
      have upper:=i.isLt.trans_le (Nat.le_pow_clog (by decide : 1<2) (H*chunks G M))
      exact (printed _ ((Nat.le_add_right first (2^(q.loBits*M))).trans (Nat.le_add_right ..))
        (Nat.add_lt_add_left upper _)).trans (words.2 i)
  intro p
  exact (ProtocolRAMGeneratedWrite.read_image (q.out first H G M) _ (lookup B) mid (row H G M p)).trans
    (projected B (q.out first H G M) q.index q.plus X mid fit held real p)

end
end Hierarchy.DescentFallbackPeriod.Projected

namespace Hierarchy.DescentFallbackPeriod.Projected
open DescentSIMDLookup DescentPackedColony DescentSixParty.Chronology DescentSixParty.Chronology.Shelf
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M field w K : ℕ}

def stride (maxBits H G M : ℕ) :=
  2^(maxBits*M)+2^(Nat.clog 2 (H*chunks G M))+2^(Nat.clog 2 (H*chunks G M))

def start (base maxBits H G M i : ℕ) := base+stride maxBits H G M*i

theorem extent (q : Query) (base maxBits : ℕ) (i : Fin K) (bits : q.loBits≤ maxBits) :
    q.stop (start base maxBits H G M i.val) H G M≤base+stride maxBits H G M*(i.val+1) := by
  have sz:=Nat.pow_le_pow_right (by decide : 0<2) (Nat.mul_le_mul_right M bits)
  have rows:=Nat.le_pow_clog (by decide : 1<2) (H*chunks G M)
  rw [Nat.mul_succ]
  unfold start Query.stop Query.out stride
  omega

theorem publish (qs : Fin K→Query) (base maxBits : ℕ) (bound : ∀i,(qs i).loBits≤ maxBits)
    (safe : ∀i,(qs i).Room (start base maxBits H G M i.val) H G M field w)
    (X : ∀i,Fin H→Fin G→Fin (qs i).slots→Cell (qs i).bytes) (mem : Memory w)
    (previous : ∀i,Reads (qs i).source (fun h g=>encode (qs i).bytes (qs i).slots (X i h g)) M mem) :
    let first:=start base maxBits H G M
    let jobs:=fun i=>(qs i).job (first i.val) (safe i)
    let sequence:=Shelf.series (Shelf.catalog jobs)
    sequence.Runs mem ∧ sequence.ticks=(∑i,(jobs i).ticks)+4 ∧
      (∀i,Reads ⟨(qs i).out (first i.val) H G M,Nat.clog 2 (H*chunks G M)⟩
        (fun h g=>((X i h g (qs i).index).val+(qs i).plus:Cell field)) M (sequence.image mem)) ∧
      ∀a,a<base ∨ base+stride maxBits H G M*K≤a→sequence.image mem a=mem a := by
  let first:=start base maxBits H G M
  let jobs (i : Fin K):=(qs i).job (first i.val) (safe i)
  have layout (i : Fin K) : first i.val≤(jobs i).first ∧ (jobs i).limit≤base+stride maxBits H G M*(i.val+1) := by
    obtain ⟨lower,upper⟩:=(qs i).bounds (first i.val) (safe i)
    exact ⟨lower.ge,upper.le.trans (extent _ _ _ i (bound i))⟩
  obtain ⟨ran,time,retained,frame⟩:=issued_catalog jobs base (stride maxBits H G M) layout mem
  refine ⟨ran,time,?_,frame⟩
  intro i p
  obtain ⟨lower,upper⟩:=(qs i).bounds (first i.val) (safe i)
  let a:=(qs i).out (first i.val) H G M+(row H G M p).val
  have lo : (jobs i).first≤a:=
    lower.le.trans (((qs i).le_out (first i.val) H G M).trans (Nat.le_add_right ..))
  have hi : a<(jobs i).limit:=by
    rw [show (jobs i).limit=(qs i).stop (first i.val) H G M from upper]
    exact Nat.add_lt_add_left (row H G M p).isLt _
  exact (retained i a lo hi).trans ((qs i).read (first i.val) (safe i) (X i) mem (previous i) p)

end
end Hierarchy.DescentFallbackPeriod.Projected

end OAI
