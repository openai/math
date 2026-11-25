import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.ProbeStageColumnScan
import OAI.Hierarchy.DescentColonies

namespace OAI
/-! # Packed native presence bits for all three normalized reset site forms -/
namespace Hierarchy.DescentActorRaster.CPU
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
inductive Query
  | empty
  | rotor (id : ℕ)
  | trunk (shape : ℕ)
  | tree (shape depth : ℕ)
  deriving DecidableEq

def accepts (r : ℕ) (q : Query) (level : ℕ) (read : Fin (2^r)→ℕ) : Prop :=
  match q with
  | .empty=>False
  | .rotor id=>∃j,DescentColonies.group level j=id ∧ read j%2=0
  | .trunk shape=>∃j,read j/2=shape
  | .tree shape depth=>(∃j,read j/2=shape) ∧ depth≤level

/-- Header zero is an absent previous host. Live headers store one plus the
depth of its measured base, or one plus the measured height of its tree. -/
def gate (r t a : ℕ) (q : Query) (src : Cell (t*2^r)) (head : Cell a) : Cell 1 :=
  if head.val>0 ∧ accepts r q (head.val-1) (fun j=>digit t j.val src.val) then 1 else 0

theorem active (r t a : ℕ) (q : Query) (words : Fin (2^r)→Cell t) (level : ℕ) (fit : level+1<2^a) :
    gate r t a q (encode t (2^r) words) (level+1:ℕ)=
      if accepts r q level (fun j=>(words j).val) then 1 else 0 := by
  unfold gate
  rw [Fin.val_cast_of_lt fit]
  simp [digit_encode]

theorem absent (r t a : ℕ) (q : Query) (src : Cell (t*2^r)) : gate r t a q src 0=0 := by simp [gate]

variable {Q r t a H G M w : ℕ}
def expression (tabs : Fin Q→Tables) (src : Expr) (heads : Fin Q→Expr) (j : Fin Q) :=
  (tabs j).read src (heads j)

def passes (tabs : Fin Q→Tables) (src : Expr) (heads : Fin Q→Expr) (base H G M : ℕ) :=
  ProbeStage.Native.columns (H*chunks G M) base (List.ofFn (expression tabs src heads))

theorem run (tabs : Fin Q→Tables) (src : Expr) (heads : Fin Q→Expr) (base : ℕ) (m : Memory w)
    (queries : Fin Q→Query) (words : Fin H→Fin G→Cell (t*2^r)) (header : Fin Q→Fin H→Fin G→Cell a)
    (fit : ∀j,Fits (tabs j) src (heads j) (t*2^r) a M base w)
    (room : base+Q*(H*chunks G M)<2^w) (fixed : ∀j,Static (tabs j) (gate r t a (queries j)) M m)
    (read : Source src words M m) (counts : ∀j,Source (heads j) (header j) M m) :
    let p:=passes tabs src heads base H G M
    let out:=ProtocolRAM.result p m
    (ProtocolRAM.program w p).Exec m out (clock p) ∧
    (∀j(p : Row H G M),out (base+j.val*(H*chunks G M)+(row H G M p).val)=
      ((data (fun h g=>gate r t a (queries j) (words h g) (header j h g)) p).val:Word w)) ∧
    (∀z,z<base ∨ base+Q*(H*chunks G M)≤z → out z=m z) ∧ CheapCode (ProtocolRAM.program w p) := by
  let es:=List.ofFn (expression tabs src heads)
  have fs : ∀e∈es,e.Fits w base:=by
    intro e he
    obtain ⟨j,rfl⟩:=List.mem_ofFn.mp he
    simp [expression,Tables.read,Expr.Fits,(fit j).left,(fit j).right,(fit j).shift,(fit j).apply]
  have len : es.length=Q:=List.length_ofFn
  refine ⟨ProbeStage.Native.columns_exec es m (ProbeStage.Native.columns_safe es le_rfl fs (by simpa only [len] using room)),?_,
    fun z hz=>ProbeStage.Native.columns_frame es m (by simpa [len] using hz),@ProtocolRAM.program_cheap _ _⟩
  intro j p
  change ProtocolRAM.result (ProbeStage.Native.columns (H*chunks G M) base es) m _ = _
  rw [ProbeStage.Native.columns_read es m le_rfl fs j.val (j.isLt.trans_eq len.symm) (row H G M p)]
  simpa only [es,List.getElem_ofFn,expression] using read_data (tabs j) src (heads j) base (fit j)
    (gate r t a (queries j)) (absent ..) m (fixed j) words (header j) read (counts j) p

end
end Hierarchy.DescentActorRaster.CPU

end OAI
