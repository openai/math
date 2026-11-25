import OAI.Hierarchy.DescentTerminalOperandTiles
import OAI.Hierarchy.DescentTerminalDenseHeaderRAM

namespace OAI
/-! # Packed terminal operand offsets with two physical passes per local chart -/
namespace Hierarchy.DescentTerminalOperandTilesRAM
open DescentKernelHistory (Recipe)
open DescentTerminalOperandScan DescentTerminalBundleRows DescentTerminalOperandTiles
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Fin.CommRing Classical
noncomputable section

structure Layout where
  input : Bank
  weight : Bank
  base : Bank
  slots : Bank
  cumulative : Bank
  result : Bank

def mask (L : Layout) : Expr := .lookup L.input .row
def pop (L : Layout) : Expr := .lookup L.weight (mask L)
def position (L : Layout) : Expr := .lookup L.slots
  (.op .add (.lookup L.base (mask L)) (DescentTerminalDenseHeaderRAM.previous L.cumulative))

def program (L : Layout) (bits rows : ℕ) :=
  (DescentTerminalHeaderPrefixRAM.program bits L.cumulative.base rows .add (pop L)).seq
    (scan bits L.result.base rows (position L))

theorem cheap (L : Layout) (bits rows : ℕ) : CheapCode (program L bits rows) :=
  @cheap_seq bits (DescentTerminalHeaderPrefixRAM.program bits L.cumulative.base rows .add (pop L))
    (scan bits L.result.base rows (position L))
    (@DescentTerminalHeaderPrefixRAM.cheap bits L.cumulative.base rows .add (pop L))
    (@scan_cheap bits L.result.base rows (position L))

def ticks (L : Layout) (rows : ℕ) := (4+rows*(2*DescentTerminalHeaderPrefixRAM.work .add (pop L)+4))+
  (4+rows*(2*(position L).work+4))

theorem ticks_bound (L : Layout) (rows : ℕ) : ticks L rows ≤ 8+120*rows := by
  simp [ticks,position,pop,mask,DescentTerminalHeaderPrefixRAM.work,DescentTerminalDenseHeaderRAM.previous,
    Expr.work]; omega

structure Fits (L : Layout) (bits rows : ℕ) : Prop where
  source : ∀b∈[L.input,L.weight,L.base,L.slots],b.Fits bits L.cumulative.base
  cumulative : L.cumulative.Fits bits L.result.base
  count : rows ≤ L.cumulative.size
  endAt : L.result.base+rows<2^bits

variable {Tag B : Type} (r : Recipe Tag B) (birth : r.Node ↪ ℕ) {q bits : ℕ}
local notation "rows" => tileCount r q
local notation "flags" => tile r birth q

def Reads (L : Layout) (m : Memory bits) :=
  (∀i : Fin rows,L.input.read m (i.val:Word bits)=((maskCode q (flags i.val)).val:Word bits)) ∧
  (∀z : Mask q,L.weight.read m ((maskCode q z).val:Word bits)=(before z q:Word bits)) ∧
  (∀z : Mask q,L.base.read m ((maskCode q z).val:Word bits)=(((maskCode q z).val*(q+1):ℕ):Word bits)) ∧
  (∀z : Mask q,∀o : Fin (q+1),L.slots.read m ((key z o).val:Word bits)=((output z o).val:Word bits))

theorem mounted (L : Layout) (m : Memory bits) (fit : Fits L bits rows)
    (count : rows ≤ L.input.size) (wt : 2^q ≤ L.weight.size) (off : 2^q ≤ L.base.size)
    (room : tableEntries q ≤ L.slots.size)
    (source : ∀i : Fin rows,m (L.input.base+i.val)=((maskCode q (flags i.val)).val:Word bits))
    (weightsAt : ∀i : Fin (2^q), m (L.weight.base+i.val)=((weights q)[i.val]'(by simp [weights]):Word bits))
    (baseAt : ∀i : Fin (2^q),m (L.base.base+i.val)=((offsets q)[i.val]'(by simp [offsets]):Word bits))
    (slotsAt : ∀i : Fin (tableEntries q),m (L.slots.base+i.val)=((table q)[i.val]'(by simp [table]):Word bits)) :
    Reads (q:=q) r birth L m := by
  refine ⟨fun i=>?_,fun z=>?_,fun z=>?_,fun z o=>?_⟩
  · exact (DescentTerminalDenseHeaderRAM.bank_nat m (fit.source L.input (by simp))
      (i.isLt.trans_le count)).trans (source i)
  · have value : (weights q)[(maskCode q z).val]'(by simp [weights]) = before z q := calc
      _ = before ((maskCode q).symm (maskCode q z)) q := by simp only [weights,List.getElem_ofFn]
      _ = _ := congrArg (fun t=>before t q) ((maskCode q).symm_apply_apply z)
    exact (DescentTerminalDenseHeaderRAM.bank_nat m (fit.source L.weight (by simp))
      ((maskCode q z).isLt.trans_le wt)).trans ((weightsAt (maskCode q z)).trans
        (congrArg (fun n : ℕ=>(n:Fin (2^bits))) value))
  · refine (DescentTerminalDenseHeaderRAM.bank_nat m (fit.source L.base (by simp))
      ((maskCode q z).isLt.trans_le off)).trans ((baseAt (maskCode q z)).trans ?_)
    simp only [offsets,List.getElem_ofFn]
  · exact (DescentTerminalDenseHeaderRAM.bank_nat m (fit.source L.slots (by simp))
      ((key z o).isLt.trans_le room)).trans ((slotsAt (key z o)).trans
        (congrArg (fun n : ℕ=>(n:Fin (2^bits))) (at_key z o)))

def current (i : ℕ) : Word bits := (cursor r birth (i*q):ℕ)

theorem run (L : Layout) (m : Memory bits) (limited : useCount r ≤ q) (fit : Fits L bits rows)
    (read : Reads (q:=q) r birth L m) :
    ∃after, (program L bits rows).Exec m after (ticks L rows) ∧
      ∀i : Fin rows,after (L.result.base+i.val)=((output (flags i.val) (offset r birth q limited i.val)).val:Word bits) := by
  obtain ⟨input,wt,base,slots⟩:=read
  let cum:=fillSegment L.cumulative.base rows (DescentTerminalHeaderPrefixRAM.file L.cumulative.base
    (current (q:=q) (bits:=bits) r birth)) m
  have span:=fit.count
  have end0:=fit.cumulative.2.2
  have end1:=fit.endAt
  have zero : current (q:=q) (bits:=bits) r birth 0=0 := by simp [current,cursor_zero]
  have first : (DescentTerminalHeaderPrefixRAM.program bits L.cumulative.base rows .add (pop L)).Exec m cum _ :=
    DescentTerminalHeaderPrefixRAM.spec L.cumulative.base .add (pop L) m
      (current (q:=q) r birth) trivial
      ⟨fit.source L.weight (by simp),fit.source L.input (by simp),trivial⟩ (by omega) zero (by
        intro i
        change ((cursor r birth (i.val*q):ℕ):Word bits)+(pop L).eval m (i.val:Word bits)=_
        simp only [pop,mask,Expr.eval,input,wt,current,tile_next,Nat.cast_add])
  have countAt (i : Fin rows) : cum (L.cumulative.base+i.val)=current (q:=q) r birth (i.val+1) :=
    DescentTerminalHeaderPrefixRAM.at_row L.cumulative.base (current (q:=q) r birth) m i
  have source (b : Bank) (mem : b∈[L.input,L.weight,L.base,L.slots]) :
      b.Fits bits L.result.base := DescentTerminalDenseHeaderRAM.fits_mono (fit.source _ mem) (by omega)
  have posFit : (position L).Fits bits L.result.base :=
    ⟨source _ (by simp),⟨source _ (by simp),source _ (by simp),trivial⟩,
      trivial,trivial,trivial,fit.cumulative,trivial,trivial⟩
  have readOld (b : Bank) (mem : b∈[L.input,L.weight,L.base,L.slots]) (j : Word bits) :
      b.read cum j=b.read m j :=
    DescentTerminalDenseHeaderRAM.before m _ j (fit.source _ mem)
  let out:=image L.result.base rows (position L) cum
  have second : (scan bits L.result.base rows (position L)).Exec cum out _ :=
    scan_exec L.result.base rows (position L) cum posFit fit.endAt
  have exec := @Procedure.Exec.then bits
    (DescentTerminalHeaderPrefixRAM.program bits L.cumulative.base rows .add (pop L))
    (scan bits L.result.base rows (position L)) m cum out _ _ first second
  refine ⟨out,exec,fun i=>?_⟩
  rw [show out (L.result.base+i.val)=(position L).eval cum (i.val:Word bits) from
    DescentTerminalDenseHeaderRAM.at_image L.result.base (position L) cum i]
  let z:=flags i.val
  let o:=offset r birth q limited i.val
  have prev:=DescentTerminalDenseHeaderRAM.previous_reads cum (current (q:=q) r birth)
    fit.cumulative fit.count zero countAt i
  change L.slots.read cum (L.base.read cum (L.input.read cum (i.val:Word bits))+
    (DescentTerminalDenseHeaderRAM.previous L.cumulative).eval cum (i.val:Word bits))=_
  rw [prev,readOld L.slots (by simp),readOld L.base (by simp),readOld L.input (by simp),input i,base]
  change L.slots.read m ((((maskCode q z).val*(q+1):ℕ):Word bits)+(o.val:Word bits))=_
  rw [←Nat.cast_add,←key_val]
  exact slots z o

/-- Decode the resident physical word at a true chronological input
position and obtain the exact compact public operand number. -/
theorem published (L : Layout) (m : Memory bits) (limited : useCount r ≤ q) (fit : Fits L bits rows)
    (read : Reads (q:=q) r birth L m) (wordRoom : (q+1)^q ≤ 2^bits) :
    ∃after, (program L bits rows).Exec m after (ticks L rows) ∧
      ∀(a : Public r) (i : Fin rows) (s : Fin q),i.val*q+s.val=raw r birth a →
        ∃z : Fin ((q+1)^q),(after (L.result.base+i.val)).val=z.val ∧
          ((digits q).symm z s).val=(publicOrdinal r birth a).val := by
  obtain ⟨after,exec,actual⟩:=run r birth L m limited fit read
  refine ⟨after,exec,fun a i s pos=>⟨_,?_,target r birth q limited a i s pos⟩⟩
  rw [actual,Fin.val_cast_of_lt ((output (flags i.val) (offset r birth q limited i.val)).isLt.trans_le wordRoom)]

end
end Hierarchy.DescentTerminalOperandTilesRAM

end OAI
