import OAI.Hierarchy.DescentTerminalShelfControl
import OAI.Hierarchy.DescentTerminalPrintedFieldsRAM
import OAI.Hierarchy.DescentTerminalChipTapes

namespace OAI
/-! # Key issue from physical chronological headers and the checked routed shelf -/
namespace Hierarchy.DescentTerminalChronologicalIssue
open DescentKernelHistory hiding Word
open DescentTerminalRecipeRows DescentTerminalBinReaddress
open DescentTerminalScalarTransposes DescentTerminalChipRuntime
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section

variable {pool S q W piece tags H N A w V bits : ℕ} (sites : Fin S→Site) (wp : 0<W) (qp : 0<q)
    (fit : ∀i,(sites i).rows q ≤ W) (room : sliceWidth W q piece ≤ bits)
    (space : DescentTerminalBinPack.purchased W (counts (q:=q) sites) ≤ pool)
    (hist : ∀i,(v : Fin (sites i).nodes)→Recipe (Fin tags) (Fin ((sites i).arity v)))
    (birth : ∀i,DescentTerminalChronologicalBooks.Birth (hist i))
    (hH : ∀i v,Fintype.card (hist i v).Hidden ≤ H) (hN : ∀i v,Fintype.card (hist i v).Node ≤ N)
    (hA : ∀i v u,(hist i v).arity u ≤ A) (hw : ∀i v u,(hist i v).width u ≤ w) (hV : ∀i,(sites i).nodes ≤ V)
local notation "atRow" => DescentTerminalRowBooks.rowAddress sites wp space
local notation "C" => DescentTerminalRowBooks.Control q tags H N A w V
local notation "meta" => DescentTerminalChronologicalBooks.meta sites qp hist birth hH hN hA hw hV
local notation "K" => Bins (W:=W) (q:=q) sites
local notation "routes" => DescentTerminalBinFormat.address W q
local notation "ctls" => DescentTerminalRecipeRows.control sites wp qp
local notation "empty" => DescentTerminalChronologicalBooks.empty q tags H N A w V (W*piece)
local notation "codes" => DescentTerminalScalarHeader.range q tags H N A w V


def leaf (i : Fin pool) := DescentTerminalRowBooks.padded atRow (fun a=>present (meta a))
  (DescentTerminalRowBooks.rows sites) none i
local notation "tape" => leaf sites wp qp space hist birth hH hN hA hw hV

theorem leaf_at (a : DescentTerminalRowBooks.LocalRow (q:=q) sites) : tape (atRow a)=present (meta a) := by
  exact DescentTerminalRowBooks.padded_live atRow (fun b => present (meta b))
    (DescentTerminalRowBooks.rows sites) none a (DescentTerminalRowBooks.mem_rows sites a)

theorem leaf_gap (i : Fin pool) (gap : ∀a,atRow a≠i) : tape i=none := by
  exact DescentTerminalRowBooks.padded_empty atRow (fun b => present (meta b))
    (DescentTerminalRowBooks.rows sites) none i (fun a _ => gap a)

theorem live_iff (i : Fin pool) : (tape i).isSome=true ↔
    ∃a : DescentTerminalRowBooks.LocalRow (q:=q) sites,atRow a=i ∧ (meta a).1.val≠0 := by
  by_cases hit : ∃a,atRow a=i
  · obtain ⟨a,rfl⟩:=hit
    rw [leaf_at]
    by_cases live : (meta a).1.val=0
    · constructor
      · intro no;simp [present,live] at no
      · rintro ⟨b,back,occupied⟩
        have eqn : b = a := (atRow).injective back
        subst b
        exact (occupied live).elim
    · exact ⟨fun _=>⟨a,rfl,live⟩,fun _=>by simp [present,live]⟩
  · constructor
    · intro no
      rw [leaf_gap sites wp qp space hist birth hH hN hA hw hV i (fun a e=>hit ⟨a,e⟩)] at no
      contradiction
    · rintro ⟨a,back,_⟩
      exact (hit ⟨a,back⟩).elim

theorem live_count (i : Fin pool) (c : C) (hc : tape i=some c) : c.1.val≠0 := by
  obtain ⟨a,rfl,nonzero⟩:=(live_iff sites wp qp space hist birth hH hN hA hw hV i).mp (by simp [hc])
  rw [leaf_at,present,ite_eq_right nonzero] at hc
  exact (Option.some.inj hc) ▸ nonzero

theorem fields_at (a : DescentTerminalRowBooks.LocalRow (q:=q) sites) (live : (meta a).1.val≠0) :
    DescentTerminalPrintedFieldsRAM.fields tape (atRow a)=
      DescentTerminalPrintedFields.digits (DescentTerminalPrintedFields.emit (meta a)) := by
  simp [DescentTerminalPrintedFieldsRAM.fields,leaf_at,present,live]

/-- Numerical row metadata are the reached six-column print, with the
same chronology as the originally emitted operand and hidden-variable
ledger. The other data tape is the second literal view of the proposal. -/
structure Reads (L : DescentTerminalScalarDispatch.Layout) (Y : Proposal K W q piece) (m : Memory bits) : Prop where
  header : ∀i : Fin pool,L.header.read m (i.val:Word bits)=(DescentTerminalPrintedFieldsRAM.expected (tape i):Word bits)
  payload : ∀a : DescentTerminalRowBooks.LocalRow (q:=q) sites,L.payload.read m ((atRow a).val:Word bits)=
    ((rowWord Y (DescentTerminalBinPack.rowIndex wp (counts (q:=q) sites) a)).val:Word bits)
  pointer : ∀j : Fin codes,L.pointer.read m (((j.val+1:ℕ):Word bits))=(((j.val*2^(q*(W*piece)):ℕ)):Word bits)

/-- Project the actual printer memory into the chip's three earlier banks.
Only the two immutable operands of the scalar issue must lie before the
new header column; their values survive the actual scan literally. -/
theorem reads_of_print (L : DescentTerminalScalarDispatch.Layout) (printer : DescentTerminalPrintedFieldsRAM.Layout)
    (Y : Proposal K W q piece) (m : Memory bits) (dst : ℕ)
    (input : DescentTerminalPrintedFieldsRAM.Inputs printer m tape)
    (fitProgram : (DescentTerminalPrintedFieldsRAM.row printer).Fits bits L.header.base)
    (room : L.header.base+pool<2^bits) (pos : 0<bits)
    (headerFits : L.header.Fits bits dst) (headSpace : pool ≤ L.header.size)
    (dataFits : L.payload.Fits bits L.header.base) (ptrFits : L.pointer.Fits bits L.header.base)
    (dataSpace : pool ≤ L.payload.size) (ptrSpace : codes+1 ≤ L.pointer.size)
    (data : ∀a : DescentTerminalRowBooks.LocalRow (q:=q) sites,m (L.payload.base+(atRow a).val)=
      ((rowWord Y (DescentTerminalBinPack.rowIndex wp (counts (q:=q) sites) a)).val:Computability.VPVNP.BurstRAM.Word bits))
    (pointer : ∀j : Fin (codes+1),m (L.pointer.base+j.val)=
      ((DescentTerminalScalarDispatch.pointers (fun a : Fin codes=>a.val*2^(q*(W*piece))))[j.val]'
        (by simpa only [DescentTerminalScalarDispatch.pointers,List.length_ofFn] using j.isLt):Computability.VPVNP.BurstRAM.Word bits)) :
    let after:=image L.header.base pool (DescentTerminalPrintedFieldsRAM.row printer) m
    (DescentTerminalPrintedFieldsRAM.program printer bits L.header.base pool).Exec m after (4+188*pool) ∧
      Reads sites wp qp space hist birth hH hN hA hw hV L Y after := by
  intro after
  obtain ⟨run,printed⟩:=DescentTerminalPrintedFieldsRAM.run printer m tape input fitProgram room pos
  have before (a : ℕ) (h : a<L.header.base) : after a=m a :=
    DescentTerminalChipRuntime.image_low m L.header.base pool (DescentTerminalPrintedFieldsRAM.row printer) h
  refine ⟨run,fun i=>?_,fun a=>?_,fun j=>?_⟩
  · rw [DescentTerminalDenseHeaderRAM.bank_nat after headerFits (i.isLt.trans_le headSpace)]
    exact printed i
  · have slot := (atRow a).isLt.trans_le dataSpace
    exact (DescentTerminalDenseHeaderRAM.bank_nat after dataFits slot).trans
      ((before _ ((Nat.add_lt_add_left slot L.payload.base).trans_le dataFits.2.2)).trans (data a))
  · have slot : j.val+1<L.pointer.size := j.succ.isLt.trans_le ptrSpace
    rw [DescentTerminalDenseHeaderRAM.bank_nat (a:=j.val+1) after ptrFits slot,
      before _ ((Nat.add_lt_add_left slot L.pointer.base).trans_le ptrFits.2.2)]
    change m (L.pointer.base+j.succ.val)=_
    rw [pointer j.succ]
    apply congrArg (fun k : ℕ => (k : Computability.VPVNP.BurstRAM.Word bits))
    unfold DescentTerminalScalarDispatch.pointers
    rw [List.getElem_ofFn]
    exact Fin.cases_succ (motive:=fun _ => ℕ) (zero:=0)
      (succ:=fun a : Fin codes=>a.val*2^(q*(W*piece))) j

theorem read (L : DescentTerminalScalarDispatch.Layout) (m : Memory bits) (X Y : Proposal K W q piece)
    (checked : wide ∘ chunks Y=sliceOutput (bits:=bits) routes ctls X)
    (fits : codes+1 ≤ 2^bits) (reads : Reads sites wp qp space hist birth hH hN hA hw hV L Y m) (i : Fin pool) :
    (DescentTerminalScalarDispatch.fetch L (empty).val).eval m (i.val:Word bits)=
      ((DescentTerminalChronologicalBooks.requests sites wp qp room X space hist birth hH hN hA hw hV i).val:Word bits) := by
  by_cases used : ∃a,atRow a=i
  · obtain ⟨a,rfl⟩:=used
    let code:=DescentTerminalScalarHeader.encode (meta a)
    have stamp_ne : (((code.val+1:ℕ):Word bits))≠((0:ℕ):Word bits) := by
      intro h
      have small : code.val+1<2^bits := code.succ.isLt.trans_le fits
      have v : (code.val+1) % (2^bits) = 0 % (2^bits) := congrArg Fin.val h
      rw [Nat.mod_eq_of_lt small,Nat.zero_mod] at v
      exact Nat.succ_ne_zero _ v
    have nz : (((code.val+1:ℕ):Word bits))≠0 := by simpa only [Nat.cast_zero] using stamp_ne
    have stamp:=reads.header (atRow a)
    rw [leaf_at] at stamp
    by_cases vacant : (meta a).1.val=0
    · rw [present,ite_eq_left vacant] at stamp
      rw [DescentTerminalChronologicalBooks.request_at]
      simp [DescentTerminalScalarDispatch.fetch,Expr.eval,Comparison.test,stamp,DescentTerminalPrintedFieldsRAM.expected,
        DescentTerminalChronologicalBooks.loc,DescentTerminalChronologicalBooks.issued,vacant]
    rw [present,ite_eq_right vacant] at stamp
    change L.header.read m ((atRow a).val:Word bits)=(((code.val+1:ℕ):Word bits)) at stamp
    have payloadEq:=data_at sites wp qp room X Y checked a
    rw [DescentTerminalChronologicalBooks.request_at]
    simp only [DescentTerminalChronologicalBooks.loc,DescentTerminalChronologicalBooks.issued,ite_eq_right vacant,DescentTerminalScalarDispatch.fetch,Expr.eval,Comparison.test,RowOp.opcode,BinaryOp.eval,beq_iff_eq,
      stamp,Nat.cast_zero,nz,ite_false,reads.pointer,reads.payload,payloadEq,←Nat.cast_add]
    apply congrArg (fun n : ℕ=>(n:Word bits))
    change code.val*2^(q*(W*piece))+_=_+2^(q*(W*piece))*code.val
    ring
  · have gap : ∀a,atRow a≠i:=fun a h=>used ⟨a,h⟩
    rw [DescentTerminalChronologicalBooks.request_gap sites wp qp room X space hist birth hH hN hA hw hV i gap]
    have hdr : L.header.read m (i.val:Word bits)=0 := (reads.header i).trans (by
      rw [leaf_gap sites wp qp space hist birth hH hN hA hw hV i gap]
      rfl)
    simp [DescentTerminalScalarDispatch.fetch,Expr.eval,Comparison.test,hdr]

end
end Hierarchy.DescentTerminalChronologicalIssue

end OAI
