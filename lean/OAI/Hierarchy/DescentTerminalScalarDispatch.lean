import OAI.Hierarchy.DescentTerminalScalarTransposes
import OAI.Hierarchy.DescentTerminalBankRead

namespace OAI
/-! # One native scalar-key issue per common paid row -/
namespace Hierarchy.DescentTerminalScalarDispatch
open DescentKernelHistory (Recipe)
open DescentTerminalBinReaddress DescentTerminalRecipeRows DescentTerminalRowBooks
open DescentTerminalScalarTransposes Computability.VPVNP.RAMSerialization Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Fin.CommRing Classical
noncomputable section

structure Layout where
  header : Bank
  payload : Bank
  pointer : Bank

/-- Zero in the header is an unoccupied row. A live header is one plus
the numeric serialization of the actual local scalar description. -/
def fetch (L : Layout) (empty : ℕ) : Expr :=
  let stamp:=Expr.lookup L.header .row
  .branch .eq stamp (.lit 0) (.lit empty)
    (.op .add (.lookup L.pointer stamp) (.lookup L.payload .row))

def program (L : Layout) (bits out rows empty : ℕ) := scan bits out rows (fetch L empty)
theorem cheap (L : Layout) (bits out rows empty : ℕ) : CheapCode (program L bits out rows empty) := @scan_cheap _ _ _ _

def pointers {n : ℕ} (shift : Fin n→ℕ) : List ℕ :=
  List.ofFn (Fin.cases 0 shift : Fin (n+1)→ℕ)

variable {bits pool q W piece tags H N A w V S rawCount : ℕ} (sites : Fin S→Site)
  (wp : 0<W) (qp : 0<q) (machine : sliceWidth W q piece ≤ bits)
  (space : DescentTerminalBinPack.purchased W (counts (q:=q) sites) ≤ pool)
  (recipes : (i : Fin S)→(v : Fin (sites i).nodes)→Recipe (Fin tags) (Fin ((sites i).arity v)))
  (hH : ∀i v,Fintype.card (recipes i v).Hidden ≤ H) (hN : ∀i v,Fintype.card (recipes i v).Node ≤ N)
  (hA : ∀i v j,(recipes i v).arity j ≤ A) (hw : ∀i v j,(recipes i v).width j ≤ w) (hV : ∀i,(sites i).nodes ≤ V)

local notation "C" => Control q tags H N A w V
local notation "p" => W*piece
local notation "K" => Bins (W:=W) (q:=q) sites
local notation "atRow" => rowAddress sites wp space
local notation "routes" => DescentTerminalBinFormat.address W q
local notation "ctls" => DescentTerminalRecipeRows.control sites wp qp
local notation "empty" => emptyKey q tags H N A w V p

def «meta» (a : LocalRow (q:=q) sites) : C :=
  DescentTerminalRowBooks.control qp (recipes a.1) (hH a.1) (hN a.1) (hA a.1) (hw a.1) (hV a.1) a.2

def shift (decode : Fin rawCount→C) (j : Fin rawCount) := (Fintype.equivFin C (decode j)).val*2^(q*p)

/-- These inputs are separate reached tape fields. The header is the
printed local address book (with a physical vacancy marker), the payload
is the second fixed transpose proposal in row order, and the pointer bank
is a single immutable alphabet-wide table. -/
structure Reads (encode : C→Fin rawCount) (decode : Fin rawCount→C) (L : Layout)
    (y : Proposal K W q piece) (m : Memory bits) : Prop where
  active : ∀a : LocalRow (q:=q) sites,L.header.read m ((atRow a).val:Word bits)=
    (((encode («meta» sites qp recipes hH hN hA hw hV a)).val+1:ℕ):Word bits)
  gap : ∀i : Fin pool,(∀a,atRow a≠i)→L.header.read m (i.val:Word bits)=0
  data : ∀a : LocalRow (q:=q) sites,L.payload.read m ((atRow a).val:Word bits)=
    ((rowWord y (DescentTerminalBinPack.rowIndex wp (counts (q:=q) sites) a)).val:Word bits)
  ptr : ∀j : Fin rawCount,L.pointer.read m (((j.val+1:ℕ):Word bits))=(shift (W:=W) (piece:=piece) decode j : Word bits)

theorem from_arrays (encode : C→Fin rawCount) (decode : Fin rawCount→C) (L : Layout)
    (y : Proposal K W q piece) (m : Memory bits) (out : ℕ)
    (bounds : ∀b∈[L.header,L.payload,L.pointer],b.Fits bits out)
    (headSpace : pool ≤ L.header.size) (dataSpace : pool ≤ L.payload.size) (tableSpace : rawCount+1 ≤ L.pointer.size)
    (active : ∀a,m (L.header.base+(atRow a).val)=(((encode («meta» sites qp recipes hH hN hA hw hV a)).val+1:ℕ):Word bits))
    (gap : ∀i : Fin pool,(∀a,atRow a≠i)→m (L.header.base+i.val)=0)
    (data : ∀a,m (L.payload.base+(atRow a).val)=
      ((rowWord y (DescentTerminalBinPack.rowIndex wp (counts (q:=q) sites) a)).val:Word bits))
    (ptr : ∀j : Fin (rawCount+1),m (L.pointer.base+j.val)=
      ((pointers (shift (W:=W) (piece:=piece) decode))[j.val]'(by simpa only [pointers,List.length_ofFn] using j.isLt):Word bits)) :
    Reads sites wp qp space recipes hH hN hA hw hV encode decode L y m := by
  refine ⟨fun a=>?_,fun i h=>?_,fun a=>?_,fun j=>?_⟩
  · rw [DescentTerminalDenseHeaderRAM.bank_nat m (bounds L.header (by simp)) ((atRow a).isLt.trans_le headSpace)]
    exact active a
  · rw [DescentTerminalDenseHeaderRAM.bank_nat m (bounds L.header (by simp)) (i.isLt.trans_le headSpace),gap i h]
  · rw [DescentTerminalDenseHeaderRAM.bank_nat m (bounds L.payload (by simp)) ((atRow a).isLt.trans_le dataSpace)]
    exact data a
  · have bound : j.val+1<L.pointer.size := j.succ.isLt.trans_le tableSpace
    rw [DescentTerminalDenseHeaderRAM.bank_nat (a:=j.val+1) m (bounds L.pointer (by simp)) bound]
    change m (L.pointer.base+j.succ.val)=_
    rw [ptr j.succ]
    apply congrArg (fun n : ℕ => (n : Word bits))
    unfold pointers
    rw [List.getElem_ofFn]
    exact Fin.cases_succ (motive:=fun _ => ℕ) (zero:=0)
      (succ:=shift (W:=W) (piece:=piece) decode) j

theorem native_exec (encode : C→Fin rawCount) (decode : Fin rawCount→C) (back : Function.LeftInverse decode encode)
    (L : Layout) (out : ℕ) (m : Memory bits) (x y : Proposal K W q piece)
    (checked : wide ∘ chunks y=sliceOutput (bits:=bits) routes ctls x)
    (bounds : ∀b∈[L.header,L.payload,L.pointer],b.Fits bits out)
    (room : out+pool<2^bits) (amps : rawCount+1 ≤ 2^bits)
    (read : Reads sites wp qp space recipes hH hN hA hw hV encode decode L y m) :
    let req:=request sites wp qp machine x space recipes hH hN hA hw hV
    ∃after, (program L bits out pool (empty).val).Exec m after (4+64*pool) ∧
      (∀i : Fin pool,after (out+i.val)=((req i).val:Word bits)) ∧
      (∀a<out,after a=m a) ∧ after=image out pool (fetch L (empty).val) m := by
  intro req
  have fit : (fetch L (empty).val).Fits bits out := by
    simp only [fetch,Expr.Fits,bounds _ (by simp : L.header∈[L.header,L.payload,L.pointer]),
      bounds _ (by simp : L.payload∈[L.header,L.payload,L.pointer]),
      bounds _ (by simp : L.pointer∈[L.header,L.payload,L.pointer]),and_self]
  refine ⟨_,?_,fun i=>?_,(fun a lt=>?_),rfl⟩
  · have work : (fetch L (empty).val).work=30 := rfl
    have ticks : 4+pool*(2*(fetch L (empty).val).work+4)=4+64*pool := by
      rw [work]
      omega
    rw [←ticks]
    exact @scan_exec bits out pool (fetch L (empty).val) m fit room
  · rw [DescentTerminalChipRuntime.image_at]
    by_cases occupied : ∃a,atRow a=i
    · obtain ⟨a,rfl⟩:=occupied
      let descr:=«meta» sites qp recipes hH hN hA hw hV a
      let s:=encode descr
      have stamp : (((s.val+1:ℕ):Word bits))≠((0:ℕ):Word bits) := by
        have small : s.val+1<2^bits := s.succ.isLt.trans_le amps
        intro eqn
        have same : (s.val+1)%(2^bits)=0%(2^bits) := congrArg Fin.val eqn
        rw [Nat.mod_eq_of_lt small,Nat.zero_mod] at same
        omega
      change (fetch L (empty).val).eval m ((atRow a).val:Word bits)=
        ((request sites wp qp machine x space recipes hH hN hA hw hV (atRow a)).val:Word bits)
      rw [request_at]
      have payloadEq:=data_at sites wp qp machine x y checked a
      simp only [fetch,Expr.eval,RowOp.opcode,BinaryOp.eval,Comparison.test,beq_iff_eq,
        read.active,read.ptr,read.data,payloadEq,shift]
      rw [ite_eq_right stamp, back descr]
      change (((Fintype.equivFin C descr).val*2^(q*p):ℕ):Word bits)+(_ : Word bits)=_
      rw [←Nat.cast_add]
      apply congrArg (fun n : ℕ=>(n:Word bits))
      change _=_+2^(q*p)*(Fintype.equivFin C descr).val
      simp only [DescentTerminalRowBooks.key]
      ring
    · have gap : ∀a,atRow a≠i:=fun a eqn=>occupied ⟨a,eqn⟩
      change (fetch L (empty).val).eval m (i.val:Word bits)=
        ((request sites wp qp machine x space recipes hH hN hA hw hV i).val:Word bits)
      rw [request_gap sites wp qp machine x space recipes hH hN hA hw hV i gap]
      simp [fetch,Expr.eval,Comparison.test,read.gap i gap]
  · simp [image,fillSegment,not_le.mpr lt]

end
end Hierarchy.DescentTerminalScalarDispatch

end OAI
