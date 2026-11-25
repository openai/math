import OAI.Hierarchy.DescentSignedTableDimensions
import OAI.Hierarchy.DescentParentFilterFused
import OAI.Hierarchy.DescentStaticTablePages

namespace OAI
/-! # Literal installation of the thirteen shared kernels of the streamed cable ranker -/
namespace Hierarchy.DescentParallelBase.ParentFilter.Fused.TablesROM
open DescentSIMDLookup DescentPackedZip DescentHaloWalkRAM DescentSharedCableNames DescentPackedOperand.Public
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open DescentOrdinaryAtomFieldRAM.ROM
open scoped Classical Fin.CommRing
noncomputable section

variable {D Q K L b M base w out : ℕ}
local notation "p" => breadth D
local notation "wd" => PackedBase.width (p*p*Q) K L


variable (D Q K L b M) in
def code : Fin (11+2) → Fin 2 → Page :=
  Fin.addCases (fun j=>binary (DescentPacking.PackedMatch.Local.Gather.setField (d:=b) j) M)
    (Fin.cases (binary (fun s (_:Cell 0)=>Machine.scalar D Q K L b s) M)
      (fun _=>binary (Stream.compareWord (p*p*Q) K L) M))

def address (kernel : Fin (11+2)) (half : Fin 2) : Fin ((11+2)*2) := finProdFinEquiv (kernel,half)

def pages (D Q K L b M : ℕ) (i : Fin ((11+2)*2)) :=
  let q:=finProdFinEquiv.symm i
  code D Q K L b M q.1 q.2

def format : Fin (11+2) := Fin.natAdd 11 (0:Fin 2)
def compare : Fin (11+2) := Fin.natAdd 11 (1:Fin 2)

local notation "book" => pages D Q K L b M
local notation "width" => unit D Q K L b*M
local notation "table" i => joined book width base (address i)

theorem insert_page (j : Fin 11) (s : Fin 2) :
    book (address (j.castAdd 2) s)=binary (DescentPacking.PackedMatch.Local.Gather.setField (d:=b) j) M s := by
  simp [pages,address,code]

theorem format_page (s : Fin 2) :
    book (address format s)=binary (fun x (_:Cell 0)=>Machine.scalar D Q K L b x) M s := by
  simp [pages,address,code,format]
  rfl

theorem compare_page (s : Fin 2) :
    book (address compare s)=binary (Stream.compareWord (p*p*Q) K L) M s := by
  simp [pages,address,code,compare]
  rfl

theorem page_bits (i : Fin ((11+2)*2)) : (book i).bits≤width := by
  obtain ⟨⟨j,t⟩,rfl⟩ := finProdFinEquiv.surjective i
  change (book (address j t)).bits≤width
  induction j using Fin.addCases with
  | left j =>
    rw [insert_page]
    have bound := Nat.mul_le_mul_right M (le_max_left (b*11+b) (wd+wd))
    fin_cases t <;> change _≤ max (b*11+b) (wd+wd)*M <;> first
      | exact bound
      | exact (Nat.mul_le_mul_right M (Nat.le_add_right (b*11) b)).trans bound
  | right j =>
    fin_cases j
    · change (book (address format t)).bits≤width
      rw [format_page]
      have bound := Nat.mul_le_mul_right M ((Nat.le_add_right (b*11) b).trans (le_max_left (b*11+b) (wd+wd)))
      fin_cases t <;> simpa [binary,unit] using bound
    · change (book (address compare t)).bits≤width
      rw [compare_page]
      have bound:=Nat.mul_le_mul_right M (le_max_right (b*11+b) (wd+wd))
      fin_cases t <;> change _≤ max (b*11+b) (wd+wd)*M <;> first
        | exact bound
        | exact (Nat.mul_le_mul_right M (Nat.le_add_right wd wd)).trans bound

theorem shift_bits {x y z : ℕ} (fn : Cell x→Cell y→Cell z) (i : Fin (11+2))
    (pagesAt : ∀j,book (address i j)=binary fn M j) :
    (table i).shift.bits=x*M ∧ (table i).apply.bits=(x+y)*M := by
  constructor
  · exact congrArg Page.bits (pagesAt 0)
  · exact congrArg Page.bits (pagesAt 1)

theorem layout {x y z : ℕ} (fn : Cell x→Cell y→Cell z) (i : Fin (11+2))
    (pagesAt : ∀j,book (address i j)=binary fn M j)
    (separate : base+26*2^width≤out) (room : out<2^w)
    (u v : Expr) (hu : u.Fits w out) (hv : v.Fits w out) :
    DescentPackedZip.Fits (table i) u v x y M out w :=
  let bits:=shift_bits (base:=base) fn i pagesAt
  ⟨hu,hv,bank_room book width base out _ (page_bits _) separate room,
    bank_room book width base out _ (page_bits _) separate room,bits.1,bits.2⟩

variable (D Q K L b M base) in
def joins (j : Fin 11) := table (j.castAdd 2)
variable (D Q K L b M base) in
def remap := table format
variable (D Q K L b M base) in
def comparator := table compare

variable (D Q K L b M base w) in
def program := mount book width w base
variable (D Q K L b M base) in
def installed (old : Memory w) := after book width base old
variable (D Q K L b M) in
def length := 26*2^width

variable (D Q K L b M base w) in
/-- Authentic code for the shift and nonlinear pages of each of the eleven
field joins, the filter, and the two-sided candidate comparison. -/
theorem setup (old : Memory w) (room : base+length D Q K L b M<2^w) :
    let done:=installed D Q K L b M base old
    (program D Q K L b M base w).Exec old done (4+10*length D Q K L b M) ∧
    (∀j,Static (joins D Q K L b M base j) (DescentPacking.PackedMatch.Local.Gather.setField (d:=b) j) M done) ∧
    Static (remap D Q K L b M base) (fun s (_:Cell 0)=>Machine.scalar D Q K L b s) M done ∧
    Static (comparator D Q K L b M base) (Stream.compareWord (p*p*Q) K L) M done ∧
    (∀a,a<base ∨ base+length D Q K L b M≤a→done a=old a) ∧
    DescentStaticWordColumn.names (program D Q K L b M base w)=15*(length D Q K L b M+1) ∧
    CheapCode (program D Q K L b M base w) := by
  have stage:=DescentOrdinaryAtomFieldRAM.ROM.run book width base old room
  exact ⟨stage.1,fun j=>binary_mounted _ M book width base old page_bits _ (insert_page j),
    binary_mounted _ M book width base old page_bits _ format_page,
    binary_mounted _ M book width base old page_bits _ compare_page,
    frame book width base old,stage.2,cheap book width w base⟩

theorem half_word (D Q K L b M w : ℕ) (bits : unit D Q K L b*M≤w/2) :
    length D Q K L b M≤26*2^(w/2) :=
  Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) bits)

theorem hardware {c : ℕ} (D Q K L b M base w out rows : ℕ) (slot : Fin c)
    (fields : Fin c→Fin 11→Expr) (limit : ℕ) (cost : ∀j i,(fields j i).work≤limit) :
    let op := operation slot (joins D Q K L b M base) fields
      (remap D Q K L b M base) (comparator D Q K L b M base)
    DescentStaticWordColumn.names ((program D Q K L b M base w).seq (scan w out rows op))≤
      15*(length D Q K L b M+1)+11+4*(1+c*(2*(13+11*(limit+11))+12)) := by
  intro op
  have work := operation_work slot (joins D Q K L b M base) fields (remap D Q K L b M base)
    (comparator D Q K L b M base) limit cost
  change op.work≤_ at work
  simp only [DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_scan,program,mount,
    DescentStaticWordColumn.names_mount,length]
  omega

section Issued
variable {F Pn J V E X T V₀ : Type} [Field F] [Fintype Pn] [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V]
    [Fintype E] [Fintype X] [Fintype T] {d k i O oldHosts H G : ℕ} {bits : Pn→ℕ}
    {W : DescentSixParty.MarkedWorld F d Pn bits} {gadget : DescentSixParty.PoweredGadget F} {price ε : ℝ}
variable (A : DescentSixParty.GroupStage W gadget price ε J V k) (native : W.graph.Edge↪ℕ)
    (schedule : DescentCompiler.AtomSchedule) (ready : A.StateBounds schedule i) (sites : Stage.Host J V k ↪ ℕ)
local notation "B" => Stage.source A native
local notation "U" => Stage.Host J V k
local notation "stream" => Stage.stream A native
variable (C : Blocks (Stage.source A native) E) (R : Fin oldHosts→Fin D→Option (Fin oldHosts))
    (symm : ∀v u i,R v i=some u→∃j,R u j=some v)
    (Z : Measured C R X T V₀ Q O K A.cap) (shelf : Measured.Shelf C R Z)
    (small : ∀h path x (s : ParentFilter.Source (breadth D) Q K A.cap) i,Machine.fields R (Z.venue h) path (Z.loc x).1 s i<2^b)
    (hosts : Fin H→Fin G→Option (Stage.Host J V k))
local notation "raw" => cell C R Z shelf small hosts
local notation "roster" => Measured.roster C R symm Z
local notation "expr" => expression (joins D Q K A.cap b M base)
local notation "filterBank" => remap D Q K A.cap b M base
local notation "cmpBank" => comparator D Q K A.cap b M base
local notation "fee" => length D Q K A.cap b M

omit [Fintype Pn] in
/-- Fresh physical program: materialize all common literal pages once, then classify
and rank the designated raw role in the same input state, for every packed lane. -/
theorem fresh (fields : Fin (p*O)→Fin 11→Expr) (dest : Bank) (old : Memory w)
    (early : ∀j i,(fields j i).Fits w base)
    (actual : ∀j i,DescentPackedZip.Source (fields j i) (fun h g=>columns (raw j h g) i) M old)
    (apart : base+fee≤dest.base) (space : dest.base+H*chunks G M<2^w)
    (slot : Fin (p*O)) (widthFit : Packed.bits A.cap*M≤w) (hm : 0<M)
    (h : Fin H) (g : Fin G) (host : U) (here : hosts h g=some host)
    (e : Local C host) (atSlot : (roster).address host e=slot) (target : Bool) :
    let mounted:=installed D Q K A.cap b M base old
    let op:=operation slot (joins D Q K A.cap b M base) fields filterBank cmpBank
    let core:=scan w dest.base (H*chunks G M) op
    let printed:=program D Q K A.cap b M base w
    let done:=image dest.base (H*chunks G M) op mounted
    let first:=(stream).symm (C.order ⟨e.val,⟨0,e.property.1⟩⟩)
    (printed.seq core).Exec old done ((4+10*fee)+(4+H*chunks G M*(2*op.work+4))) ∧
      digit (Packed.bits A.cap) (lane g hm).val (done (dest.base+(row H G M (position h g hm)).val)).val=
        (endpoint A native schedule ready sites target first).wire.val ∧
      (∀a,a<base ∨ dest.base+H*chunks G M≤a→done a=old a) ∧
      CheapCode (printed.seq core) := by
  intro mounted op core printed done first
  have below : dest.base<2^w := (Nat.le_add_right ..).trans_lt space
  have oldToNew : base≤dest.base := (Nat.le_add_right base fee).trans apart
  obtain ⟨write,start,remapped,compared,stable,_,cheapPrinted⟩ := setup D Q K A.cap b M base w old (apart.trans_lt below)
  have inputs (j : Fin (p*O)) (i : Fin 11) : DescentPackedZip.Source (fields j i)
      (fun h g=>columns (raw j h g) i) M mounted := by
    intro u
    exact (ProtocolRAM.eval_below (fields j i) _ old mounted (early j i) (fun z hz=>stable z (.inl hz))).trans (actual j i u)
  have bounds (j : Fin (p*O)) : DescentPacking.PackedMatch.Local.Gather.Bounds (d:=b) (M:=M) (w:=w)
      (joins D Q K A.cap b M base) (fields j) dest.base := by
    intro i
    have entry := layout (DescentPacking.PackedMatch.Local.Gather.setField (d:=b) (N:=11) i)
      (i.castAdd 2) (insert_page i) apart below (.lit 0) (fields j i) trivial
        (ProtocolRAMGeneratedWrite.fits_mono _ oldToNew (early j i))
    exact ⟨entry.right,entry.shift,entry.apply,entry.shiftBits,entry.applyBits⟩
  have filterOk (j : Fin (p*O)) := layout (fun s (_:Cell 0)=>Machine.scalar D Q K A.cap b s)
    format format_page apart below (DescentPacking.PackedMatch.Local.Gather.assembly (joins D Q K A.cap b M base) (fields j))
      (.lit 0) (DescentPacking.PackedMatch.Local.Gather.fits _ _ _ (bounds j) _) trivial
  have exprOk (j : Fin (p*O)) : (expr (fields j) filterBank).Fits w dest.base := by
    let t:=filterOk j
    exact ⟨t.apply,t.right,t.shift,t.left⟩
  have pairOk (j : Fin (p*O)) := layout (Stream.compareWord (p*p*Q) K A.cap)
    compare compare_page apart below _ _ (exprOk slot) (exprOk j)
  obtain ⟨rank,read,cheapRank⟩ := Fused.run A native schedule ready sites C R symm Z shelf small hosts
    (joins D Q K A.cap b M base) fields filterBank cmpBank dest mounted bounds start inputs filterOk
    remapped slot pairOk compared space widthFit hm h g host here e atSlot target
  refine ⟨?_,read,?_,cheap_seq cheapPrinted cheapRank⟩
  · apply Procedure.Exec.then write
    exact rank
  · intro a outside
    have same:=ProtocolRAMGeneratedWrite.frame_image dest.base (H*chunks G M) op mounted a
      (by rcases outside with lt|hi <;> omega)
    exact same.trans (stable a (by rcases outside with lt|hi <;> omega))

end Issued

end
end Hierarchy.DescentParallelBase.ParentFilter.Fused.TablesROM

end OAI
