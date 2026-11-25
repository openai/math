import OAI.Hierarchy.DescentTerminalShelfControl
import OAI.Hierarchy.DescentTerminalLeafDigits
import OAI.Hierarchy.DescentTerminalHeaderScatterRAM
import OAI.Hierarchy.ProtocolRAMWeightedScatter

namespace OAI
/-! # Native sparse add-and-decode of the real chronological leaf events -/
namespace Hierarchy.DescentTerminalLeafFold
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM
open PhysicalProcedure DescriptorExpr ProtocolRAM DescentTerminalPrintedFields DescentTerminalLeafDigits
open DescentTerminalHeaderScatter DescentTerminalRowBooks
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {q t V H N A w bits pool n : ℕ}
local notation "C" => Control q t H N A w V
local notation "uf" => capacity q t H N A w V

variable (tape : Fin pool→Option (Control q t H N A w V))
/-- The fiber of an option contains at most its one stored value. -/
noncomputable instance controlFiberFintype (o : Option (Control q t H N A w V)) :
    Fintype {x : Control q t H N A w V // o = some x} :=
  Fintype.ofInjective (fun _ => ()) fun x y _ =>
    Subtype.ext (Option.some.inj (x.property.symm.trans y.property))

abbrev Leaves (tape : Fin pool→Option (Control q t H N A w V)) : Type :=
  Sigma fun i : Fin pool => Sigma fun c : {x : Control q t H N A w V // tape i=some x} =>
    {j : Coord V H N A // (digit (emit c.val) j).val≠0}
def key (z : Leaves tape) :=
  (eventOrder (token (emit z.2.1.val) z.2.2.val z.2.2.property)).succ.val
def amount (z : Leaves tape) := weight (token (emit z.2.1.val) z.2.2.val z.2.2.property)

private theorem fiber_sum (o : Option (Control q t H N A w V)) :
    (∑ c : {x // o = some x}, ∑ j : {a : Coord V H N A // (digit (emit c.val) a).val ≠ 0},
      weight (token (emit c.val) j.val j.property)) = code o := by
  classical
  cases o with
  | none =>
    let : IsEmpty {x : Control q t H N A w V // (none : Option _) = some x} :=
      ⟨fun x => Option.some_ne_none x.val x.property.symm⟩
    simp [code]
  | some c =>
    let cc : {x : Control q t H N A w V // some c = some x} := ⟨c, rfl⟩
    rw [Finset.sum_eq_single cc]
    · exact (sparse_digits (emit c)).symm
    · intro x _ ne
      exact (ne (Subtype.ext (Option.some.inj x.property).symm)).elim
    · simp

set_option maxHeartbeats 1000000 in
theorem leaf_sum (i : Fin pool) : (∑a : Leaves tape,if a.1=i then amount tape a else 0)=code (tape i) := by
  classical
  unfold Leaves amount
  rw [Fintype.sum_sigma, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simpa only [Fintype.sum_sigma, ite_eq_left rfl, ite_true] using fiber_sum (tape i)
  · intro j _ ne
    apply Finset.sum_eq_zero
    intro b _
    exact ite_eq_right ne

variable (choose : Fin n→Option (Leaves tape))
    (unique : ∀z : Leaves tape,∃!i,choose i=some z)

def destination (base : ℕ) (i : Fin n) := base+((choose i).map Sigma.fst |>.map Fin.val |>.getD pool)
def contribution (i : Fin n) := ((choose i).map (amount tape)).getD 0

include unique in
theorem sum_destination (base : ℕ) (i : Fin pool) :
    ProtocolRAMWeightedScatter.sumAt (destination tape choose base) (contribution tape choose) (base+i.val)=code (tape i) := by
  classical
  let pos (z : Leaves tape) := (unique z).choose
  have picks (z : Leaves tape) : choose (pos z)=some z := (unique z).choose_spec.1
  let val (j : Fin n) (z : Leaves tape) := if choose j=some z ∧ z.1=i then amount tape z else 0
  have per (j : Fin n) :
      (if destination tape choose base j=base+i.val then contribution tape choose j else 0)=∑z,val j z := by
    cases hj : choose j with
    | none=>simp [destination,contribution,hj,val]
    | some z=>
      rw [Finset.sum_eq_single z]
      · simp [destination,contribution,hj,val,Fin.ext_iff]
      · intro b _ ne; simp [val,hj,ne.symm]
      · simp
  unfold ProtocolRAMWeightedScatter.sumAt
  simp_rw [per]
  rw [Finset.sum_comm,←leaf_sum tape i]
  apply Finset.sum_congr rfl
  intro z _
  rw [Finset.sum_eq_single (pos z)]
  · simp [val,picks]
  · intro j _ ne
    have off:choose j≠some z:=fun e=>ne ((unique z).choose_spec.2 j e)
    simp [val,off]
  · simp

structure Layout where
  half : Bank
  lanes : Bank
  home : Bank
  event : Bank
  weight : Bank
  cells : Bank
  occupancy : Bank
  table : Bank

def address (L : Layout) : Expr := .op .add (.lit L.cells.base) (.lookup L.home (.lookup L.half .row))
def low (L : Layout) : Expr := bounded L.cells (address L)
def high (L : Layout) : Expr := .lookup L.weight (.lookup L.event (.lookup L.half .row))
def lookup (L : Layout) : Expr := .branch .eq (.lookup L.occupancy .row) (.lit 0) (.lit 0) (.lookup L.table (.lookup L.cells .row))
def row (L : Layout) := stage (low L) (high L) L.lanes

def program (bits src pool n out : ℕ) (L : Layout) :=
  (((scan bits L.cells.base (pool+1) (.lit 0)).seq (scan bits src (2*n) (row L))).seq
    (ProtocolRAMWeightedScatter.program bits src n)).seq (scan bits out pool (lookup L))
def work (L : Layout) (pool n : ℕ) :=
  (((4+(2*Expr.work (.lit 0)+4)*(pool+1))+(4+(2*(row L).work+4)*(2*n)))+(3+12*n))+
    (4+(2*(lookup L).work+4)*pool)
theorem cheap (bits src pool n out : ℕ) (L : Layout) : CheapCode (program bits src pool n out L) := by
  let clear := scan bits L.cells.base (pool+1) (.lit 0)
  let write := scan bits src (2*n) (row L)
  let add := ProtocolRAMWeightedScatter.program bits src n
  let print := scan bits out pool (lookup L)
  exact @cheap_seq bits ((clear.seq write).seq add) print
    (@cheap_seq bits (clear.seq write) add
      (@cheap_seq bits clear write (@scan_cheap bits L.cells.base (pool+1) (.lit 0))
        (@scan_cheap bits src (2*n) (row L)))
      (@ProtocolRAMWeightedScatter.cheap bits src n))
    (@scan_cheap bits out pool (lookup L))

theorem scans (L : Layout) (src pool n out : ℕ) {start blank stage sum finish : Memory bits}
    (init : (scan bits L.cells.base (pool+1) (.lit 0)).Exec start blank (4+(pool+1)*(2*Expr.work (.lit 0)+4)))
    (write : (scan bits src (2*n) (row L)).Exec blank stage (4+(2*n)*(2*(row L).work+4)))
    (add : (ProtocolRAMWeightedScatter.program bits src n).Exec stage sum (3+12*n))
    (print : (scan bits out pool (lookup L)).Exec sum finish (4+pool*(2*(lookup L).work+4))) :
    (program bits src pool n out L).Exec start finish (work L pool n) := by
  let clear := scan bits L.cells.base (pool+1) (.lit 0)
  let rows := scan bits src (2*n) (row L)
  let scatter := ProtocolRAMWeightedScatter.program bits src n
  let decode := scan bits out pool (lookup L)
  rw [work,Nat.mul_comm (2*Expr.work (.lit 0)+4) (pool+1),
    Nat.mul_comm (2*(row L).work+4) (2*n),Nat.mul_comm (2*(lookup L).work+4) pool]
  have a := @Procedure.Exec.then bits clear rows start blank stage _ _ init write
  have b := @Procedure.Exec.then bits (clear.seq rows) scatter start stage sum _ _ a add
  exact @Procedure.Exec.then bits ((clear.seq rows).seq scatter) decode start sum finish _ _ b print

/-- The token address is the numeric column-local rank from the original
archive; each true nonzero field is written exactly once across all records.
A zero padding event targets the dedicated extra cell. -/
structure Arrival (L : Layout) (m : Memory bits) : Prop where
  half : ∀(i : Fin n) (j : Fin 2),L.half.read m ((field i j).val:Word bits)=(i.val:Word bits)
  lane : ∀(i : Fin n) (j : Fin 2),L.lanes.read m ((field i j).val:Word bits)=(j.val:Word bits)
  home : ∀i : Fin n,L.home.read m (i.val:Word bits)=
    (((choose i).map Sigma.fst |>.map Fin.val |>.getD pool):Word bits)
  token : ∀i : Fin n,L.event.read m (i.val:Word bits)=(((choose i).map (key tape)).getD 0:Word bits)
  weights : ∀j : Fin (tokenCount q t V H N A w+1),L.weight.read m (j.val:Word bits)=
    ((dictionary (q:=q) (t:=t) (V:=V) (H:=H) (N:=N) (A:=A) (w:=w))[j.val]'
      (by simpa only [dictionary,List.length_ofFn] using j.isLt):Word bits)

theorem row_eval (L : Layout) (m : Memory bits) (inputs : Arrival tape choose L m) (pos : 0<bits)
    {src : ℕ} (fit : L.cells.Fits bits src) (space : pool<L.cells.size) (room : src<2^bits)
    (i : Fin n) (j : Fin 2) :
    (row L).eval m ((field i j).val:Word bits)=if j=0 then (destination tape choose L.cells.base i:Word bits)
      else (contribution tape choose i:Word bits) := by
  rw [row,lane_read _ _ _ _ _ _ pos (inputs.lane i j)]
  by_cases h:j=0
  · rw [ite_eq_left h,ite_eq_left h]
    have addr : (address L).eval m ((field i j).val:Word bits)=(destination tape choose L.cells.base i:Word bits) := by
      simp [address,Expr.eval,inputs.half,inputs.home,destination,Nat.cast_add,RowOp.opcode,BinaryOp.eval]
    apply Eq.trans _ addr
    apply bounded_exact L.cells (address L) _ _ fit room _ addr
    cases e:choose i with
    | none=>
      simp only [Option.map_none,Option.getD_none]
      exact space
    | some v=>
      simp only [Option.map_some,Option.getD_some]
      exact v.1.isLt.trans space
  · simp only [h,ite_false,high,Expr.eval,inputs.half,inputs.token]
    cases hi:choose i with
    | none=>simpa [hi,dictionary,contribution] using inputs.weights (0:Fin (tokenCount q t V H N A w+1))
    | some z=>
      let event := token (emit z.2.1.val) z.2.2.val z.2.2.property
      have word := inputs.weights (eventOrder event).succ
      rw [dictionary_token event] at word
      simpa only [hi,Option.map_some,Option.getD_some,key,contribution,amount,event] using word

def cleared (L : Layout) (pool : ℕ) (m : Memory bits) := image L.cells.base (pool+1) (.lit 0) m
def staged (L : Layout) (pool n src : ℕ) (m : Memory bits) := image src (2*n) (row L) (cleared L pool m)
def merged (L : Layout) (m : Memory bits) (src : ℕ) :=
  ProtocolRAMWeightedScatter.image (destination tape choose L.cells.base) (contribution tape choose) (staged L pool n src m) n

include unique in
theorem run (L : Layout) (m : Memory bits) (src out : ℕ) (pos : 0<bits)
    (fits : (row L).Fits bits L.cells.base) (fitStage : (row L).Fits bits src)
    (fitFinal : (lookup L).Fits bits out) (cellFit : L.cells.Fits bits src)
    (room : pool+1 ≤ L.cells.size) (_sep : src+2*n ≤ out) (endAt : out+pool<2^bits)
    (stagingRoom : src+2*n<2^bits) (input : Arrival tape choose L m)
    (mask : ∀i : Fin pool,L.occupancy.read m (i.val:Word bits)=((if (tape i).isSome then 1 else 0:ℕ):Word bits))
    (table : ∀j : Fin (uf).total,L.table.read m (j.val:Word bits)=
      ((headerTable q t H N A w V)[j.val]'(by simpa only [headerTable,List.length_ofFn] using j.isLt):Word bits))
    (beforeMask : L.occupancy.Fits bits L.cells.base) (beforeTable : L.table.Fits bits L.cells.base) :
    let before:=merged tape choose L m src
    let final:=image out pool (lookup L) before
    (program bits src pool n out L).Exec m final (work L pool n) ∧
      ∀i : Fin pool,final (out+i.val)=(DescentTerminalPrintedFieldsRAM.expected (tape i):Word bits) := by
  intro before final
  let base:=L.cells.base
  let dst:=destination tape choose base
  let val:=contribution tape choose
  have endCells:=cellFit.2.2
  have dstBounds (i : Fin n) : base ≤ dst i ∧ dst i ≤ base+pool := by
    cases h:choose i with
    | none=>
      change base ≤ base+((choose i).map Sigma.fst |>.map Fin.val |>.getD pool) ∧ _
      simp only [dst,destination,h,Option.map_none,Option.getD_none]
      exact ⟨Nat.le_add_right _ _,le_rfl⟩
    | some e=>
      simp only [dst,destination,h,Option.map_some,Option.getD_some]
      exact ⟨Nat.le_add_right _ _,Nat.add_le_add_left e.1.isLt.le base⟩
  have zero:=@scan_exec bits base (pool+1) (.lit 0) m trivial (by dsimp [base];omega)
  have write:=@scan_exec bits src (2*n) (row L) (cleared L pool m) fitStage stagingRoom
  have stable (a : ℕ) (h : a<base) : cleared L pool m a=m a := by
    change a<L.cells.base at h
    simp [cleared,image,fillSegment,not_le.mpr h]
  have pair (i : Fin n) (j : Fin 2) :
      staged L pool n src m (src+(field i j).val)=
        if j=0 then (dst i:Word bits) else (val i:Word bits) := by
    rw [staged,DescentTerminalDenseHeaderRAM.at_image,eval_below (row L) _ m _ fits stable]
    exact row_eval tape choose L m input pos cellFit (by omega) (by omega) i j
  have add:=@ProtocolRAMWeightedScatter.run bits n src dst val (staged L pool n src m) stagingRoom.le
    (fun i=>(dstBounds i).2.trans_lt (by dsimp [base];omega))
    (fun i=>Or.inl ((dstBounds i).2.trans_lt (by dsimp [base];omega))) (fun i=>⟨
      by simpa [field] using pair i 0,by simpa [field,Nat.add_assoc] using pair i 1⟩)
  have current (i : Fin pool) : L.cells.read before (i.val:Word bits)=(code (tape i):Word bits) := by
    rw [DescentTerminalDenseHeaderRAM.bank_nat before cellFit (by omega)]
    have small : L.cells.base+i.val<src := by have:=i.isLt;omega
    have blank : staged L pool n src m (base+i.val)=0 := by
      simp [staged,cleared,image,base,fillSegment,not_le.mpr small,show L.cells.base+i.val<L.cells.base+(pool+1) by have:=i.isLt;omega,Expr.eval]
    change staged L pool n src m (base+i.val)+(ProtocolRAMWeightedScatter.partialLoad dst val (base+i.val) n:Word bits)=_
    have sum:=sum_destination tape choose unique base i
    simpa [blank,ProtocolRAMWeightedScatter.partialLoad,ProtocolRAMWeightedScatter.sumAt] using
      congrArg (fun k : ℕ=>(k:Word bits)) sum
  have frame (a : ℕ) (h : a<base) : before a=m a := by
    have lo:=ProtocolRAMWeightedScatter.frame dst val (staged L pool n src m) n a (fun i ne=>by have:=(dstBounds i).1;omega)
    change ProtocolRAMWeightedScatter.image dst val (staged L pool n src m) n a=_
    rw [lo]
    have be:a<src:=by dsimp [base] at h;omega
    simp [staged,image,fillSegment,not_le.mpr be,stable a h]
  have bank (b : Bank) (f : b.Fits bits base) (x : Word bits) : b.read before x=b.read m x := by
    apply frame
    have h:=Nat.mod_lt x.val f.1
    have last:=f.2.2
    omega
  have endRun:=@scan_exec bits out pool (lookup L) before fitFinal endAt
  refine ⟨@scans bits L src pool n out m (cleared L pool m) (staged L pool n src m) before final
    zero write add endRun,?_⟩
  intro i
  change image out pool (lookup L) before (out+i.val)=_
  rw [DescentTerminalDenseHeaderRAM.at_image out (lookup L) before i]
  cases h:tape i with
  | none=>simp [lookup,Expr.eval,DescriptorExpr.Comparison.test,bank _ beforeMask,mask,h,DescentTerminalPrintedFieldsRAM.expected]
  | some c=>
    have nonzero : (1:Word bits)≠0 := by
      intro e
      have p : 1<2^bits:=Nat.one_lt_pow (Nat.ne_of_gt pos) (by decide)
      have vals:=congrArg Fin.val e
      change 1%(2^bits)=0 at vals
      simp [Nat.mod_eq_of_lt p] at vals
    have word:=table (serial uf (digits (emit c)))
    rw [table_actual c] at word
    simp only [lookup,Expr.eval,DescriptorExpr.Comparison.test,bank _ beforeMask,mask,h,Option.isSome_some,
      ite_true,Nat.cast_one,Nat.cast_zero,beq_iff_eq,nonzero,ite_false,current,code,Option.map_some,
      Option.getD_some,bank _ beforeTable]
    simpa [DescentTerminalPrintedFieldsRAM.expected,h,Nat.ne_of_gt pos] using word

end
end Hierarchy.DescentTerminalLeafFold

end OAI
