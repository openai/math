import OAI.Hierarchy.DescentTerminalMergedPrint
import OAI.Hierarchy.DescentTerminalPackedLeaves
import OAI.Hierarchy.DescentTerminalLeafPlan
import OAI.Hierarchy.DescentTerminalLeafHeap

namespace OAI
/-! # Native checked packed-event updates without a word clock per small operand -/
namespace Hierarchy.DescentTerminalPackedLeaves
open DescentTerminalPrintedFields DescentTerminalRowBooks Computability.VPVNP.BurstRAM PrivateRAM
open DescentTerminalHeaderScatter ThreeFlat.RAM
open PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {q t H N A w V pool n b lanes bits : ℕ}
local notation "C" => Control q t H N A w V
local notation "u" => capacity q t H N A w V
variable (tape : Fin pool→Option (Control q t H N A w V)) (room : DescentTerminalLeafDigits.tokenCount q t V H N A w+1≤2^b)
abbrev Chunk:= (i : Fin pool)×Fin (count (tape i) lanes)
def chunks := ∑i,count (tape i) lanes
def order : Chunk (lanes:=lanes) tape ≃ Fin (chunks (lanes:=lanes) tape) :=
  ProtocolRAMPortRanks.enumerate (fun i=>count (tape i) lanes) Fin.val Fin.val_injective

def active (i : Fin n) := if h : i.val<chunks (lanes:=lanes) tape then some ((order tape).symm ⟨i.val,h⟩) else none
def src (i : Fin n) := ((active (lanes:=lanes) tape i).map Sigma.fst |>.map Fin.val |>.getD pool)
def key (i : Fin n) := ((active (lanes:=lanes) tape i).map (fun z=>(serialize (piece (lanes:=lanes) room (tape z.1) z.2.val)).val)).getD 0
def val (i : Fin n) := ((active (lanes:=lanes) tape i).map (fun z=>amount (tape z.1) z.2.val lanes)).getD 0

theorem reached (lp : 0<lanes) (enough : chunks (lanes:=lanes) tape ≤ n) (i : Fin pool) :
    (∑k : Fin n,if src (lanes:=lanes) tape k=i.val then val (lanes:=lanes) tape k else 0)=DescentTerminalLeafFold.code (tape i) := by
  let f (k : ℕ):=if hk:k<chunks (lanes:=lanes) tape then
    let z:=(order (lanes:=lanes) tape).symm ⟨k,hk⟩
    if z.1=i then amount (tape z.1) z.2.val lanes else 0 else 0
  have one (k : Fin n) : (if src (lanes:=lanes) tape k=i.val then val (lanes:=lanes) tape k else 0)=f k.val := by
    by_cases h:k.val<chunks (lanes:=lanes) tape <;> simp [src,val,active,f,h,Fin.ext_iff]
  simp_rw [one]
  have eqn : (∑k : Fin n,f k.val)=∑k : Fin (chunks (lanes:=lanes) tape),f k.val := by
    rw [Fin.sum_univ_eq_sum_range,Fin.sum_univ_eq_sum_range]
    symm
    exact Finset.sum_subset (Finset.range_mono enough) fun k _ h=>by simp [f,show ¬k<chunks (lanes:=lanes) tape by simpa using h]
  let readAt (z : Chunk (lanes:=lanes) tape) :=
    if z.1=i then amount (tape z.1) z.2.val lanes else 0
  have atOrder (z : Chunk (lanes:=lanes) tape) :
      f ((order (lanes:=lanes) tape) z).val=readAt z := by
    dsimp only [f]
    rw [dite_eq_left ((order (lanes:=lanes) tape) z).isLt]
    change readAt ((order (lanes:=lanes) tape).symm ((order (lanes:=lanes) tape) z))=readAt z
    exact congrArg readAt ((order (lanes:=lanes) tape).symm_apply_apply z)
  rw [eqn,←(order (lanes:=lanes) tape).sum_comp (fun k=>f k.val)]
  simp_rw [atOrder]
  rw [Fintype.sum_sigma,Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simpa only [readAt,ite_eq_left rfl,ite_true] using block_sum lp (tape i)
  · intro j _ ne
    simp [readAt,ne]

structure Arrival (L : DescentTerminalLeafFold.Layout) (m : Memory bits) : Prop where
  half : ∀(i : Fin n) (j : Fin 2),L.half.read m ((field i j).val:Word bits)=(i.val:Word bits)
  lane : ∀(i : Fin n) (j : Fin 2),L.lanes.read m ((field i j).val:Word bits)=(j.val:Word bits)
  home : ∀i : Fin n,L.home.read m (i.val:Word bits)=(src (lanes:=lanes) tape i:Word bits)
  bundle : ∀i : Fin n,L.event.read m (i.val:Word bits)=(key (lanes:=lanes) tape room i:Word bits)
  table : ∀j : Fin (2^(b*lanes)),L.weight.read m (j.val:Word bits)=
    ((table b lanes q t V H N A w)[j.val]'(by simpa only [table,List.length_ofFn] using j.isLt):Word bits)

theorem zero_table : (table b lanes q t V H N A w)[0]'(by simp [table])=0 := by
  let zero : Fin lanes → Fin (2^b) := fun _ => 0
  have packed : serialize zero=0 := by
    apply Fin.ext
    change (finFunctionFinEquiv zero).val=0
    rw [finFunctionFinEquiv_apply]
    simp [zero]
  have z : unpack (0:Fin (2^(b*lanes)))=(fun _=>0) := by
    rw [←packed]
    exact unpack_serial zero
  simp [table,z,DescentTerminalLeafDigits.dictionary]

theorem row_word (L : DescentTerminalLeafFold.Layout) (m : Memory bits) (input : Arrival (n:=n) (lanes:=lanes) tape room L m)
    (i : Fin n) : (DescentTerminalLeafFold.high L).eval m ((field i 1).val:Word bits)=(val (lanes:=lanes) tape i:Word bits) := by
  simp only [DescentTerminalLeafFold.high,Expr.eval,input.half,input.bundle]
  cases live:active (lanes:=lanes) tape i with
  | none=>simpa [key,val,live,zero_table] using input.table (0:Fin (2^(b*lanes)))
  | some a=>
    have word:=input.table (serialize (piece (lanes:=lanes) room (tape a.1) a.2.val))
    rw [read room (tape a.1) a.2.val] at word
    simpa only [key,val,live,Option.map_some,Option.getD_some] using word

theorem read_merge (L : DescentTerminalLeafFold.Layout) (m : Memory bits) (srcBase : ℕ) (lp : 0<lanes)
    (enough : chunks (lanes:=lanes) tape ≤ n) (input : Arrival (n:=n) (lanes:=lanes) tape room L m)
    (cell : L.cells.Fits bits srcBase) (space : pool+1≤L.cells.size) (top : srcBase<2^bits)
    (rows : (DescentTerminalLeafFold.row L).Fits bits L.cells.base) (i : Fin pool) :
    L.cells.read (DescentTerminalLeafFold.reduced L m pool n srcBase) (i.val:Word bits)=(DescentTerminalLeafFold.code (tape i):Word bits) := by
  let clear:=DescentTerminalLeafFold.cleared L pool m
  let record:=DescentTerminalLeafFold.selected L m pool n
  have same {x} (b:x<L.cells.base):clear x=m x:=by simp [clear,DescentTerminalLeafFold.cleared,image,fillSegment,not_le.mpr b]
  have lo : (DescentTerminalLeafFold.low L).Fits bits L.cells.base:=rows.2.2.1
  have hi : (DescentTerminalLeafFold.high L).Fits bits L.cells.base:=rows.2.2.2
  have bounds (k : Fin n) : src (lanes:=lanes) tape k≤pool := by
    cases z:active (lanes:=lanes) tape k with
    | none=>simp only [src,z,Option.map_none,Option.getD_none,le_rfl]
    | some a=>
      simp only [src,z,Option.map_some,Option.getD_some]
      exact a.1.isLt.le
  have first (k : Fin n) : (record k).1.val=L.cells.base+src (lanes:=lanes) tape k := by
    have add : (DescentTerminalLeafFold.address L).eval m ((field k 0).val:Word bits)=((L.cells.base+src (lanes:=lanes) tape k:ℕ):Word bits) := by
      simp [DescentTerminalLeafFold.address,Expr.eval,RowOp.opcode,BinaryOp.eval,input.half,input.home,Nat.cast_add]
    have native:=bounded_exact L.cells (DescentTerminalLeafFold.address L) m ((field k 0).val:Word bits) cell top
      ((bounds k).trans_lt (by omega)) add
    change ((DescentTerminalLeafFold.low L).eval clear _).val=_
    rw [eval_below _ _ m _ lo (fun a h=>same h),DescentTerminalLeafFold.low,native,add,Fin.val_cast_of_lt (by have:=cell.2.2;have:=bounds k;omega)]
  have values (k : Fin n) : ((record k).2.val:Word bits)=(val (lanes:=lanes) tape k:Word bits) := by
    rw [Fin.cast_val_eq_self]
    change (DescentTerminalLeafFold.high L).eval clear _=_
    rw [eval_below _ _ m _ hi (fun a h=>same h),row_word tape room L m input]
  rw [DescentTerminalDenseHeaderRAM.bank_nat _ cell (by omega)]
  have atZero : DescentTerminalLeafFold.staged L pool n srcBase m (L.cells.base+i.val)=0 := by
    have prior:L.cells.base+i.val<srcBase:=by have:=cell.2.2;have:=i.isLt;omega
    simp [DescentTerminalLeafFold.staged,DescentTerminalLeafFold.cleared,image,fillSegment,not_le.mpr prior,Expr.eval,show L.cells.base+i.val<L.cells.base+(pool+1) by omega]
  change DescentTerminalLeafFold.staged L pool n srcBase m (L.cells.base+i.val)+(_ : ℕ)=_
  rw [atZero,zero_add]
  change ((∑k:Fin n,if k.val<n ∧ (record k).1.val=L.cells.base+i.val then (record k).2.val else 0:ℕ):Word bits)=_
  simp only [Fin.is_lt,true_and,first,Nat.add_left_cancel_iff,Nat.cast_sum]
  rw [←reached tape lp enough i,Nat.cast_sum]
  apply Finset.sum_congr rfl
  intro k _
  split <;> simp [*]

theorem printed (L : DescentTerminalLeafFold.Layout) (m : Memory bits) (srcBase out : ℕ) (lp : 0<lanes)
    (pos : 0<bits) (enough : chunks (lanes:=lanes) tape ≤ n)
    (input : Arrival (n:=n) (lanes:=lanes) tape room L m)
    (cell : L.cells.Fits bits srcBase) (space : pool+1≤L.cells.size) (top : srcBase<2^bits)
    (rows : (DescentTerminalLeafFold.row L).Fits bits L.cells.base)
    (beforeMask : L.occupancy.Fits bits L.cells.base) (beforeTable : L.table.Fits bits L.cells.base)
    (mask : ∀i : Fin pool,L.occupancy.read m (i.val:Word bits)=((if (tape i).isSome then 1 else 0:ℕ):Word bits))
    (headers : ∀j : Fin (u).total,L.table.read m (j.val:Word bits)=
      ((headerTable q t H N A w V)[j.val]'(by simpa only [headerTable,List.length_ofFn] using j.isLt):Word bits))
    (i : Fin pool) : DescentTerminalLeafFold.final L m pool n srcBase out (out+i.val)=
      (DescentTerminalPrintedFieldsRAM.expected (tape i):Word bits) := by
  let reduced:=DescentTerminalLeafFold.reduced L m pool n srcBase
  have frame (a : ℕ) (early : a<L.cells.base) : reduced a=m a := by
    have off (k:Fin n) : (DescentTerminalLeafFold.selected L m pool n k).1.val≠a := by
      change ((bounded L.cells _).eval _ _).val≠a
      rw [bounded_val L.cells _ _ _ cell top]
      omega
    have ahead:a<srcBase:=by have:=cell.2.2;omega
    change ProtocolRAMWeightedScatter.image _ _ (DescentTerminalLeafFold.staged L pool n srcBase m) n a=_
    rw [ProtocolRAMWeightedScatter.frame _ _ _ _ _ off]
    simp [DescentTerminalLeafFold.staged,DescentTerminalLeafFold.cleared,image,fillSegment,not_le.mpr early,not_le.mpr ahead]
  have bank (b:Bank) (small:b.Fits bits L.cells.base) (j:Word bits) : b.read reduced j=b.read m j := by
    apply frame
    have:=small.2.2;have:=Nat.mod_lt j.val small.1;omega
  have read : L.cells.read reduced (i.val:Word bits)=(DescentTerminalLeafFold.code (tape i):Word bits) :=
    read_merge tape room L m srcBase lp enough input cell space top rows i
  change image out pool (DescentTerminalLeafFold.lookup L) reduced (out+i.val)=_
  rw [DescentTerminalDenseHeaderRAM.at_image]
  cases h:tape i with
  | none=>simp [DescentTerminalLeafFold.lookup,Expr.eval,DescriptorExpr.Comparison.test,bank _ beforeMask,mask,h,DescentTerminalPrintedFieldsRAM.expected]
  | some c=>
    have nz : (1:Word bits)≠0:=by
      have p:1<2^bits:=Nat.one_lt_pow (Nat.ne_of_gt pos) (by decide)
      intro e
      have equal:=congrArg Fin.val e
      change 1%(2^bits)=0 at equal
      simp [Nat.mod_eq_of_lt p] at equal
    have word:=headers (serial u (digits (emit c)))
    rw [table_actual c] at word
    simp only [DescentTerminalLeafFold.lookup,Expr.eval,DescriptorExpr.Comparison.test,bank _ beforeMask,
      mask,h,Option.isSome_some,ite_true,Nat.cast_one,Nat.cast_zero,beq_iff_eq,nz,ite_false,read,
      DescentTerminalLeafFold.code,Option.map_some,Option.getD_some,bank _ beforeTable]
    simpa [DescentTerminalPrintedFieldsRAM.expected,h,Nat.ne_of_gt pos] using word

theorem printed_self (L : DescentTerminalLeafFold.Layout) (m : Memory bits) (srcBase out : ℕ) (lp : 0<lanes)
    (pos : 0<bits) (enough : chunks (lanes:=lanes) tape ≤ n)
    (input : Arrival (n:=n) (lanes:=lanes) tape room L m)
    (cell : L.cells.Fits bits srcBase) (space : pool+1≤L.cells.size) (top : srcBase<2^bits)
    (rows : (DescentTerminalLeafFold.row L).Fits bits L.cells.base)
    (same : L.occupancy=L.cells) (beforeTable : L.table.Fits bits L.cells.base)
    (totalFit : (u).total≤2^bits) (occupied : ∀i c,tape i=some c → c.1.val≠0)
    (headers : ∀j : Fin (u).total,L.table.read m (j.val:Word bits)=
      ((headerTable q t H N A w V)[j.val]'(by simpa only [headerTable,List.length_ofFn] using j.isLt):Word bits))
    (i : Fin pool) : DescentTerminalLeafFold.final L m pool n srcBase out (out+i.val)=
      (DescentTerminalPrintedFieldsRAM.expected (tape i):Word bits) :=
  print_merged tape L m srcBase out pos (read_merge tape room L m srcBase lp enough input cell space top rows)
    cell space top same beforeTable totalFit occupied headers i

theorem packed_room (s h digits : ℕ) (positive : 0<digits) (fits : 2*digits≤h)
    (chosen : s=h/(2*digits)) : 0<s ∧ digits*s≤h/2 ∧ h≤4*digits*s := by
  subst s
  have d : 0<2*digits:=by omega
  have n : 0<h/(2*digits):=Nat.div_pos fits d
  have a:=Nat.div_mul_le_self h (2*digits)
  have b:=Nat.mod_lt h d
  have c:=Nat.mod_add_div h (2*digits)
  have large:=Nat.mul_le_mul_left (2*digits) n
  constructor
  · exact n
  constructor
  · apply (Nat.le_div_iff_mul_le (by decide:0<2)).2
    nlinarith only [a]
  · nlinarith only [c,b,large]

end
end Hierarchy.DescentTerminalPackedLeaves

end OAI
