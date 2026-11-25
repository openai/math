import OAI.Hierarchy.DescentTerminalPackedPositions
import OAI.Hierarchy.DescentTerminalHeaderAny

namespace OAI
/-! # Real bounded native reading of two predecessor chunks across every field family -/
namespace Hierarchy.DescentTerminalVertexFields
open DescentTerminalSiteShelves DescentTerminalDenseWindow DescentTerminalDenseHeader
open Computability.VPVNP.BurstRAM PrivateRAM Computability.VPVNP.RAMSerialization ThreeFlat.RAM PhysicalProcedure DescriptorExpr ProtocolRAM
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable {q t H N A w V M S B bits : ℕ}
local notation "width" => span q t H N A w
local notation "Group" => Panels (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) M
local notation "G" => tablesize (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=M)
local notation "cap" => widthAt (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) M
local notation "factor" => stride (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=M)
local notation "Raw" => Home (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (V:=V)

def paired : Fin M×(Group×Group)≃Fin (M*(G*G)) :=
  (Equiv.prodCongr (Equiv.refl _) ((Equiv.prodCongr finPiFinEquiv finPiFinEquiv).trans finProdFinEquiv)).trans finProdFinEquiv

local notation "pairCode" => paired (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) (M:=M)

def siblingROM (enough : V≤M) (fit : V*width≤B) (j : Fin (M*(G*G))) :=
  let z:Fin M×(Group×Group):=(pairCode).symm j
  clippedPage (joinGroups (q:=q) (t:=t) (H:=H) (N:=N) (A:=A) (w:=w) enough z.1 z.2.1 z.2.2) fit

theorem paired_val (r : Fin M) (lo hi : Group) :
    (pairCode (r,lo,hi)).val=r.val*(G*G)+(finPiFinEquiv lo).val*G+(finPiFinEquiv hi).val := by
  change ((finPiFinEquiv hi).val+G*(finPiFinEquiv lo).val)+(G*G)*r.val=_
  ring

theorem paired_room (h : ℕ) (space : Nat.clog 2 M+2*(M*width)≤h/2) : M*(G*G)≤2^(h/2) := by
  have volumeEq : G=2^(M*width) := by unfold tablesize;rw [Finset.prod_pow_eq_pow_sum,volume]
  rw [volumeEq]
  calc
    _ ≤ 2^(Nat.clog 2 M)*(2^(M*width)*2^(M*width)) := Nat.mul_le_mul_right _ (Nat.le_pow_clog (by decide) M)
    _ ≤ _ := by rw [←pow_add,←pow_add];exact Nat.pow_le_pow_right (by decide) (by omega)

structure PackedShelf where
  «prefix» : DescentTerminalDenseHeaderRAM.Layout
  columns : Fin 8→Bank
  low : Fin 8→Bank
  high : Fin 8→Bank
  residue : Bank
  table : Bank

def partExpr (L : PackedShelf) (side : Bool) (f : Fin 8) : Expr :=
  let base:=Expr.lookup L.prefix.index .row
  let loc:=if side then Expr.op .add base (.lit 1) else base
  .lookup (if side then L.high f else L.low f) (.lookup (L.columns f) loc)

def assemble (L : PackedShelf) : Expr :=
  .lookup L.table (.op .add (.lookup L.residue (DescentTerminalDenseHeaderRAM.previous L.prefix.rem))
    (.op .add (sumExpr (partExpr L false) (List.finRange 8)) (sumExpr (partExpr L true) (List.finRange 8))))

private theorem sum_work_of_const {ι : Type} (e : ι → Expr) (n : ℕ)
    (work : ∀ f, (e f).work=n) (l : List ι) :
    (sumExpr e l).work=l.length*(n+1)+1 := by
  induction l with
  | nil => simp [sumExpr,Expr.work]
  | cons f l ih =>
    simp only [sumExpr,Expr.work,work,ih,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem assemble_work (L : PackedShelf) : (assemble L).work=332 := by
  have lo : (sumExpr (partExpr L false) (List.finRange 8)).work=145 := by
    rw [sum_work_of_const (partExpr L false) 17 (fun _=>rfl)]; decide
  have hi : (sumExpr (partExpr L true) (List.finRange 8)).work=161 := by
    rw [sum_work_of_const (partExpr L true) 19 (fun _=>rfl)]; decide
  change ((DescentTerminalDenseHeaderRAM.previous L.prefix.rem).work+5+
      ((sumExpr (partExpr L false) (List.finRange 8)).work+
       (sumExpr (partExpr L true) (List.finRange 8)).work+1)+1)+5=332
  rw [lo,hi]
  norm_num [DescentTerminalDenseHeaderRAM.previous,Expr.work]

def framedExpr (L : PackedShelf) (S : ℕ) : Expr := .branch .lt .row (.lit S) (assemble L) (.lit 0)
theorem frame_work (L : PackedShelf) : (framedExpr L S).work=337 := by
  change 2+1+(assemble L).work+1+1=337
  rw [assemble_work]

structure Resident (L : PackedShelf) (mem : Memory bits) (books : Fin S→Raw) (stream : ℕ→Group)
    (enough : V≤M) (fit : V*width≤B) : Prop where
  columns : ∀i : Fin S,∀d:Fin 2,∀f,(L.columns f).read mem ((population books i.val/M+d.val:ℕ):Word bits)=
    ((stream (population books i.val/M+d.val) f).val:Word bits)
  low : ∀f,∀z:Word (cap f),(L.low f).read mem (z.val:Word bits)=((z.val*factor f*G:ℕ):Word bits)
  high : ∀f,∀z:Word (cap f),(L.high f).read mem (z.val:Word bits)=((z.val*factor f:ℕ):Word bits)
  residue : ∀r:Fin M,L.residue.read mem (r.val:Word bits)=((r.val*(G*G):ℕ):Word bits)
  dictionary : ∀k : Fin (M*(G*G)),L.table.read mem (k.val:Word bits)=((siblingROM enough fit k).val:Word bits)

private theorem sum_ordinal (data : Group) (m : ℕ) :
    ((List.finRange 8).map fun f=>(data f).val*factor f*m).sum=(finPiFinEquiv data).val*m := by
  rw [finPiFinEquiv_apply]
  change (List.ofFn fun f=>(data f).val*factor f*m).sum=_
  rw [List.sum_ofFn,Finset.sum_mul]; rfl

theorem assemble_read (L : PackedShelf) (mem : Memory bits) (books : Fin S→Raw) (stream : ℕ→Group)
    (enough : V≤M) (mp : 0<M) (fit : V*width≤B) (src : Resident L mem books stream enough fit)
    (i : Fin S) (head : L.prefix.index.read mem (i.val:Word bits)=((population books i.val/M:ℕ):Word bits))
    (skip : (DescentTerminalDenseHeaderRAM.previous L.prefix.rem).eval mem (i.val:Word bits)=((population books i.val%M:ℕ):Word bits)) :
    (assemble L).eval mem (i.val:Word bits)=((clippedPage (siblings books enough mp stream i) fit).val:Word bits) := by
  let a:=population books i.val/M
  let lo:=stream a;let hi:=stream (a+1)
  let r:Fin M:=⟨population books i.val%M,Nat.mod_lt _ mp⟩
  have idx : L.prefix.index.read mem (i.val:Word bits)=(a:Word bits) := head
  have loRow (f:Fin 8) : (partExpr L false f).eval mem (i.val:Word bits)=(((lo f).val*factor f*G:ℕ):Word bits) := by
    have col : (L.columns f).read mem (a:Word bits)=((lo f).val:Word bits) := src.columns i 0 f
    change (L.low f).read mem ((L.columns f).read mem (L.prefix.index.read mem (i.val:Word bits)))=_
    rw [idx,col,src.low f (lo f)]
  have hiRow (f:Fin 8) : (partExpr L true f).eval mem (i.val:Word bits)=(((hi f).val*factor f*1:ℕ):Word bits) := by
    have col : (L.columns f).read mem ((a:Word bits)+1)=((hi f).val:Word bits) := by
      have colNat : (L.columns f).read mem ((a+1:ℕ):Word bits)=((hi f).val:Word bits) := src.columns i 1 f
      simpa only [Nat.cast_add,Nat.cast_one] using colNat
    change (L.high f).read mem ((L.columns f).read mem (L.prefix.index.read mem (i.val:Word bits)+1))=_
    simpa only [idx,col,Nat.mul_one] using src.high f (hi f)
  have lowSum := sum_read (partExpr L false) mem (i.val:Word bits)
    (fun f => (lo f).val*factor f*G) loRow (List.finRange 8)
  have highSum := sum_read (partExpr L true) mem (i.val:Word bits)
    (fun f => (hi f).val*factor f*1) hiRow (List.finRange 8)
  rw [sum_ordinal lo G] at lowSum
  rw [sum_ordinal hi 1,Nat.mul_one] at highSum
  have residue : L.residue.read mem ((DescentTerminalDenseHeaderRAM.previous L.prefix.rem).eval mem (i.val:Word bits))=
      ((r.val*(G*G):ℕ):Word bits) := by
    rw [skip]
    exact src.residue r
  have key : ((r.val*(G*G):ℕ):Word bits)+((((finPiFinEquiv lo).val*G:ℕ):Word bits)+((finPiFinEquiv hi).val:Word bits))=((pairCode (r,lo,hi)).val:Word bits) := by
    rw [paired_val,Nat.cast_add,Nat.cast_add,add_assoc]
  change L.table.read mem
    (L.residue.read mem ((DescentTerminalDenseHeaderRAM.previous L.prefix.rem).eval mem (i.val:Word bits))+
      ((sumExpr (partExpr L false) (List.finRange 8)).eval mem (i.val:Word bits)+
       (sumExpr (partExpr L true) (List.finRange 8)).eval mem (i.val:Word bits)))=_
  rw [residue,lowSum,highSum,key]
  simpa only [siblingROM,Equiv.symm_apply_apply,siblings,r,lo,hi,a] using
    src.dictionary (pairCode (r,lo,hi))

end
end Hierarchy.DescentTerminalVertexFields

end OAI
