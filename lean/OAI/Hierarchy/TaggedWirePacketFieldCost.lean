import OAI.Hierarchy.TaggedWirePacketSiteFields
import OAI.Hierarchy.TaggedWirePacketScanCost

namespace OAI
/-! # A bound on candidate field work independent of selector and acquired row values -/
namespace Hierarchy.WireTelescope.PacketTurns.Operands
open ProtocolRAM
variable {n t : ℕ} {len : Fin n→ℕ} (o : Operands len) (ord : Fin t≃Σi,Fin (len i))

structure Bound (B : ℕ) : Prop where
  old : ∀i b,(o.oldSite i b).work≤B
  width : ∀i,(o.width i).work≤B
  key : ∀i q,(o.edge i q).work≤B
  site : ∀i q b,(o.endSite i q b).work≤B

/-- One representative search per physical sector and one earlier-width scan
per source occurrence, with all true operand syntax charged. -/
def operandWork (t B : ℕ) := PacketScan.rankWork t B+4*PacketScan.firstWork t B+5*B+17
def fieldWork (t B : ℕ) := operandWork t B+8*B+8

variable {B : ℕ} (ok : o.Bound B)
include ok

theorem site_work (i : Fin n) (j : ℕ) : (o.site i j).work≤4*B+1 := by
  unfold site
  split
  · have a:=ok.old i false;omega
  split
  · have a:=ok.old i true;omega
  split
  next h=>
    have a:=ok.old i false;have b:=ok.site i ⟨0,h⟩ false;have c:=ok.site i ⟨0,h⟩ true
    simp only [Expr.work];omega
  · have a:=ok.old i false;omega

theorem sector_work (i : Fin n) (q : Fin (len i)) (b : Bool) :
    (o.sector ord i q b).work≤2*PacketScan.firstWork t B+5 := by
  have small (a : Expr) (hit : a∈List.ofFn (o.key ord)) : a.work≤B := by
    obtain ⟨u,rfl⟩:=List.mem_ofFn.mp hit
    exact ok.key _ _
  have bound:=PacketScan.first_work (o.edge i q) (List.ofFn (o.key ord)) B (ok.key i q) small
  simp only [List.length_ofFn] at bound
  simp only [sector,PacketScan.add,Expr.work]
  omega

theorem offset_work (i : Fin n) (q : Fin (len i)) :
    (o.offset ord i q).work≤PacketScan.rankWork t B := by
  have bound:=PacketScan.earlier_work (o.key ord) (fun j=>o.width (ord j).1) (o.edge i q) B
    (fun _=>ok.key _ _) (fun _=>ok.width _) (ok.key i q) (ord.symm ⟨i,q⟩).val
  exact bound.trans (Nat.add_le_add_left (Nat.mul_le_mul_right _ (ord.symm ⟨i,q⟩).isLt.le) _)

theorem linked_work (i : Fin n) (q : Fin (len i)) (j : ℕ) (start : Bool) :
    (o.linked ord i q (o.site i j) start).work≤operandWork t B := by
  have a:=site_work o ok i j
  have b:=sector_work o ord ok i q false
  have c:=sector_work o ord ok i q true
  have d:=offset_work o ord ok i q
  have f:=ok.site i q false
  cases start <;> simp only [linked,Bool.false_eq_true,ite_false,ite_true,Expr.work,operandWork] <;> omega

theorem side_work (i : Fin n) (j : ℕ) (right start : Bool) :
    (o.sideWord ord i j right start).work≤operandWork t B := by
  have law (q : Fin (len i)):=linked_work o ord ok i q j start
  have literal (v : ℕ) : (Expr.lit v).work≤operandWork t B := by
    simp only [Expr.work,operandWork]
    omega
  cases right
  · by_cases zero : j=0
    · simpa only [sideWord,Bool.false_eq_true,ite_false,ite_eq_left zero] using
        literal (if start then 0 else (ChosenPackets.RowRouting.halfCode i false).val)
    · by_cases h : j-1<len i
      · simpa only [sideWord,Bool.false_eq_true,ite_false,ite_eq_right zero,dite_eq_left h] using law ⟨j-1,h⟩
      · simpa only [sideWord,Bool.false_eq_true,ite_false,ite_eq_right zero,dite_eq_right h] using
          literal (if start then 0 else (ChosenPackets.RowRouting.halfCode i false).val)
  · by_cases h : j<len i
    · simpa only [sideWord,ite_true,dite_eq_left h] using law ⟨j,h⟩
    · simpa only [sideWord,ite_true,dite_eq_right h] using
        literal (if start then 0 else (ChosenPackets.RowRouting.halfCode i true).val)

theorem words_work (i : Fin n) (j : ℕ) (f : Fin 7) : (o.words ord i j f).work≤operandWork t B := by
  have side (a b : Bool):=side_work o ord ok i j a b
  have width:=ok.width i
  have localSite:=site_work o ok i j
  fin_cases f <;> simp only [words] <;> first
    | exact side false false
    | exact side true false
    | exact side false true
    | exact side true true
    | (simp [operandWork,Expr.work] <;> omega)

theorem field_work (party : Expr) (small : party.work≤B) (f : Fin ((n*3)*5)) :
    (o.field ord party f).work≤fieldWork t B := by
  let u : Fin (n*3)×Fin 5:=finProdFinEquiv.symm f
  let ij : Fin n×Fin 3:=finProdFinEquiv.symm u.1
  have rwid:=ok.width ij.1
  have sw:=site_work o ok ij.1 ij.2.val
  have fw:=words_work o ord ok ij.1 ij.2.val (u.2.castLE (by decide))
  dsimp only [field,column]
  split
  · change (o.width ij.1).work+1+1+((o.site ij.1 ij.2.val).work+party.work+
      (o.words ord ij.1 ij.2.val (u.2.castLE (by decide))).work+1+1)+1≤_
    unfold fieldWork;omega
  · simp [Expr.work,fieldWork]

end Hierarchy.WireTelescope.PacketTurns.Operands

end OAI
