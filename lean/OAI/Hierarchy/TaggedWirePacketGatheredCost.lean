import OAI.Hierarchy.TaggedWirePacketGatheredOpcode
import OAI.Hierarchy.TaggedWirePacketFieldCost

namespace OAI
/-! # Work of real finite alias-prefix, degree lookup, and shifted header emission -/
namespace Hierarchy.WireTelescope.PacketTurns.Operands
open ProtocolRAM
variable {n t D : ℕ} {len : Fin n→ℕ} (o : Operands len) (ord : Fin t≃Σi,Fin (len i))
    (width nbr : Fin D→Expr) {B : ℕ} (ok : o.Bound B)
    (shelf : ∀q,(width q).work≤B) (neighbors : ∀q,(nbr q).work≤B)

def gatheredWork (t D B : ℕ) := PacketScan.rankWork t (7*B+7)+PacketScan.rankWork t B+
  2*PacketScan.firstWork D (3*B+7)+6*B+10

def gatheredFieldWork (t D B : ℕ) := gatheredWork t D B+8*B+8

include shelf neighbors in
theorem gathered_sector_work (x : Expr) (small : x.work≤B) :
    (neighborSector n width nbr x).work≤PacketScan.firstWork D (3*B+7)+2 := by
  let xs:=List.ofFn (fun q=>PacketNeighbor.compare (width q) (nbr q) x)
  have bound (z : Expr) (atZ : z∈xs) : z.work≤3*B+7 := by
    obtain ⟨q,rfl⟩:=List.mem_ofFn.mp atZ
    have w:=shelf q;have k:=neighbors q
    simp only [PacketNeighbor.compare,Expr.work];omega
  have scan:=PacketScan.first_work (.lit 1) xs (3*B+7) (by simp [Expr.work]) bound
  simp only [xs,List.length_ofFn] at scan
  simp only [neighborSector,PacketNeighbor.selectExpr,PacketScan.add,Expr.work]
  omega

include ok

theorem prior_work (i : Fin n) (j : Fin (len i)) (u : Fin t) : (o.priorAmount ord i j u).work≤7*B+7 := by
  have k:=ok.key i j;have k':=ok.key (ord u).1 (ord u).2
  have a:=ok.site i j false;have a':=ok.site (ord u).1 (ord u).2 false
  have b:=ok.site i j true;have b':=ok.site (ord u).1 (ord u).2 true
  have w:=ok.width (ord u).1
  simp only [priorAmount,Expr.work];omega

theorem aggregate_work (i : Fin n) (j : Fin (len i)) :
    (o.aggregateStart ord i j).work≤PacketScan.rankWork t (7*B+7) :=
  PacketScan.earlier_work _ _ _ _ (fun _=>by simp [Expr.work]) (prior_work o ord ok i j) (by simp [Expr.work]) _

theorem low_work (x y : Expr) (l : x.work≤B) (h : y.work≤B) :
    (o.aggregateWidth ord x y).work≤PacketScan.rankWork t (5*B+5) := by
  apply PacketScan.earlier_work _ _ _ _ (fun _=>by simp [Expr.work]) _ (by simp [Expr.work]) _
  intro u;have a:=ok.site (ord u).1 (ord u).2 false;have b:=ok.site (ord u).1 (ord u).2 true
  have w:=ok.width (ord u).1
  simp only [matchingAmount,Expr.work];omega

include shelf neighbors

theorem gathered_link_work (i : Fin n) (q : Fin (len i)) (j : ℕ) (start : Bool) :
    (o.gatheredLink ord width nbr i q (o.site i j) start).work≤gatheredWork t D B := by
  have a:=site_work o ok i j
  have b:=gathered_sector_work (n:=n) width nbr shelf neighbors (o.endSite i q false) (ok.site i q false)
  have c:=gathered_sector_work (n:=n) width nbr shelf neighbors (o.endSite i q true) (ok.site i q true)
  have d:=offset_work o ord ok i q
  have f:=ok.site i q false
  have g:=aggregate_work o ord ok i q
  cases start <;> simp only [gatheredLink,Bool.false_eq_true,ite_false,ite_true,PacketScan.add,Expr.work,gatheredWork] <;> omega

theorem gathered_side_work (i : Fin n) (j : ℕ) (right start : Bool) :
    (o.gatheredSide ord width nbr i j right start).work≤gatheredWork t D B := by
  have law (q : Fin (len i)):=gathered_link_work o ord width nbr ok shelf neighbors i q j start
  have literal (v : ℕ) : (Expr.lit v).work≤gatheredWork t D B := by
    simp only [Expr.work,gatheredWork]
    omega
  cases right
  · by_cases zero : j=0
    · simpa only [gatheredSide,Bool.false_eq_true,ite_false,ite_eq_left zero] using
        literal (if start then 0 else (ChosenPackets.RowRouting.halfCode i false).val)
    · by_cases h : j-1<len i
      · simpa only [gatheredSide,Bool.false_eq_true,ite_false,ite_eq_right zero,dite_eq_left h] using law ⟨j-1,h⟩
      · simpa only [gatheredSide,Bool.false_eq_true,ite_false,ite_eq_right zero,dite_eq_right h] using
          literal (if start then 0 else (ChosenPackets.RowRouting.halfCode i false).val)
  · by_cases h : j<len i
    · simpa only [gatheredSide,ite_true,dite_eq_left h] using law ⟨j,h⟩
    · simpa only [gatheredSide,ite_true,dite_eq_right h] using
        literal (if start then 0 else (ChosenPackets.RowRouting.halfCode i true).val)

theorem gathered_words_work (i : Fin n) (j : ℕ) (f : Fin 7) : (o.gatheredWords ord width nbr i j f).work≤gatheredWork t D B := by
  have side (a b : Bool):=gathered_side_work o ord width nbr ok shelf neighbors i j a b
  have width:=ok.width i
  have localSite:=site_work o ok i j
  fin_cases f <;> simp only [gatheredWords] <;> first
    | exact side false false
    | exact side true false
    | exact side false true
    | exact side true true
    | (simp [gatheredWork,Expr.work] <;> omega)

theorem gathered_field_work (party : Expr) (small : party.work≤B) (f : Fin ((n*3)*5)) :
    (o.column (o.gatheredWords ord width nbr) party f).work≤gatheredFieldWork t D B := by
  let u : Fin (n*3)×Fin 5:=finProdFinEquiv.symm f
  let ij : Fin n×Fin 3:=finProdFinEquiv.symm u.1
  have rwid:=ok.width ij.1
  have sw:=site_work o ok ij.1 ij.2.val
  have fw:=gathered_words_work o ord width nbr ok shelf neighbors ij.1 ij.2.val (u.2.castLE (by decide))
  dsimp only [column]
  split
  · change (o.width ij.1).work+1+1+((o.site ij.1 ij.2.val).work+party.work+
      (o.gatheredWords ord width nbr ij.1 ij.2.val (u.2.castLE (by decide))).work+1+1)+1≤_
    unfold gatheredFieldWork;omega
  · simp [Expr.work,gatheredFieldWork]

end Hierarchy.WireTelescope.PacketTurns.Operands

end OAI
