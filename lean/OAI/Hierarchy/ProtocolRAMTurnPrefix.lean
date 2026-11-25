import OAI.Hierarchy.ProtocolRAMTurnRankProgram
import OAI.Hierarchy.ProtocolRAMPackedCommon
import OAI.Hierarchy.TaggedWireNativeOrder

namespace OAI
/-! # Chronological per-edge bit offsets of the installed and terminal route occurrences -/

noncomputable section
namespace Hierarchy.ProtocolRAMTurnPrefix
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM ProtocolRAM.RouteSettlement AdaptiveProbe WireTelescope
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped BigOperators Fin.CommRing Classical
variable {W K edges r n bins : ℕ} {I C : Type} [Fintype I] [Fintype C]

theorem term_work (b : Banks) (edges : ℕ) : (keyTerm b edges).work=20 ∧ (widthTerm b edges).work=129 := by
  constructor <;> rfl

omit [Fintype I] [Fintype C] in
private theorem tail (b : Banks) (m : Memory W) {core : I→List (Fin edges)} {center : C→List (Fin edges)}
    (enum : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : C→ℕ) (dir : Directory b m enum ci cj)
    (wide : 2<2^W) (funded : ∀j,actual b.used m (cj j)≤ actual b.reserved m (cj j)) (i : Fin r) :
    (RouteSettlement.words b).eval m ((2*i.val+1:ℕ):Word W)=(RouteSettlement.weight b m enum ci cj i:Word W) := by
  have one : (1:Word W)≠0 := by intro eq;have := congrArg Fin.val eq;simp [Nat.mod_eq_of_lt (show 1<2^W by omega)] at this
  have two : (2:Word W)≠0 := by intro eq;have := congrArg Fin.val eq;simp [Nat.mod_eq_of_lt wide] at this
  have apart : (2:Word W)≠1 := by intro eq;have := congrArg Fin.val eq;simp [Nat.mod_eq_of_lt wide,Nat.mod_eq_of_lt (show 1<2^W by omega)] at this
  have stock (row j : Word W) (kind : b.kind.read m row=1) (index : b.index.read m row=j) :
      (RouteSettlement.words b).eval m row=b.stock.read m j := by
    simp [RouteSettlement.words,Expr.eval,Comparison.test,kind,index,one]
  have returned (row j : Word W) (kind : b.kind.read m row=2) (index : b.index.read m row=j) :
      (RouteSettlement.words b).eval m row=b.reserved.read m j-b.used.read m j := by
    simp [RouteSettlement.words,Expr.eval,Comparison.test,kind,index,two,apart,RowOp.opcode,BinaryOp.eval]
  have kind:=dir.tailKind i
  have index:=dir.tailIndex i
  cases h : enum i with
  | inl x =>
    rcases x with ⟨j,q⟩
    rw [h] at kind index
    rw [stock _ (ci j:Word W) kind index]
    simp [RouteSettlement.weight,h,RouteOccurrence.weight,actual]
  | inr x =>
    rcases x with ⟨j,q⟩
    rw [h] at kind index
    rw [returned _ (cj j:Word W) kind index]
    simp only [RouteSettlement.weight,h,RouteOccurrence.weight]
    rw [Nat.cast_sub (funded j)]
    simp only [actual,Fin.cast_val_eq_self]

omit [Fintype I] [Fintype C] in
theorem term_read (B : SettledMatrix.Layout K edges I C) (enum : Fin r≃RouteOccurrence B.core B.center)
    (b : Banks) (m : Memory W) (ci : I→ℕ) (cj : C→ℕ) (dir : Directory b m enum ci cj)
    (num : edges+r<2^W) (wide : 2<2^W) (funded : ∀j,actual b.used m (cj j)≤ actual b.reserved m (cj j)) (i : Fin (edges+r)) :
    let width:=B.nativeWidth enum (fun e=> actual b.width m e.val) (fun i=> actual b.stock m (ci i))
      (fun j=> actual b.reserved m (cj j)) (fun j=> actual b.used m (cj j))
    (keyTerm b edges).eval m (i.val:Word W)=((B.nativeEdge enum i).val:Word W) ∧
      (widthTerm b edges).eval m (i.val:Word W)=(width i:Word W) := by
  intro width
  have eFit : edges<2^W:=by omega
  obtain ⟨(e|j),rfl⟩:=finSumFinEquiv.surjective i
  · have below := e.isLt.trans eFit
    have cond : Comparison.lt.test (e.val:Word W) (edges:Word W)=true := by
      simp [Comparison.test,Fin.lt_def,Fin.val_cast_of_lt below,Fin.val_cast_of_lt eFit,e.isLt]
    have e1 : B.nativeEdge enum (finSumFinEquiv (.inl e))=e := by simp [SettledMatrix.Layout.nativeEdge]
    have e2 : width (finSumFinEquiv (.inl e))=actual b.width m e.val := by simp [width,SettledMatrix.Layout.nativeWidth]
    rw [e1,e2];change _ ∧ _
    simp only [keyTerm,widthTerm,Expr.eval,finSumFinEquiv_apply_left,Fin.val_castAdd,cond,ite_true,actual,Fin.cast_val_eq_self]; trivial
  · have live := j.isLt
    have small : edges+j.val<2^W:=by omega
    have cond : Comparison.lt.test ((edges+j.val:ℕ):Word W) (edges:Word W)=false := by
      simp only [Comparison.test,Fin.lt_def,Fin.val_cast_of_lt small,Fin.val_cast_of_lt eFit,decide_eq_false_iff_not,not_lt]
      omega
    have off : (relative edges).eval m ((edges+j.val:ℕ):Word W)=(j.val:Word W) := by
      change ((edges+j.val:ℕ):Word W)-(edges:Word W)=_;rw [Nat.cast_add];abel
    have ev : (evenTerm edges).eval m ((edges+j.val:ℕ):Word W)=((2*j.val:ℕ):Word W) := by
      change (relative edges).eval m _+(relative edges).eval m _=_
      rw [off,two_mul,Nat.cast_add]
    have key : B.nativeEdge enum (finSumFinEquiv (.inr j))=(enum j).edge := by simp [SettledMatrix.Layout.nativeEdge]
    have amt : width (finSumFinEquiv (.inr j))=RouteSettlement.weight b m enum ci cj j := by simp [width,SettledMatrix.Layout.nativeWidth,RouteSettlement.weight]
    rw [key,amt]
    change (keyTerm b edges).eval m ((edges+j.val:ℕ):Word W)=_ ∧ (widthTerm b edges).eval m ((edges+j.val:ℕ):Word W)=_
    have after : (Expr.op .add (evenTerm edges) (.lit 1)).eval m ((edges+j.val:ℕ):Word W)=((2*j.val+1:ℕ):Word W) := by
      change (evenTerm edges).eval m _+1=_;rw [ev,Nat.cast_add,Nat.cast_one]
    constructor
    · change (if Comparison.lt.test ((edges+j.val:ℕ):Word W) (edges:Word W) then _ else b.index.read m ((evenTerm edges).eval m _))=_
      simp only [cond,Bool.false_eq_true,ite_false,ev,dir.headIndex]
    · change (if Comparison.lt.test ((edges+j.val:ℕ):Word W) (edges:Word W) then _ else ((RouteSettlement.words b).atRow _).eval m _)=_
      simp only [cond,Bool.false_eq_true,ite_false,eval_atRow,after,tail b m enum ci cj dir wide funded]

def fixedBank (b : Banks) (m : Memory W) : Fin edges→ℕ := fun e=> actual b.width m e.val

omit [Fintype I] [Fintype C] in
theorem run_counts (B : SettledMatrix.Layout K edges I C) (enum : Fin r≃RouteOccurrence B.core B.center)
    (b : Banks) (m : Memory W) (ci : I→ℕ) (cj : C→ℕ) (dir : Directory b m enum ci cj)
    (lo src keys counters dst : ℕ) (weightBank keyBank : Bank)
    (Ksafe : (keyTerm b edges).Fits W keyBank.base) (Vsafe : (widthTerm b edges).Fits W keyBank.base)
    (separate : keyBank.base+(edges+r)≤ weightBank.base)
    (fits : ProtocolRAMRankGather.Fits (ProtocolRAMPackedCommon.inputBanks weightBank keyBank) W (edges+r) lo src keys)
    (afterKeys : keys+4*(edges+r)≤ counters) (afterCount : counters+edges≤ dst) (stop : dst+4*(edges+r)<2^W)
    (wide : 2<2^W) (funded : ∀j,actual b.used m (cj j)≤ actual b.reserved m (cj j)) :
    let widths:=B.nativeWidth enum (fixedBank b m) (fun i=> actual b.stock m (ci i))
      (fun j=> actual b.reserved m (cj j)) (fun j=> actual b.used m (cj j))
    ∃ out,(program W edges r lo src keys counters dst b weightBank keyBank).Exec m out (clock edges r src keys b weightBank keyBank) ∧
      (∀i : Fin (edges+r),out (dst+4*i.val+3)=(TaggedShorterCommonScan.earlier (B.nativeEdge enum) widths i.val (B.nativeEdge enum i):Word W)) ∧
      (∀ x< keyBank.base,out x=m x) ∧
      (∀i : Fin (edges+r),out (keyBank.base+i.val)=((B.nativeEdge enum i).val:Word W)) ∧
      (∀i : Fin (edges+r),out (weightBank.base+i.val)=(widths i:Word W)) ∧
      ∀e : Fin edges,out (counters+e.val)=((∑i : Fin (edges+r), if B.nativeEdge enum i=e then widths i else 0 : ℕ):Word W) := by
  intro widths
  let n:=edges+r
  let mid:=image keyBank.base n (keyTerm b edges) m
  let ready:=image weightBank.base n (widthTerm b edges) mid
  have wbase : weightBank.base+n≤ lo := (Nat.add_le_add_left fits.weight_count weightBank.base).trans fits.weights_fit.2.2
  have below : keyBank.base≤ weightBank.base:=by omega
  have endK : keyBank.base+n<2^W := by have u:=fits.start;have v:=fits.sep;have q:=fits.room;omega
  have endW : weightBank.base+n<2^W := by have u:=fits.start;have v:=fits.sep;have q:=fits.room;omega
  have total : edges+r<2^W := by omega
  have earlier (x) (hx : x< keyBank.base) : mid x=m x:=ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl hx)
  have prior (x) (hx : x< weightBank.base) : ready x=mid x:=ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl hx)
  have terms:=term_read B enum b m ci cj dir total wide funded
  have kLoad (i : Fin n) : ready (keyBank.base+i.val)=((B.nativeEdge enum i).val:Word W) := by
    rw [prior _ (by have bound:=i.isLt;omega)]
    exact (ProtocolRAMGeneratedWrite.read_image keyBank.base n (keyTerm b edges) m i).trans (terms i).1
  have wLoad (i : Fin n) : ready (weightBank.base+i.val)=(widths i:Word W) :=
    (ProtocolRAMGeneratedWrite.read_image _ _ _ mid i).trans ((eval_below _ _ m mid Vsafe earlier).trans (terms i).2)
  obtain ⟨out,rankRun,packed,frame,counts⟩:=ProtocolRAMPackedCommon.run_counts lo src keys counters dst weightBank keyBank
    (B.nativeEdge enum) widths ready fits afterKeys afterCount stop wLoad kLoad
  have kRun : (scan W keyBank.base n (keyTerm b edges)).Exec m mid (4+n*(2*(keyTerm b edges).work+4)) :=
    scan_exec _ _ _ _ Ksafe endK
  have wRun : (scan W weightBank.base n (widthTerm b edges)).Exec mid ready (4+n*(2*(widthTerm b edges).work+4)) :=
    scan_exec _ _ _ _ (ProtocolRAMGeneratedWrite.fits_mono _ below Vsafe) endW
  have columns : ((scan W keyBank.base n (keyTerm b edges)).seq (scan W weightBank.base n (widthTerm b edges))).Exec m ready
      ((4+n*(2*(keyTerm b edges).work+4))+(4+n*(2*(widthTerm b edges).work+4))) := by
    intro P R L machine
    exact Procedure.Exec.then kRun wRun machine
  refine ⟨out,Procedure.Exec.then columns rankRun,packed,fun x hx=>(frame x (by omega)).trans ((prior x (hx.trans_le below)).trans (earlier x hx)),?_,?_,counts⟩
  · intro i
    have h:=i.isLt
    exact (frame _ (by omega)).trans (kLoad i)
  · intro i
    have h:=i.isLt
    exact (frame _ (by omega)).trans (wLoad i)


omit [Fintype I] [Fintype C] in
theorem run (B : SettledMatrix.Layout K edges I C) (enum : Fin r≃RouteOccurrence B.core B.center)
    (b : Banks) (m : Memory W) (ci : I→ℕ) (cj : C→ℕ) (dir : Directory b m enum ci cj)
    (lo src keys counters dst : ℕ) (weightBank keyBank : Bank)
    (Ksafe : (keyTerm b edges).Fits W keyBank.base) (Vsafe : (widthTerm b edges).Fits W keyBank.base)
    (separate : keyBank.base+(edges+r)≤ weightBank.base)
    (fits : ProtocolRAMRankGather.Fits (ProtocolRAMPackedCommon.inputBanks weightBank keyBank) W (edges+r) lo src keys)
    (afterKeys : keys+4*(edges+r)≤ counters) (afterCount : counters+edges≤ dst) (stop : dst+4*(edges+r)<2^W)
    (wide : 2<2^W) (funded : ∀j,actual b.used m (cj j)≤ actual b.reserved m (cj j)) :
    let widths:=B.nativeWidth enum (fixedBank b m) (fun i=> actual b.stock m (ci i))
      (fun j=> actual b.reserved m (cj j)) (fun j=> actual b.used m (cj j))
    ∃ out,(program W edges r lo src keys counters dst b weightBank keyBank).Exec m out (clock edges r src keys b weightBank keyBank) ∧
      (∀i : Fin (edges+r),out (dst+4*i.val+3)=(TaggedShorterCommonScan.earlier (B.nativeEdge enum) widths i.val (B.nativeEdge enum i):Word W)) ∧
      (∀ x< keyBank.base,out x=m x) ∧
      (∀i : Fin (edges+r),out (keyBank.base+i.val)=((B.nativeEdge enum i).val:Word W)) ∧
      ∀i : Fin (edges+r),out (weightBank.base+i.val)=(widths i:Word W) := by
  obtain ⟨out,exec,rank,frame,keysRead,weights,_⟩ := run_counts B enum b m ci cj dir lo src keys counters dst
    weightBank keyBank Ksafe Vsafe separate fits afterKeys afterCount stop wide funded
  exact ⟨out,exec,rank,frame,keysRead,weights⟩

theorem natural_offset (key : Fin n→Fin bins) (width : Fin n→ℕ) (out : Memory W) (dst : ℕ)
    (i : Fin n) (read : out (dst+4*i.val+3)=(TaggedShorterCommonScan.earlier key width i.val (key i):Word W))
    (fit : TaggedShorterCommonScan.earlier key width i.val (key i)<2^W) :
    (out (dst+4*i.val+3)).val=TaggedShorterCommonScan.earlier key width i.val (key i) := by
  rw [read,Fin.val_cast_of_lt fit]

end Hierarchy.ProtocolRAMTurnPrefix
end

end OAI
