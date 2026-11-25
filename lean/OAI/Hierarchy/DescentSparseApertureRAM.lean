import OAI.Hierarchy.DescentSparseDirectoryHeaders
import OAI.Hierarchy.DescentGLPermutationRAM

namespace OAI
/-! # A fixed local aperture over the measured source and its old neighbor ports -/

noncomputable section
namespace Hierarchy.DescentPacking.SparseBinRAM.Rect
open Sparse ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM DescentFirstColonyRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
variable {C : Type*} [Fintype C] [DecidableEq C] {H p R w : ℕ}

/-- Port zero is the source itself. The remaining old neighbor ports may be
empty or repeated. Every port has the same public dyadic code range. -/
def nearby (cell : C↪Fin H×Fin R) (ports : Fin (p+1)→Option (Fin H)) :=
  Finset.univ.filter fun c=>∃q,ports q=some (cell c).1

def rawName (cell : C↪Fin H×Fin R) (ports : Fin (p+1)→Option (Fin H)) :
    Fin ((p+1)*R+1)→Option C := Fin.cases (binOrder C).head? (fun i=>
  let q := finProdFinEquiv.symm i
  (ports q.1).bind (fun v=>occupant (cell.trans finProdFinEquiv.toEmbedding) (finProdFinEquiv (v,q.2))))

omit [DecidableEq C] in
private theorem tail_some (cell : C↪Fin H×Fin R) (ports : Fin (p+1)→Option (Fin H)) (c : C) :
    (∃i : Fin ((p+1)*R),rawName cell ports i.succ=some c) ↔ c∈nearby cell ports := by
  simp only [nearby,Finset.mem_filter,Finset.mem_univ,true_and]
  constructor
  · rintro ⟨i,h⟩
    let q := finProdFinEquiv.symm i
    change (ports q.1).bind _=some c at h
    obtain ⟨v,hv,ok⟩ := Option.bind_eq_some_iff.mp h
    have hit := (occupant_eq_some _ _ c).mp ok
    change finProdFinEquiv (cell c)=finProdFinEquiv (v,q.2) at hit
    have pos := congrArg Prod.fst (finProdFinEquiv.injective hit)
    exact ⟨q.1,by simpa [pos] using hv⟩
  · rintro ⟨q,hq⟩
    refine ⟨finProdFinEquiv (q,(cell c).2),?_⟩
    simp only [rawName,Fin.cases_succ,Equiv.symm_apply_apply,hq,Option.bind_some]
    apply (occupant_eq_some ..).2
    rfl

theorem covers (cell : C↪Fin H×Fin R) (ports : Fin (p+1)→Option (Fin H)) (c : C) :
    (∃i,rawName cell ports i=some c) ↔ c∈keep (nearby cell ports) := by
  have split : (∃i,rawName cell ports i=some c) ↔
      (binOrder C).head?=some c ∨ ∃i : Fin ((p+1)*R),rawName cell ports i.succ=some c := by
    constructor
    · rintro ⟨i,hi⟩
      cases i using Fin.cases with
      | zero=>exact Or.inl hi
      | succ i=>exact Or.inr ⟨_,hi⟩
    · rintro (head|⟨i,tail⟩)
      · exact ⟨0,head⟩
      · exact ⟨i.succ,tail⟩
  rw [split,tail_some]
  cases h : (binOrder C).head? <;> simp [keep,h,eq_comm]

def installed (cell : C↪Fin H×Fin R) (ports : Fin (p+1)→Option (Fin H)) :=
  aperture (nearby cell ports) (rawName cell ports) (covers cell ports)

omit [DecidableEq C] in
private theorem first_tag : tag (binOrder C).head?=0 := by
  by_cases h : 0<Fintype.card C
  · have eqn : (binOrder C).head?=some ((Fintype.equivFin C).symm ⟨0,h⟩) := by
      rw [List.head?_eq_getElem?,List.getElem?_eq_getElem (by simp [binOrder,h])]
      simp [binOrder]
    simp [tag,eqn,code]
  · have z : Fintype.card C=0 := by omega
    have nil_ : binOrder C=[] := List.length_eq_zero_iff.mp (by simp [binOrder,z])
    simp [nil_,z,tag]

def portWord (ports : Fin (p+1)→Option (Fin H)) (i : Fin (p+1)) := ((ports i).map Fin.val).getD H

def row (H R missing : ℕ) (L : Chart) (source : Expr) (d : ℕ) : Expr :=
  .branch .lt source (.lit H)
    (header L (.op .add (scale R source) (.lit d)) missing) (.lit missing)

def fields (H p R missing : ℕ) (L : Chart) (src : Fin (p+1)→Expr) : Fin ((p+1)*R+1)→Expr :=
  Fin.cases (.lit 0) (fun i=>let q := finProdFinEquiv.symm i;row H R missing L (src q.1) q.2.val)

def expr (H p R missing : ℕ) (L : Chart) (src : Fin (p+1)→Expr) :=
  chooseField ((p+1)*R+1) 0 (fields H p R missing L src) .row

omit [DecidableEq C] in
theorem cell_card (cell : C↪Fin H×Fin R) : Fintype.card C≤H*R := by
  simpa using Fintype.card_le_of_injective cell cell.injective

omit [DecidableEq C] in
private theorem row_read (missing : ℕ) (cell : C↪Fin H×Fin R) (L : Chart)
    (source : Expr) (m : Memory w) (r : Word w) (port : Option (Fin H)) (d : Fin R)
    (headers : Headers L (cell.trans finProdFinEquiv.toEmbedding) m)
    (seen : source.eval m r = (((port.map Fin.val).getD H : ℕ) : Word w))
    (hr : H < 2^w) (size : H*R≤L.heads.size) (headFit : L.heads.size<2^w) :
    (row H R missing L source d.val).eval m r =
      (wideTag missing (port.bind (fun v => occupant (cell.trans finProdFinEquiv.toEmbedding)
        (finProdFinEquiv (v,d)))) : Word w) := by
  cases port with
  | none =>
    change source.eval m r = (H : Word w) at seen
    simp [row,Expr.eval,Comparison.test,seen,wideTag]
  | some v =>
    change source.eval m r = (v.val : Word w) at seen
    have addr : (Expr.op .add (scale R source) (.lit d.val)).eval m r =
        ((finProdFinEquiv (v,d)).val : Word w) := by
      simp [Expr.eval,scale_eval,RowOp.opcode,BinaryOp.eval,seen,finProdFinEquiv]
      ring
    have ok : (v.val : Word w) < (H : Word w) := by
      change (v.val : Word w).val < (H : Word w).val
      rw [Fin.val_cast_of_lt (v.isLt.trans hr),Fin.val_cast_of_lt hr]
      exact v.isLt
    change (if Comparison.lt.test (source.eval m r) (H : Word w) then _ else _) = _
    simp only [seen,show Comparison.lt.test (v.val : Word w) (H : Word w) = true from decide_eq_true ok,
      ite_true]
    exact header_code_missing missing L _ m headers _ r (finProdFinEquiv (v,d)) addr size headFit

omit [DecidableEq C] in
theorem eval_missing [Nonempty C] (missing : ℕ) (cell : C↪Fin H×Fin R) (ports : Fin (p+1)→Option (Fin H)) (L : Chart)
    (src : Fin (p+1)→Expr) (m : Memory w) (i : Fin ((p+1)*R+1))
    (headers : Headers L (cell.trans finProdFinEquiv.toEmbedding) m)
    (seen : ∀q,(src q).eval m (i.val:Word w)=(portWord ports q:Word w))
    (hr : H<2^w) (room : (p+1)*R+1≤2^w) (size : H*R≤L.heads.size) (headFit : L.heads.size<2^w) :
    (expr H p R missing L src).eval m (i.val:Word w)=(wideTag missing (rawName cell ports i):Word w) := by
  rw [expr,eval_chooseField _ _ _ _ _ _ i (by omega) (by simp [Expr.eval,Fin.val_cast_of_lt (i.isLt.trans_le room)])]
  cases i using Fin.cases with
  | zero =>
    change (0:Word w)=(wideTag missing (binOrder C).head?:Word w)
    have h := Fintype.card_pos (α:=C)
    have head : (binOrder C).head?=some ((Fintype.equivFin C).symm ⟨0,h⟩) := by
      rw [List.head?_eq_getElem?,List.getElem?_eq_getElem (by simp [binOrder,h])]
      simp [binOrder]
    simp [head,wideTag,code]
  | succ i =>
    let q : Fin (p+1)×Fin R := finProdFinEquiv.symm i
    change (row H R _ L (src q.1) q.2.val).eval _ _=(wideTag missing ((ports q.1).bind _):Word w)
    exact row_read missing cell L (src q.1) m (i.succ.val : Word w) (ports q.1) q.2
      headers (seen q.1) hr size headFit

omit [DecidableEq C] in
theorem eval (cell : C↪Fin H×Fin R) (ports : Fin (p+1)→Option (Fin H)) (L : Chart)
    (src : Fin (p+1)→Expr) (m : Memory w) (i : Fin ((p+1)*R+1))
    (headers : Headers L (cell.trans finProdFinEquiv.toEmbedding) m)
    (seen : ∀q,(src q).eval m (i.val:Word w)=(portWord ports q:Word w))
    (hr : H<2^w) (room : (p+1)*R+1≤2^w) (size : H*R≤L.heads.size) (headFit : L.heads.size<2^w) :
    (expr H p R (Fintype.card C) L src).eval m (i.val:Word w)=(tag (rawName cell ports i):Word w) := by
  rw [expr,eval_chooseField _ _ _ _ _ _ i (by omega) (by simp [Expr.eval,Fin.val_cast_of_lt (i.isLt.trans_le room)])]
  cases i using Fin.cases with
  | zero =>
    change (0:Word w)=(tag (binOrder C).head?:Word w)
    rw [first_tag];rfl
  | succ i =>
    let q : Fin (p+1)×Fin R := finProdFinEquiv.symm i
    change (row H R _ L (src q.1) q.2.val).eval _ _=(tag ((ports q.1).bind _):Word w)
    exact row_read (Fintype.card C) cell L (src q.1) m (i.succ.val : Word w) (ports q.1) q.2
      headers (seen q.1) hr size headFit

theorem fits (H p R missing out : ℕ) (L : Chart) (src : Fin (p+1)→Expr)
    (heads : L.heads.Fits w out) (starts : L.starts.Fits w out) (f : ∀q,(src q).Fits w out) :
    (expr H p R missing L src).Fits w out := by
  apply DescentGLPermutationRAM.fits_choose ((p+1)*R+1) 0 .row (fields H p R missing L src) (w := w) (out := out) trivial
  intro i
  cases i using Fin.cases with
  | zero => trivial
  | succ i =>
    let q : Fin (p+1)×Fin R := finProdFinEquiv.symm i
    exact ⟨f q.1,trivial,header_fits L _ _ _ heads starts ⟨scale_fits _ _ (f q.1),trivial⟩,trivial⟩

theorem expr_work (H p R missing : ℕ) (L : Chart) (src : Fin (p+1)→Expr) (U : ℕ)
    (bound : ∀q,(src q).work≤U) : (expr H p R missing L src).work≤
      1+((p+1)*R+1)*(U+2*R*(U+1)+35) := by
  have choose (a off B : ℕ) (f : Fin a→Expr) (h : ∀i,(f i).work≤B) :
      (chooseField a off f .row).work≤1+a*(B+4) := by
    induction a generalizing off with
    | zero => simp [chooseField, Expr.work]
    | succ a ih =>
      have tail := ih (off+1) (fun i=>f i.succ) (fun i=>h i.succ)
      have front := h 0
      simp only [chooseField,Expr.work,Nat.succ_mul]
      omega
  apply (choose _ 0 (U+2*R*(U+1)+31) (fields H p R missing L src) ?_).trans
  · rfl
  · intro i
    cases i using Fin.cases with
    | zero => change 1≤_;omega
    | succ i =>
      let q : Fin (p+1)×Fin R := finProdFinEquiv.symm i
      change (row H R missing L (src q.1) q.2.val).work≤_
      have h := bound q.1
      have mul := Nat.mul_le_mul_left (2*R) (Nat.add_le_add_right h 1)
      simp [row,Expr.work,header_work,scale_work]
      nlinarith only [h,mul]

end Hierarchy.DescentPacking.SparseBinRAM.Rect

end
end OAI
