import OAI.Hierarchy.DescentResetOriginalSlots
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # Old host and local shape of each compact numbered reset actor -/
namespace Hierarchy.DescentResetCompactGeometry
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H Q P N w : ℕ}
def words (P : ℕ):=2*DescentResetOriginalSlots.stride P
def value (Q : ℕ) (s : Fin 2) (raw : ℕ):=if s=0 then raw%Q else raw/Q
def literal (P Q : ℕ) (i : ℕ):=let n:=DescentResetOriginalSlots.stride P
  if i<n then i%Q else (i-n)/Q
def tab (base P : ℕ) (s : Fin 2) : Bank:=⟨base+s.val*DescentResetOriginalSlots.stride P,Nat.clog 2 P⟩
def expr (here total : Bank) (base P : ℕ) (s : Fin 2) : Expr:=
  .branch .lt .row (.lookup total (.lit 0)) (.lookup (tab base P s) (.lookup here .row)) (.lit 0)
def cols (here total : Bank) (base P : ℕ) (p : Fin (1*2)):=expr here total base P (finProdFinEquiv.symm p).2
def scans (here total : Bank) (base P out H : ℕ):=DescentResetOriginalSlots.passes (X:=1)
  (Function.Embedding.refl (Fin 2)) out H (cols here total base P)
def phase (here total : Bank) (base P Q out H w : ℕ):=
  (DescentStaticWordColumn.program w base (literal P Q) (words P)).seq (program w (scans here total base P out H))
def after (here total : Bank) (base P Q out H : ℕ) (m : Memory w):=
  result (scans here total base P out H) (DescentStaticWordColumn.image base (literal P Q) m (words P))
def ticks (here total : Bank) (base P out H : ℕ):=4+10*(words P)+clock (scans here total base P out H)
def output (out H : ℕ) (s : Fin 2):=DescentResetOriginalSlots.bank out H 2 0 s.val
def stop (out H : ℕ):=DescentResetOriginalSlots.finish out H 1 2

theorem tab_range (base P : ℕ) (s : Fin 2) : (tab base P s).base+(tab base P s).size≤base+words P:=by
  have bound:=Nat.mul_le_mul_right (DescentResetOriginalSlots.stride P) s.isLt
  rw [Nat.succ_mul] at bound
  change base+s.val*DescentResetOriginalSlots.stride P+DescentResetOriginalSlots.stride P≤base+2*DescentResetOriginalSlots.stride P
  omega

theorem fit (here total : Bank) (base P out : ℕ) (s : Fin 2) (input : here.Fits w base) (cnt : total.Fits w base)
    (early : base+words P≤out) (room : out<2^w) : (expr here total base P s).Fits w out:=by
  have span:=(tab_range base P s).trans early
  have fit : (tab base P s).Fits w out:=⟨Nat.two_pow_pos _,(Nat.le_add_left _ _).trans_lt (span.trans_lt room),span⟩
  have lo : base≤out:=(Nat.le_add_right ..).trans early
  exact ⟨trivial,⟨⟨cnt.1,cnt.2.1,cnt.2.2.trans lo⟩,trivial⟩,
    ⟨fit,ProtocolRAMGeneratedWrite.fits_mono (.lookup here .row) lo ⟨input,trivial⟩⟩,trivial⟩

theorem any (here total : Bank) (base P Q out H : ℕ) (m : Memory w)
    (input : here.Fits w base) (cnt : total.Fits w base) (early : base+words P≤out) (room : stop out H<2^w) :
    (phase here total base P Q out H w).Exec m (after here total base P Q out H m) (ticks here total base P out H) ∧
      CheapCode (phase here total base P Q out H w) ∧ ∀a,a<base ∨ stop out H≤a→after here total base P Q out H m a=m a:=by
  have cap : out<2^w:=(Nat.le_add_right ..).trans_lt room
  let mid := DescentStaticWordColumn.image base (literal P Q) m (words P)
  let ps := scans here total base P out H
  have mounted : (DescentStaticWordColumn.program w base (literal P Q) (words P)).Exec m mid (4+10*words P) :=
    @DescentStaticWordColumn.mount w base (words P) (literal P Q) m (early.trans_lt cap)
  have safe : ∀ pass ∈ ps, pass.Fits w :=
    DescentResetOriginalSlots.safe (X:=1) (Function.Embedding.refl (Fin 2)) out H (cols here total base P)
      (fun p => fit here total base P out (finProdFinEquiv.symm p).2 input cnt early cap) room
  have scanned : (program w ps).Exec mid (result ps mid) (clock ps) :=
    @ProtocolRAM.program_exec w ps mid safe
  refine ⟨@Procedure.Exec.then w _ _ m mid (result ps mid) (4+10*words P) (clock ps) (@mounted) (@scanned),
    @ProtocolRAM.cheap_seq w _ _ (@DescentStaticWordColumn.cheap w base (literal P Q) (words P))
      (@ProtocolRAM.program_cheap w ps), ?_⟩
  intro a away
  have first : after here total base P Q out H m a=DescentStaticWordColumn.image base (literal P Q) m (words P) a:=by
    apply DescentResetOriginalSlots.frame
    intro p
    let shelf := Function.Embedding.refl (Fin 2)
    let pass : Pass := ⟨out+(DescentResetOriginalSlots.cell (X:=1) shelf p).val*DescentResetOriginalSlots.stride H,
      H,cols here total base P p⟩
    have member : pass ∈ DescentResetOriginalSlots.passes (X:=1) shelf out H (cols here total base P) :=
      List.mem_map.mpr ⟨p,List.mem_finRange _,rfl⟩
    have h := DescentResetOriginalSlots.earlier (X:=1) shelf out H (cols here total base P) pass member
    rcases away with lo|hi
    · exact .inl (lo.trans_le (((Nat.le_add_right ..).trans early).trans h.1))
    · exact .inr (h.2.trans hi)
  exact first.trans (DescentStaticWordColumn.frame _ _ _ _ _ (away.imp id (fun hi=>early.trans ((Nat.le_add_right ..).trans hi))))

theorem read (here total : Bank) (base P Q out H : ℕ) (m : Memory w) (N : ℕ) (name : Fin N→Fin P)
    (full : N≤H) (count : m total.base=(N:Word w)) (inverse : ∀i,m (here.base+i.val)=((name i).val:Word w))
    (input : here.Fits w base) (cnt : total.Fits w base) (extent : N≤here.size)
    (early : base+words P≤out) (room : stop out H<2^w) (h : Fin H) (s : Fin 2) :
    after here total base P Q out H m ((output out H s).base+h.val)=
      ((if l : h.val<N then value Q s (name ⟨h.val,l⟩).val else 0):Word w):=by
  let init:=DescentStaticWordColumn.image base (literal P Q) m (words P)
  let t:=finProdFinEquiv ((0:Fin 1),s)
  have cap : out<2^w:=(Nat.le_add_right ..).trans_lt room
  have f:=(fit here total base P out s input cnt early cap)
  have valueRead:=DescentResetOriginalSlots.read (X:=1) (Function.Embedding.refl (Fin 2)) out H (cols here total base P) init t
    (by simpa [t,cols] using f) h
  have before (addr : ℕ) (first : addr < base) : init addr = m addr :=
    DescentStaticWordColumn.frame base (words P) (literal P Q) m addr (.inl first)
  have oldCount : total.read init ((0 : ℕ) : Word w) = (N : Word w) := by
    calc
      _ = init (total.base + 0) := DescentPackedZip.bank_read total init (i := 0) cnt.1 cnt
      _ = (N : Word w) := by
        rw [Nat.add_zero]
        exact (before _ ((Nat.lt_add_of_pos_right cnt.1).trans_le cnt.2.2)).trans count
  have small : H<2^w:=by
    have hr:=DescentResetOriginalSlots.rows_le H
    change out+1*2*DescentResetOriginalSlots.stride H<2^w at room
    omega
  have wn : N<2^w:=full.trans_lt small
  have outs : (output out H s).base=out+(DescentResetOriginalSlots.cell (Function.Embedding.refl (Fin 2)) t).val*DescentResetOriginalSlots.stride H:=by
    simp [output,DescentResetOriginalSlots.bank,DescentResetOriginalSlots.offset,t,DescentResetOriginalSlots.cell]
    left
    change s.val = s.val + 2 * (0 : ℕ)
    simp
  have which : cols here total base P t = expr here total base P s := by
    simp only [cols,t,Equiv.symm_apply_apply]
  have test : DescriptorExpr.Comparison.lt.test (h.val : Word w) (N : Word w) = decide (h.val < N) := by
    simp [DescriptorExpr.Comparison.test,Fin.lt_def,Fin.val_cast_of_lt wn,Fin.val_cast_of_lt (h.isLt.trans small)]
  rw [outs]
  apply valueRead.trans
  rw [which]
  change (if DescriptorExpr.Comparison.lt.test (h.val : Word w) (total.read init ((0 : ℕ) : Word w)) then
    (tab base P s).read init (here.read init (h.val : Word w)) else ((0 : ℕ) : Word w)) = _
  rw [oldCount,test]
  by_cases inside : h.val < N
  · rw [ite_eq_left (decide_eq_true inside),dite_eq_left inside]
    let i : Fin N := ⟨h.val,inside⟩
    have oldRange : h.val < here.size := inside.trans_le extent
    have previous : here.read init (h.val : Word w) = ((name i).val : Word w) :=
      (DescentPackedZip.bank_read here init oldRange input).trans
        ((before _ ((Nat.add_lt_add_left oldRange here.base).trans_le input.2.2)).trans (inverse i))
    have lim : (name i).val < DescentResetOriginalSlots.stride P :=
      (name i).isLt.trans_le (DescentResetOriginalSlots.rows_le P)
    have span := (tab_range base P s).trans early
    have tableFits : (tab base P s).Fits w out :=
      ⟨Nat.two_pow_pos _,(Nat.le_add_left _ _).trans_lt (span.trans_lt cap),span⟩
    have idx : s.val*DescentResetOriginalSlots.stride P+(name i).val < words P := by
      have hi:=Nat.mul_le_mul_right (DescentResetOriginalSlots.stride P) s.isLt
      rw [Nat.succ_mul] at hi
      change _ < 2 * DescentResetOriginalSlots.stride P
      omega
    have literal_at (digit : Fin 2) (raw : ℕ) (hr : raw < DescentResetOriginalSlots.stride P) :
        literal P Q (digit.val*DescentResetOriginalSlots.stride P+raw) = value Q digit raw := by
      have high : ¬ DescentResetOriginalSlots.stride P + raw < DescentResetOriginalSlots.stride P := by omega
      fin_cases digit
      · simp [literal,value,hr]
      · simp [literal,value,high]
    rw [previous,DescentPackedZip.bank_read (tab base P s) init (i := (name i).val) lim tableFits]
    change init (base+s.val*DescentResetOriginalSlots.stride P+(name i).val) = _
    rw [Nat.add_assoc]
    exact (DescentStaticWordColumn.read base (words P) (literal P Q) m idx).trans
      (congrArg (fun raw : ℕ => (raw : Word w)) (literal_at s (name i).val lim))
  · rw [ite_eq_right (fun yes => inside (of_decide_eq_true yes)),dite_eq_right inside]
    exact Fin.natCast_zero (n := 2^w)

end
end Hierarchy.DescentResetCompactGeometry

end OAI
