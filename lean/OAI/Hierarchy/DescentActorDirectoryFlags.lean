import OAI.Hierarchy.DescentPackedZip
import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # One live reset-directory flag per static rack, including isolated actors -/
namespace Hierarchy.DescentActorRaster.Flags
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical Fin.CommRing
noncomputable section
variable {N G M w : ℕ}

theorem chunks_present (bits : Fin N→Fin G→Cell 1) (rack : Fin N) (hm : 0<M) (wide : M≤w) :
    (∃j : Fin (chunks G M),((data bits (rack,j)).val:Word w)≠0) ↔ ∃g,bits rack g≠0 := by
  constructor
  · rintro ⟨j,live⟩
    by_contra! absent
    have nil : data bits (rack,j)=(0:Cell (1*M)):=by
      unfold data
      have key : (fun s : Fin M=> if h : j.val*M+s.val<G then bits rack ⟨_,h⟩ else 0)=fun _=>0:=by
        funext y
        split <;> simp [absent]
      rw [key]
      apply Fin.ext
      simp [encode]
    simp [nil] at live
  · rintro ⟨g,hit⟩
    let j:=(position rack g hm).2
    refine ⟨j,?_⟩
    intro zero
    have raw:(data bits (rack,j)).val < 2^w:=(data bits (rack,j)).isLt.trans_le
      (Nat.pow_le_pow_right (by decide) (by simpa using wide))
    have val := congrArg Fin.val zero
    simp only [Fin.val_cast_of_lt raw,Fin.val_zero] at val
    let l:=lane g hm
    have ix:j.val*M+l.val=g.val:=by
      change g.val/M*M+g.val%M=g.val
      exact Nat.div_add_mod' ..
    have small:j.val*M+l.val<G:=ix.symm ▸ g.isLt
    have hdigit:=digit_encode (b:=1) (M:=M) (fun s : Fin M=>if ok:j.val*M+s.val<G then bits rack ⟨_,ok⟩ else 0) l
    change digit 1 l.val (data bits (rack,j)).val=_ at hdigit
    rw [val] at hdigit
    have eq : (⟨j.val*M+l.val,small⟩:Fin G)=g:=Fin.ext ix
    simp only [dite_eq_left small,eq] at hdigit
    apply hit
    apply Fin.ext
    simpa [DescentSIMDLookup.digit] using hdigit.symm

/-- Each physical page address is the static shape-major stencil-actor offset
of one sparse rack. Its complete chunk row can be empty. -/
def poll (roots src : Bank) : ℕ→Expr
  | 0=>.lit 0
  | j+1=>.branch .eq (.lookup src (.op .add (.lookup roots .row) (.lit j))) (.lit 0)
      (poll roots src j) (.lit 1)

theorem read (roots src : Bank) (pos : Fin N→ℕ) (part : Fin N→Fin (chunks G M)→Word w)
    (m : Memory w) (base : ℕ) (rootFit : roots.Fits w base) (srcFit : src.Fits w base)
    (nr : N≤roots.size) (span : ∀i,pos i+chunks G M ≤ src.size)
    (root : ∀i,m (roots.base+i.val)=(pos i:Word w))
    (inputs : ∀i j,m (src.base+(pos i+j.val))=part i j) (i : Fin N) :
    (poll roots src (chunks G M)).eval m (i.val:Word w)=if ∃j,part i j≠0 then 1 else 0 := by
  have aux (a : ℕ) (ok : a≤chunks G M) :
      (poll roots src a).eval m (i.val:Word w)=if ∃j,j.val<a ∧ part i j≠0 then 1 else 0 := by
    induction a with
    | zero=>simp [poll,Expr.eval]
    | succ a ih=>
      let j : Fin (chunks G M):=⟨a,by omega⟩
      have bound : pos i+a<src.size:=by have:=span i;omega
      have atWord : (.lookup src (.op .add (.lookup roots .row) (.lit a)) : Expr).eval m (i.val:Word w)=part i j := by
        simp only [Expr.eval,bank_read _ _ (i.isLt.trans_le nr) rootFit,root,RowOp.opcode,BinaryOp.eval,←Nat.cast_add]
        exact (bank_read _ _ bound srcFit).trans (inputs i j)
      have split : (∃j',j'.val<a+1 ∧ part i j'≠0) ↔
          (∃j',j'.val<a ∧ part i j'≠0) ∨ part i j≠0:=by
        constructor
        · rintro ⟨l,hl,active⟩
          by_cases lt:l.val<a
          · exact Or.inl ⟨l,lt,active⟩
          · exact Or.inr ((show l=j from Fin.ext (by dsimp [j];omega)) ▸ active)
        · rintro (⟨l,hl,active⟩|active)
          · exact ⟨l,by omega,active⟩
          · exact ⟨j,by simp [j],active⟩
      change (if Comparison.eq.test ((.lookup src (.op .add (.lookup roots .row) (.lit a)) : Expr).eval m (i.val:Word w)) 0 then
        (poll roots src a).eval m (i.val:Word w) else 1)=_
      rw [atWord,ih (by omega)]
      simp only [split]
      by_cases zero:part i j=0 <;>simp [Comparison.test,zero]
  simpa using aux (chunks G M) le_rfl

theorem fits (roots src : Bank) (base : ℕ) (hr : roots.Fits w base) (hs : src.Fits w base)
    (_one : 1<2^w) (a : ℕ) (room : a≤2^w) : (poll roots src a).Fits w base := by
  induction a with
  | zero=>simp [poll,Expr.Fits]
  | succ a ih=>simp [poll,Expr.Fits,hr,hs,ih (by omega)]

def emit (roots src : Bank) (base N chunks_ w : ℕ) :=
  scan w base N (poll roots src chunks_)

theorem issue (roots src : Bank) (pos : Fin N→ℕ) (part : Fin N→Fin (chunks G M)→Word w)
    (m : Memory w) (base : ℕ) (rootFit : roots.Fits w base) (srcFit : src.Fits w base)
    (nr : N≤roots.size) (span : ∀i,pos i+chunks G M ≤ src.size)
    (root : ∀i,m (roots.base+i.val)=(pos i:Word w))
    (inputs : ∀i j,m (src.base+(pos i+j.val))=part i j)
    (one : 1<2^w) (chunksOK : chunks G M≤2^w) (room : base+N<2^w) :
    let e:=poll roots src (chunks G M)
    let out:=ProtocolRAM.image base N e m
    (emit roots src base N (chunks G M) w).Exec m out (4+N*(2*e.work+4)) ∧
      (∀i,out (base+i.val)=if ∃j,part i j≠0 then 1 else 0) ∧
      ∀a,a<base ∨ base+N≤a → out a=m a := by
  exact ⟨scan_exec _ _ _ _ (fits _ _ _ rootFit srcFit one _ chunksOK) room,
    fun i=>(ProtocolRAMGeneratedWrite.read_image base N _ m i).trans
      (read roots src pos part m base rootFit srcFit nr span root inputs i),
    ProtocolRAMGeneratedWrite.frame_image base N _ m⟩

end
end Hierarchy.DescentActorRaster.Flags

end OAI
