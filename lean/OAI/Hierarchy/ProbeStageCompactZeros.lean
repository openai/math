import OAI.Hierarchy.ProbeStageCompactWindow
import OAI.Hierarchy.ProbeStageRawInput

namespace OAI
/-! # The eight staging cells are zero at every subdivision level -/

namespace Hierarchy.ProbeStage.Native.Compact
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open scoped Fin.CommRing
noncomputable section

theorem images_zero {h d : ℕ} (hd : 1≤d) (hh : 4≤h) (π : Equiv.Perm (Fin (2^h)))
    (raw : Memory (wordBits h d copies)) (read : ∀r : Fin (2^h),raw r.val=((π r).val : Word _))
    (k : ℕ) (hk : k≤rounds d) (q : Fin 8) :
    images h d (inputTape h d _ raw) k (base h+q.val)=0 := by
  let input:=inputTape h d (wordBits h d copies) raw
  induction k with
  | zero =>
    have small : 8≤2^h := (show 8≤2^4 by decide).trans (Nat.pow_le_pow_right (by decide) hh)
    let r : Fin (2^h):=⟨q.val,q.isLt.trans_le small⟩
    have fit : ∀e∈([.lit 0,.row] : List Expr),e.Fits (wordBits h d copies) (2^h) := by
      simp [Expr.Fits]
    simpa [base,images,rootPasses,Expr.eval,r,input] using
      (columns_read (n:=2^h) (base:=2^h) ([.lit 0,.row] : List Expr) input le_rfl fit 0 (by decide) r)
  | succ k ih =>
    let j : Fin (rounds d):=⟨k,by omega⟩
    have prev:=after_levels hd π raw read (physical_ordinal hd π) k (by omega)
    obtain ⟨fixed,fresh⟩:=prev.future j le_rfl
    have next:=phase_result hd π j (images h d input k) fixed prev.parent fresh (physical_ordinal hd π j)
    have lo:=window_before (d:=d) hh j.val
    exact (next.frame _ (Or.inl (by have := q.isLt; omega))).trans (ih (by omega))

theorem prepared_zero {h d w : ℕ} (hh : 4≤h) (j : ℕ) (m : Memory w)
    (zero : ∀q : Fin 8,m (base h+q.val)=0) (q : Fin 8) :
    result (prepareRows h d j) m (base h+q.val)=0 := by
  apply Eq.trans _ (zero q)
  apply columns_frame
  left
  have lo:=window_before (d:=d) hh j
  have before : phase h d copies j≤allocatorBase h d copies j := Nat.le_add_right ..
  have := q.isLt
  omega

theorem visit_zero {h d k : ℕ} {hd : 1≤d} {π : Equiv.Perm (Fin (2^h))} {j : Fin (rounds d)}
    (hh : 4≤h) {input : Memory (wordBits h d copies)} (v : Visit hd π j input k)
    (zero : ∀q : Fin 8,input (base h+q.val)=0) (q : Fin 8) :
    records h d j.val input k (base h+q.val)=0 := by
  apply Eq.trans (v.frame _ _) (zero q)
  intro i _ writes
  have after:=(mayWrite_region writes).1
  have before:=window_before (d:=d) hh j.val
  have :=q.isLt
  omega

end
end Hierarchy.ProbeStage.Native.Compact

end OAI
