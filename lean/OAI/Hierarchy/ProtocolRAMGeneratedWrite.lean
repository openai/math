import OAI.Hierarchy.ProtocolRAMIndexedWrite
import OAI.Hierarchy.ProtocolRAMScan

namespace OAI
/-! # Generating a sparse write stream from two cheap row expressions -/

namespace Hierarchy.ProtocolRAMGeneratedWrite

open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorScan
open ProtocolRAM
open scoped Fin.CommRing

variable {w n : ℕ}

theorem fits_mono (e : Expr) {a b : ℕ} (h : a≤b) (fit : e.Fits w a) : e.Fits w b := by
  induction e with
  | row | lit => trivial
  | lookup bank i ih => exact ⟨⟨fit.1.1,fit.1.2.1,fit.1.2.2.trans h⟩,ih fit.2⟩
  | op _ x y hx hy => exact ⟨hx fit.1,hy fit.2⟩
  | branch _ x y a b hx hy ha hb => exact ⟨hx fit.1,hy fit.2.1,ha fit.2.2.1,hb fit.2.2.2⟩

theorem read_image (base n : ℕ) (e : Expr) (m : Memory w) (i : Fin n) :
    ProtocolRAM.image base n e m (base+i.val)=e.eval m (i.val : Word w) := by
  have live : base≤base+i.val ∧ base+i.val<base+n := by have := i.isLt; omega
  simp [ProtocolRAM.image,fillSegment,live,Nat.cast_add]

theorem frame_image (base n : ℕ) (e : Expr) (m : Memory w) (a : ℕ)
    (away : a<base ∨ base+n≤a) : ProtocolRAM.image base n e m a=m a := by
  simp [ProtocolRAM.image,fillSegment,show ¬(base≤a ∧ a<base+n) by omega]

def program (w addresses words n : ℕ) (A V : Expr) : Procedure w :=
  ((scan w addresses n A).seq (scan w words n V)).seq (ProtocolRAMIndexedWrite.scatter w addresses words n)

def work (n : ℕ) (A V : Expr) : ℕ :=
  (4+n*(2*A.work+4))+(4+n*(2*V.work+4))+(3+10*n)

def image (addresses words : ℕ) (A V : Expr) (address : Fin n → ℕ) (word : Fin n → Word w)
    (m : Memory w) : Memory w :=
  ProtocolRAMIndexedWrite.image address word
    (ProtocolRAM.image words n V (ProtocolRAM.image addresses n A m)) n

/-- The source expressions see the input word banks. The two scratch columns are materialized
by native passes before the sparse stores are issued. -/
theorem run (addresses words : ℕ) (A V : Expr) (address : Fin n → ℕ) (word : Fin n → Word w)
    (m : Memory w) (ha : A.Fits w addresses) (hv : V.Fits w addresses)
    (sep : addresses+n≤words) (fit : words+n<2^w)
    (dataA : ∀ i : Fin n, A.eval m (i.val:Word w)=(address i:Word w))
    (dataV : ∀ i : Fin n, V.eval m (i.val:Word w)=word i)
    (range : ∀ i, address i<2^w)
    (safeA : ∀ i j : Fin n, addresses+i.val≠address j)
    (safeV : ∀ i j : Fin n, words+i.val≠address j) :
    (program w addresses words n A V).Exec m (image addresses words A V address word m) (work n A V) := by
  let a := ProtocolRAM.image addresses n A m
  let v := ProtocolRAM.image words n V a
  have aRun : (scan w addresses n A).Exec m a (4+n*(2*A.work+4)) := scan_exec addresses n A m ha (by omega)
  have vRun : (scan w words n V).Exec a v (4+n*(2*V.work+4)) := scan_exec words n V a (fits_mono V (by omega) hv) fit
  have loaded (i : Fin n) : v (addresses+i.val)=(address i:Word w) ∧ v (words+i.val)=word i := by
    constructor
    · exact ((frame_image words n V a _ (.inl (by have := i.isLt; omega))).trans
        (read_image addresses n A m i)).trans (dataA i)
    · rw [show v (words+i.val)=V.eval a (i.val:Word w) from read_image words n V a i]
      exact (eval_below V (i.val:Word w) m a hv (fun j hj =>
        frame_image addresses n A m j (.inl hj))).trans (dataV i)
  have scatter : (ProtocolRAMIndexedWrite.scatter w addresses words n).Exec v
      (ProtocolRAMIndexedWrite.image address word v n) (3+10*n) := by
    intro P R K M pc reg pub exit rom data cfg raw entry eq
    subst raw
    exact ProtocolRAMIndexedWrite.run addresses words address word (by omega) fit range safeA safeV
      M pc reg pub exit rom data cfg v entry loaded
  intro P R K M pc reg pub exit rom data cfg raw entry eq
  exact Procedure.Exec.then (Procedure.Exec.then aRun vRun) scatter M pc reg pub exit rom data cfg raw entry eq

theorem read (addresses words : ℕ) (A V : Expr) (address : Fin n → ℕ) (word : Fin n → Word w)
    (m : Memory w) (inj : Function.Injective address) (i : Fin n) :
    image addresses words A V address word m (address i)=word i :=
  ProtocolRAMIndexedWrite.read_unique address word _ inj n le_rfl i i.isLt

theorem frame (addresses words : ℕ) (A V : Expr) (address : Fin n → ℕ) (word : Fin n → Word w)
    (m : Memory w) (a : ℕ) (aw : ∀ i, a ≠ address i)
    (wa : a<addresses ∨ addresses+n≤a) (wv : a<words ∨ words+n≤a) :
    image addresses words A V address word m a=m a :=
  ((ProtocolRAMIndexedWrite.frame address word _ n a aw).trans
    (frame_image words n V _ a wv)).trans (frame_image addresses n A _ a wa)


end Hierarchy.ProtocolRAMGeneratedWrite

end OAI
