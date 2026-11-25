import OAI.Hierarchy.DescentTerminalRowArena

namespace OAI
/-! # Native priming of the parity and half-index arrays at the reached word address -/

namespace Hierarchy.DescentTerminalRowArena.Arena
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Fin.CommRing
noncomputable section
variable {w : ℕ} (A : Arena)

private def parity : Expr := .op .mask .row (.lit 1)
private def incrementHalf : Expr := .branch .eq .row (.lit 0) (.lit 0) (.op .sub (.lit 1) parity)
private def halfState (i : ℕ) : Word w := (((i-1)/2 : ℕ) : Word w)

def prime (w : ℕ) := (scan w (A.atBand 0) (2*A.sites) parity).seq
  (DescentTerminalHeaderPrefixRAM.program w (A.atBand 1) (2*A.sites) .add incrementHalf)

theorem prime_text (w : ℕ) :
    (A.prime w).labels+(A.prime w).registers+(A.prime w).slots=110 := by
  simp only [prime,Procedure.seq,scan,DescentTerminalHeaderPrefixRAM.program,
    PhysicalInputPhases.writing,Term.labels_eq,compile_binds,DescentTerminalHeaderPrefixRAM.binds]; rfl

private theorem parity_read (m : Memory w) (i : ℕ) (hi : i < 2^w) (one : 1 < 2^w) :
    parity.eval m (i : Word w)=((i%2 : ℕ) : Word w) := by
  change Fin.ofNat (2^w) (((i : Word w).val) &&& (((1 : ℕ) : Word w).val))=_
  rw [Fin.val_cast_of_lt hi,Fin.val_cast_of_lt one]
  have bit : i &&& 1=i%2 := Nat.and_two_pow_sub_one_eq_mod i 1
  rw [bit]; rfl

private theorem prefix_step (m : Memory w) (i : ℕ) (hi : i < 2^w) (one : 1 < 2^w) :
    halfState i+incrementHalf.eval m (i : Word w)=halfState (i+1) := by
  have val := parity_read m i hi one
  by_cases zero : i=0
  · subst i
    simp [halfState,incrementHalf,Expr.eval,Comparison.test]
  · have nonzero : (i : Word w) ≠ 0 := by
      intro e
      exact zero (by simpa only [Fin.val_cast_of_lt hi,Fin.val_zero] using congrArg Fin.val e)
    have small : i%2 ≤ 1 := by omega
    have delta : (i-1)/2+(1-i%2)=i/2 := by omega
    change halfState i+(if Comparison.eq.test (i : Word w) 0 then 0 else
      BinaryOp.sub.eval 1 (parity.eval m (i : Word w)))=_
    simp only [Comparison.test,beq_iff_eq,nonzero,ite_false,BinaryOp.eval,val,halfState,Nat.add_sub_cancel]
    simpa only [Nat.cast_add,Nat.cast_sub small,Nat.cast_one] using
      congrArg (fun j : ℕ => (j : Word w)) delta

private def parityImage (m : Memory w) := fillSegment (A.atBand 0) (2*A.sites)
  (fun x => (((x-A.atBand 0)%2 : ℕ) : Word w)) m

private theorem parity_image (m : Memory w) (fit : A.finish < 2^w) :
    image (A.atBand 0) (2*A.sites) parity m=A.parityImage m := by
  have cap := A.stride_min
  have close := A.end_word fit (by decide : 0 < 22) (show 2*A.sites ≤ A.stride by omega)
  have bank := A.fits_band fit (by decide : 0 < 2) (by decide)
  have room : A.stride < 2^w := bank.2.1
  funext x
  simp only [image,parityImage,fillSegment]
  split
  · rename_i live
    have lo := live.1
    rw [← Nat.cast_sub lo]
    exact parity_read m _ (by omega) (by omega)
  · rfl

/-- The two scans run from arbitrary scratch memory. They generate the exact
two finite arrays and leave every other word equal to its input. -/
theorem prime_run (m : Memory w) (fit : A.finish < 2^w) :
    (A.prime w).Exec m (A.mount m) (8+104*A.sites) ∧ CheapCode (A.prime w) := by
  have cap := A.stride_min
  have bound : 2*A.sites ≤ A.stride := by omega
  have bank := A.fits_band fit (by decide : 0 < 2) (by decide)
  have room : A.stride < 2^w := bank.2.1
  have fits0 : parity.Fits w (A.atBand 0) := ⟨trivial,trivial⟩
  have fits1 : incrementHalf.Fits w (A.atBand 1) := by
    simp [incrementHalf,parity,Expr.Fits]
  have first : (scan w (A.atBand 0) (2*A.sites) parity).Exec m
      (image (A.atBand 0) (2*A.sites) parity m) (4+2*A.sites*(2*parity.work+4)) :=
    @scan_exec w (A.atBand 0) (2*A.sites) parity m fits0 (A.end_word fit (by decide) bound)
  rw [A.parity_image m fit] at first
  have second : (DescentTerminalHeaderPrefixRAM.program w (A.atBand 1) (2*A.sites) .add incrementHalf).Exec
      (A.parityImage m) (fillSegment (A.atBand 1) (2*A.sites)
        (DescentTerminalHeaderPrefixRAM.file (A.atBand 1) (halfState (w:=w))) (A.parityImage m))
      (4+2*A.sites*(2*DescentTerminalHeaderPrefixRAM.work .add incrementHalf+4)) :=
    @DescentTerminalHeaderPrefixRAM.spec w (2*A.sites) (A.atBand 1) .add incrementHalf (A.parityImage m)
      (halfState (w:=w)) trivial fits1 (A.end_word fit (by decide) bound) (by rfl)
      (fun (i : Fin (2*A.sites)) => prefix_step _ _ (i.isLt.trans_le (bound.trans room.le)) (by omega))
  have target : fillSegment (A.atBand 1) (2*A.sites)
      (DescentTerminalHeaderPrefixRAM.file (A.atBand 1) (halfState (w:=w))) (A.parityImage m)=A.mount m := by
    have contents : DescentTerminalHeaderPrefixRAM.file (A.atBand 1) (halfState (w:=w)) =
        fun x => (((x-A.atBand 1)/2 : ℕ) : Word w) := by
      funext x
      simp only [DescentTerminalHeaderPrefixRAM.file,halfState,Nat.add_sub_cancel]
    exact congrArg (fun values => fillSegment (A.atBand 1) (2*A.sites) values (A.parityImage m)) contents
  rw [target] at second
  refine ⟨?_,cheap_seq (@scan_cheap _ _ _ _) (DescentTerminalHeaderPrefixRAM.cheap w (A.atBand 1) (2*A.sites) .add incrementHalf)⟩
  have cost : (4+2*A.sites*(2*parity.work+4))+
      (4+2*A.sites*(2*DescentTerminalHeaderPrefixRAM.work .add incrementHalf+4))=8+104*A.sites := by
    change (4+2*A.sites*(2*4+4))+(4+2*A.sites*(2*18+4))=8+104*A.sites
    omega
  rw [←cost]
  exact @Procedure.Exec.then w (scan w (A.atBand 0) (2*A.sites) parity)
    (DescentTerminalHeaderPrefixRAM.program w (A.atBand 1) (2*A.sites) .add incrementHalf)
    m (A.parityImage m) (A.mount m) _ _ (@first) (@second)

end
end Hierarchy.DescentTerminalRowArena.Arena

end OAI
