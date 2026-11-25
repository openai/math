import OAI.Computability.BorderVNP.CubeISAOwnedDigits
import OAI.Computability.BorderVNP.CubeISAOwnedSingletons
import OAI.Computability.BorderVNP.RoutingISATableState

/-! # Native endpoint addresses of a singleton trial

The ordered row symbols are inserted into the two tail addresses before the
singleton filter tests the pair. These are exactly the public base-`d` codes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.Owned

/-- Both native endpoint addresses coincide with the full public product labels
of the trial, including labels on a diagonal row. -/
theorem singleEndpointCodes {n d : ℕ} (i : Fin (n+1)) (a b : Fin d) (t : Fin (singlePairTrials n d)) :
    let u := (singleOrderedPairs i a b t).val
    (finFunctionFinEquiv u.1).val = insertDigit d (d^i.val) a.val (t.val / d^n) ∧
      (finFunctionFinEquiv u.2).val = insertDigit d (d^i.val) b.val (t.val % d^n) := by
  change (finFunctionFinEquiv (i.insertNth (α := fun _ => Fin d) a
    (finFunctionFinEquiv.symm (finProdFinEquiv.symm t).1))).val = _ ∧
    (finFunctionFinEquiv (i.insertNth (α := fun _ => Fin d) b
    (finFunctionFinEquiv.symm (finProdFinEquiv.symm t).2))).val = _
  rw [rank_insertNth, rank_insertNth, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  exact ⟨rfl,rfl⟩

end Cube.Physical.Owned

namespace RoutingISA.Owned

open VPVNP.BurstRAM Cube.Physical.Owned

/-- Insert each fixed grouping symbol into the corresponding quotient or remainder
tail. Outputs 24 and 25 are the public labels, 29 and 30 their unmodified tails. -/
def prepareSingle : Code := .block [
  .binary .div 29 18 11, .binary .mod 30 18 11,
  .binary .mod 31 29 12, .binary .div 32 29 12, .binary .mul 32 10 32,
  .binary .add 32 14 32, .binary .mul 32 12 32, .binary .add 24 31 32,
  .binary .mod 31 30 12, .binary .div 32 30 12, .binary .mul 32 10 32,
  .binary .add 32 15 32, .binary .mul 32 12 32, .binary .add 25 31 32]

private theorem digitFits {d p a t limit : ℕ} (hp : 0 < p)
    (hf : insertDigit d p a t < limit) :
    d*(t/p) < limit ∧ a+d*(t/p) < limit ∧ p*(a+d*(t/p)) < limit := by
  have := Nat.le_mul_of_pos_left (a+d*(t/p)) hp
  unfold insertDigit at hf
  omega

/-- Exact fourteen-tick preparation. Only the actual endpoint codes have to
fit; all intermediate natural products and sums then fit as well. -/
theorem prepareSingle_run {w : ℕ} (pub : Arg → Word w) (macros : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) {d place tails a b trial : ℕ}
    (r10 : readings s 10 = d) (r11 : readings s 11 = tails) (r12 : readings s 12 = place)
    (r14 : readings s 14 = a) (r15 : readings s 15 = b) (r18 : readings s 18 = trial)
    (hp : 0 < place) (ht : 0 < tails)
    (srcFit : insertDigit d place a (trial/tails) < 2^w)
    (dstFit : insertDigit d place b (trial%tails) < 2^w) :
    BoundedRun pub macros prepareSingle s m 14 (fun z =>
      z.reg 24 = insertDigit d place a (trial/tails) ∧
      z.reg 25 = insertDigit d place b (trial%tails) ∧ z.reg 29 = trial/tails ∧
      z.reg 30 = trial%tails ∧ (∀ j : Reg, j.val < 24 → z.reg j = readings s j) ∧ z.mem = readings m) := by
  let st := NatState.ofWords s m
  have hs := digitFits hp srcFit
  have hd := digitFits hp dstFit
  have safe : prepareSingle.fixedSafe w (readings pub) st := by
    simp (config := {decide := true}) [prepareSingle, Code.block, Code.fixedSafe, Code.safeReadOnly,
      Code.fixedEval, Code.evalNat, addressOp, addressOpFits, st, NatState.ofWords,
      r10,r11,r12,r14,r15,r18,hp,ht]
    unfold insertDigit at srcFit dstFit
    tauto
  apply (prepareSingle.runFixed pub macros s m safe).mono (by decide)
  intro z hz
  subst z
  refine ⟨?_,?_,?_,?_,fun j hj => prepareSingle.fixedEval_protected _ st (by decide) j hj, rfl⟩ <;>
    simp (config := {decide := true}) [prepareSingle, Code.block, Code.fixedEval, Code.evalNat,
      addressOp, NatState.ofWords, r10,r11,r12,r14,r15,r18,insertDigit]

end RoutingISA.Owned

end BorderVNP
end Computability
end OAI
