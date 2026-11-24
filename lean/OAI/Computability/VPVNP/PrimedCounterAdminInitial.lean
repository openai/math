import OAI.Computability.VPVNP.PrimedCounterAdminFrame
import OAI.Computability.VPVNP.PrimedInputRAMHeaders

/-!
# Initial parser state after the primed input passes

The parser's input rectangle is the output of the second pass. Its stack,
marks and production counters begin immediately beyond that rectangle. The
prescribed header memory initializes these scratch cells to zero and stores
the nominated histogram before the first-pass rectangle.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedCounter.Admin

open BurstRAM PrimedInputRAM PrimedStackRAM
open scoped Fin.CommRing

variable {L : Lengths} {n r H s w : ℕ} (Q : Layout L n r H w)
variable (hdr : Header L → Bool) (bits : Internal L r H w → Bool) (hist : List (Word w))

private theorem assembled_outside (bitWord : Bool → Word w) (initial : Memory w) (a : ℕ)
    (ha : a < Q.scratchBase ∨ Q.scratchBase + PrimedInputRAM.positions n r + PrimedInputRAM.positions n r ≤ a) :
    Q.assembled bitWord bits initial a = initial a := by
  rw [Layout.assembled, secondPass_outside]
  · apply store_outside
    intro i _
    change a ≠ Q.scratchBase + i.val
    have := i.isLt
    omega
  · intro i
    change a ≠ Q.scratchBase + PrimedInputRAM.positions n r + i.val
    have := i.isLt
    omega

/-- Each nomination word remains available at the prescribed histogram offset. -/
theorem assembled_nomination (hf : Header.count L + hist.length ≤ Q.scratchBase)
    (j : Fin hist.length) :
    Q.assembled (encodeBit w) bits (headerMemory L hdr hist) (Header.count L + j.val) = hist[j] := by
  rw [assembled_outside Q bits _ _ _ (Or.inl (by have := j.isLt; omega)), headerMemory_hist]
  simp [j.isLt]

/-- After both passes the pending list, marks and accumulated histogram are empty,
while every terminal read already sees its prescribed input bit. -/
theorem assembled_holds (hf : Header.count L + hist.length ≤ Q.scratchBase) :
    Holds (Q.scratchBase + PrimedInputRAM.positions n r)
      (fun g v j => input Q.program Q.fits hdr bits (g,v) j)
      (⟨[], ∅, 0⟩ : VisitState n n s)
      (Q.assembled (encodeBit w) bits (headerMemory L hdr hist)) := by
  let base := Q.scratchBase + PrimedInputRAM.positions n r
  let final := Q.assembled (encodeBit w) bits (headerMemory L hdr hist)
  have hzero (a : ℕ) (ha : base + PrimedInputRAM.positions n r ≤ a) : final a = 0 := by
    change Q.assembled (encodeBit w) bits (headerMemory L hdr hist) a = _
    rw [assembled_outside Q bits _ _ _ (Or.inr ha)]
    have he : Header.count L + (a - Header.count L) = a := by dsimp [base] at ha; omega
    rw [← he, headerMemory_hist, List.getElem?_eq_none (by dsimp [base] at ha; omega)]
    rfl
  refine ⟨⟨by simp [frames], ?_, fun i => i.elim0, fun i => i.elim0⟩, ?_, ?_, ?_⟩
  · change (final (address base (depthCell : Locations (2^r) n n s))).val = 0
    rw [depthCell, address_depth, hzero _ (by unfold PrimedInputRAM.positions; omega)]
    rfl
  · intro g v j
    have haddr : (Q.outputAddress (finProdFinEquiv (finProdFinEquiv (g,v), j))).val =
        address base (.inl ((g,v),j) : Locations (2^r) n n s) := by
      rw [address_input]
      change base + (j.val + n * (v.val + 2^r * g.val)) = _
      ring
    unfold view
    rw [← haddr, Q.assembled_input _ bits hdr _ (headerMemory_bits L hdr hist)]
    cases input Q.program Q.fits hdr bits (g,v) j <;> simp [encodeBit]
  · intro j
    change final (address base (markCell j : Locations (2^r) n n s)) = _
    rw [markCell, address_mark, hzero _ (by unfold PrimedInputRAM.positions; omega)]
    simp
  · intro a
    change (final (address base (countCell (labelIndex n n s a) : Locations (2^r) n n s))).val = _
    rw [countCell, address_hist, hzero _ (by unfold PrimedInputRAM.positions; omega)]
    rfl

end PrimedCounter.Admin

end VPVNP
end Computability
end OAI
