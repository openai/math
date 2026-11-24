import OAI.Computability.VPVNP.PrimedInputRAMHeaders
import OAI.Computability.VPVNP.PrimedInputRAMUniform

/-!
# Native RAM histories for the two primed input passes

In Section 11 each internal bit has one owner in the first pass. The second
pass copies the owner's bit to every position that refers to it. For the
prescribed header memory, the accepting native histories are in bijection
with all internal assignments, and their reports recover the parser's input
at every site and bit offset.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedInputRAM.Layout

open BurstRAM

variable {L : Lengths} {n r H w : ℕ} (Q : Layout L n r H w)

/-- The public cursor reaches both complete rectangles and the final halt. -/
theorem cursorFits (Q : Layout L n r H w) : positions n r + positions n r < 2^w := by
  have h := Q.headersFit
  have := Q.addressesFit
  unfold Header.count at h
  omega

/-- Instantiate the two passes at the addresses of the primed tapes. -/
def twoPass (bitWord : Bool → Word w) : TwoPass (positions n r) w where
  own := Q.owns
  scratch := Q.bitAddress
  dest := Q.outputAddress
  source := Q.source bitWord

/-- The burst-RAM program that first chooses shared bits in the layout and then copies the
resolved input bits into their rows. -/
def inputProgram (bitWord : Bool → Word w) : Program w (Dispatch w) :=
  scheduledProgram (Q.twoPass bitWord).ops bitWord Q.cursorFits

/-- Native reports including the terminal call, for an internal assignment. -/
def inputReports (bitWord : Bool → Word w) (bits : Internal L r H w → Bool)
    (m : Memory w) : List (Report w) :=
  (Q.twoPass bitWord).completeReports bitWord Q.cursorFits (Q.assignment bits) m

theorem inputReports_cost (bitWord : Bool → Word w) (bits : Internal L r H w → Bool)
    (m : Memory w) : RAMBuckets.cost Report.probes (Q.inputReports bitWord bits m) ≤
      5 * positions n r + 1 :=
  (Q.twoPass bitWord).completeReports_cost_le bitWord Q.cursorFits (Q.assignment bits) m

theorem after_inputReports (bitWord : Bool → Word w) (bits : Internal L r H w → Bool)
    (m : Memory w) : after m (eventLog (Q.inputReports bitWord bits m)) =
      Q.assembled bitWord bits m :=
  (Q.twoPass bitWord).after_completeReports bitWord Q.cursorFits (Q.assignment bits) m

/-- All prescribed words below the first scratch address survive both passes. -/
theorem inputReports_preserve_header (bitWord : Bool → Word w) (bits : Internal L r H w → Bool)
    (m : Memory w) {a : ℕ} (ha : a < Q.scratchBase) :
    after m (eventLog (Q.inputReports bitWord bits m)) a = m a := by
  rw [Q.after_inputReports, assembled, secondPass_outside]
  · exact store_header _ _ _ _ _ ha
  · intro i
    change a ≠ Q.scratchBase + positions n r + i.val
    omega

/-- Each of the three cut lengths fits in its header word. The exterior
lengths are bounded by the reserved header capacity and the middle length
by the number of sites in one rectangle. -/
theorem cutLength_lt (Q : Layout L n r H w) (j : Fin 3) : cutLength L j < 2 ^ w := by
  have hfit := Q.fits
  unfold ProcessorInput.Fits at hfit
  have hn : 1 ≤ n := by omega
  have hsites : 2 * 2 ^ r ≤ positions n r := Nat.le_mul_of_pos_right _ hn
  have hrect := Q.cursorFits
  have hh := Q.headersFit
  unfold Header.count at hh
  have := Q.addressesFit
  have := Q.middleFits
  have := L.leftFit
  have := L.rightFit
  unfold cutLength
  split_ifs <;> omega

/-- A fetch of any supplied cut length yields the exact natural number,
also after the choice and copy phases have run. -/
theorem inputReports_cutLength (bits : Internal L r H w → Bool) (hdr : Header L → Bool)
    (hist : List (Word w)) (j : Fin 3) :
    (after (headerMemory L hdr hist)
      (eventLog (Q.inputReports (encodeBit w) bits (headerMemory L hdr hist))) j.val).val =
      cutLength L j := by
  have hh := Q.headersFit
  unfold Header.count at hh
  rw [Q.inputReports_preserve_header _ _ _ (by have := j.isLt; omega), headerMemory_length]
  exact Nat.mod_eq_of_lt (Q.cutLength_lt j)

/-- The bounded, accepting histories of this RAM enumerate the internal bits
with their full multiplicity. The site and bucket parameters here are those
of the auxiliary RAM, which may differ from the primed parameters. -/
def inputPathEquiv (bitWord : Bool → Word w) (m : Memory w) {S K : ℕ}
    (hK : 3 ≤ K) (hTotal : 5 * positions n r + 1 ≤ S * K) :
    ActualPaths (Q.inputProgram bitWord) 3 0 m (withinCaps S K) ≃ (Internal L r H w → Bool) :=
  ((Q.twoPass bitWord).actualPathEquiv bitWord Q.cursorFits m hK hTotal).trans
    (Q.internalOwner.symm.arrowCongr (Equiv.refl _))

/-- Every path produces the reports of its decoded internal assignment. -/
theorem run_inputPath (bitWord : Bool → Word w) (m : Memory w) {S K : ℕ}
    (hK : 3 ≤ K) (hTotal : 5 * positions n r + 1 ≤ S * K)
    (p : ActualPaths (Q.inputProgram bitWord) 3 0 m (withinCaps S K)) :
    runSegment (Q.inputProgram bitWord) 3 (some 0) m p.val =
      some (Q.inputReports bitWord (Q.inputPathEquiv bitWord m hK hTotal p) m) := by
  let e := Q.inputPathEquiv bitWord m hK hTotal
  obtain ⟨bits, rfl⟩ := e.symm.surjective p
  rw [show Q.inputPathEquiv bitWord m hK hTotal (e.symm bits) = bits from e.apply_symm_apply bits]
  exact (Q.twoPass bitWord).run_completeReports bitWord Q.cursorFits (Q.assignment bits) m

/-- At every leaf, the words written by the accepting run give the complete
primed parse input on its assignment, including the exterior header bits. -/
theorem run_input_bits (hdr : Header L → Bool) (hist : List (Word w)) {S K : ℕ}
    (hK : 3 ≤ K) (hTotal : 5 * positions n r + 1 ≤ S * K)
    (p : ActualPaths (Q.inputProgram (encodeBit w)) 3 0 (headerMemory L hdr hist) (withinCaps S K))
    {rs : List (Report w)}
    (hr : runSegment (Q.inputProgram (encodeBit w)) 3 (some 0) (headerMemory L hdr hist) p.val =
      some rs) (u : Site r) (j : Fin n) :
    after (headerMemory L hdr hist) (eventLog rs)
        (Q.outputAddress (finProdFinEquiv (finProdFinEquiv u, j))).val =
      encodeBit w (input Q.program Q.fits hdr
        (Q.inputPathEquiv (encodeBit w) (headerMemory L hdr hist) hK hTotal p) u j) := by
  rw [Option.some.inj (hr.symm.trans (Q.run_inputPath _ _ hK hTotal p)), Q.after_inputReports]
  exact Q.assembled_input _ _ _ _ (headerMemory_bits L hdr hist) u j

end PrimedInputRAM.Layout

end VPVNP
end Computability
end OAI
