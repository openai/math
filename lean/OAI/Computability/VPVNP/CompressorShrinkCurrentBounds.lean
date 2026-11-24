import OAI.Computability.VPVNP.CompressorShrinkCurrentBranch

/-!
# Constructing all shrinking continuations within the input-length bounds

One threshold fixes the word width for the entire physical shrinking
boundary. After publication the actual selector and geometry runs exist
for every typed choice, independently of the later branch.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

namespace CompressorRecords.ShrinkCurrentBranch

open BurstRAM Compression DescriptorSpace CurrentGraph CursorBounds Filter
open scoped Classical Fin.CommRing

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)

theorem eventually_build (factor : ℕ) (hb : 1 ≤ factor) : ∀ᶠ n : ℕ in atTop,
    ∀ {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps) {g : ℕ}
      (X : State (S.degreeExponent i.castSucc) (packingLaneBits (S.degreeExponent i.castSucc) g)),
      X.positions ≤ initialPositions factor n → X.maxWireWidth ≤ n → ∀ (base blocks : ℕ)
      (old new : Fin (BlockProgram.layout B base (initialPositions factor n) blocks).levels)
      (m : Memory (wordBits factor n)) (fuel : ℕ),
      let L := BlockProgram.layout B base (initialPositions factor n) blocks
      let w := wordBits factor n
      let start := tableBase L old (0 : Fin 6)
      let T := packedIncidence L w old (DemandRAM.oldCount X)
      Current L old X n m → old.val+1=new.val → endAddress L < 2^w → ShrinkBranch.prefixClock B factor n ≤ fuel →
      ShrinkBranch.PrefixFits B X T start (10 : Word w) fuel ∧
        Nonempty (Common B f hf i X base (initialPositions factor n) blocks old new m fuel) := by
  filter_upwards [ShrinkBranch.eventually_prefixFits B factor hb,PrefixLevelScale.eventually_scores B factor hb,
    CursorRAM.eventual_word_room factor hb (CursorRAM.bounded_positions factor),
    CursorRAM.eventual_word_room factor hb (PolynomiallyBounded.const (slotDegree S))] with n prefixes scores sites degrees
  intro R _ f hf i g X pos mx base blocks old new m fuel L w start T current next fit clock
  have pre := prefixes i X pos mx base blocks old fit fuel clock
  exact ⟨pre,build B f hf i X base _ blocks old new m n fuel current next pos (pos.trans_lt sites) degrees fit pre
    (Nat.mod_eq_of_lt scores.1) scores.2.1 (scores.2.2 i X pos mx)⟩

end CompressorRecords.ShrinkCurrentBranch

end

end VPVNP
end Computability
end OAI
