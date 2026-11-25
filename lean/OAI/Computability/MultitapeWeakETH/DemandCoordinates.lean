import OAI.Computability.MultitapeWeakETH.ShrinkABTape
import OAI.Computability.VPVNP.PairShrinkRoleMapLabels

/-! # The four demand endpoints of the selected six-party input -/

namespace OAI.Computability.MultitapeWeakETH.ShrinkMap

open IntegerMultiplication VPVNP Compression Compression.ShrinkMotif NetworkKernel PairSimulation
open LocalHistory MapResidentRows MotifEntry
open private input_bits from OAI.Computability.VPVNP.PairShrinkCallDemandCells
open scoped Classical
noncomputable section

private theorem input_word {n : ℕ} (bits : Fin n → Bool) :
    inputBits ((RAMSerialization.wordBits n).symm bits) = bits := funext (input_bits bits)

variable {a g : ℕ} (X : State a (packingLaneBits a g)) (layout : Bool) (m : X.packingData.Motif)
local notation "P" => X.packingData

set_option maxHeartbeats 900000 in
/-- The old-demand gather yields the binary coordinates passed to the
selected local map at each incident source and target. -/
theorem demand_coordinates (j : Fin 6) (v : Site X) (loc : (P).shrinkPartySite layout m j = v)
    (old : Placed ((P).shrinkPlace layout) ((P).oldWireNetwork X.packingWidth).Half v)
    (bits : Bool → Bool → Bits.Word)
    (ab : ∀ dir (h : v = packedSiteEquiv (ShrinkOldHalves.abSite X m dir)),
      bits dir false = List.ofFn (ShrinkAB.operand (P) X.shrinkNumber X.shrinkOrder X.packingWidth ⟨m,rfl⟩
        (State.two_le_packingColors _) (Nat.two_pow_pos _) (ShrinkOldHalves.abData X layout m dir
          ((P).shrinkPlacedHalf X.packingWidth layout _ h old))))
    (c : ∀ h : v = packedSiteEquiv ((P).placement layout ((P).C m)), bits false true =
      List.ofFn ((P).localCWord X.packingWidth layout m ((P).shrinkPlacedHalf X.packingWidth layout _ h old)))
    (d : ∀ h : v = packedSiteEquiv ((P).roleD layout m), bits true true =
      List.ofFn ((P).localDWord X.packingWidth layout m ((P).shrinkPlacedHalf X.packingWidth layout _ h old))) :
    let arg := (P).shrinkLocalDemandArg (State.two_le_packingColors _) (Nat.two_pow_pos _)
      X.shrinkNumber X.shrinkOrder X.packingWidth layout m j (loc.symm ▸ old)
    (∀ e (h : j = demandSource e), bits false e = List.ofFn (inputBits (arg.1 e h))) ∧
      (∀ e (h : j = demandTarget e), bits true e = List.ofFn (inputBits (arg.2 e h))) := by
  subst v
  constructor
  · intro e h
    subst j
    cases e with
    | false =>
      change bits false false = List.ofFn (inputBits ((RAMSerialization.wordBits _).symm _))
      erw [input_word]
      exact ab false rfl
    | true =>
      change bits false true = List.ofFn (inputBits ((RAMSerialization.wordBits _).symm _))
      erw [input_word]
      exact c ((P).shrinkPartySite_C layout m)
  · intro e h
    subst j
    cases e with
    | false =>
      change bits true false = List.ofFn (inputBits ((RAMSerialization.wordBits _).symm _))
      erw [input_word]
      exact ab true rfl
    | true =>
      change bits true true = List.ofFn (inputBits ((RAMSerialization.wordBits _).symm _))
      erw [input_word]
      exact d rfl

end
end OAI.Computability.MultitapeWeakETH.ShrinkMap
