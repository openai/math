import OAI.Hierarchy.DescentCanonicalSeedHistory
import OAI.Hierarchy.DescentTerminalEpochRoutes
import OAI.Hierarchy.DescentTerminalEpochLocalProfiles
import OAI.Hierarchy.DescentTerminalSharedProfileROM
import OAI.Hierarchy.DescentTerminalSeedChip

namespace OAI
/-! # The original short selector data and dense matched profiles on the actual numbered seed tree -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentInitialHost DescentSeedRoot DescentColonies DescentTerminalEpochChart DescentTerminalEpochBits
open DescentTerminalEpochDecoder Chronology DescentGL Catalyst Computability.BorderVNP.Crossing
open ThreeFlat Routing
open scoped Classical BigOperators
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {cp data : ℕ}
    {u ε : ℝ} (G : PoweredGadget F) (hu : 0 ≤ u) (he : 0 ≤ ε)
    (X : Approximation F cp data) (R s w : ℕ) (fit : s < 2^w) {groups k : ℕ}
    (digits : Fin R ≃ Fin groups×Block k) {J h C Ht t : ℕ}
variable (run : Epochs G hu he (h:=h) (C:=C) (Ht:=Ht) (t:=t) J (initial X R s groups k digits)) (order : EpochOrders G hu he run)

def packedChart : Chart (selectBit X (R:=R) (s:=s) w) (valid X (R:=R) (s:=s))
    (fun c : (Epochs.finish G hu he run).Choice => Epochs.seedChoice G hu he (H:=initial X R s groups k digits) (J:=J) (t:=t) (h:=h) (C:=C) (Ht:=Ht) run c) :=
  epochsWith G hu he (H:=initial X R s groups k digits) (t:=t) (h:=h) (C:=C) (Ht:=Ht) (J:=J) run order (seedChart X R s w fit)
local notation "ch" => packedChart G hu he X R s w fit digits run order

local instance : Fintype (ch).Pin := (ch).finite

def route : Route ch :=
  epochRoute G hu he run order (seedChart X R s w fit) (seedRoute X R s w fit)

theorem packed_once (c : (Epochs.finish G hu he run).Choice) : ∃!z,(ch).read z=some c := (ch).once c

theorem seed_read (z : (ch).Pin→Bool) (c : (Epochs.finish G hu he run).Choice) (success : (ch).read z=some c)
    (key : CountKey X R) :
    (rawCount X (z∘(ch).seed) key).val=selected X (Epochs.seedChoice G hu he (H:=initial X R s groups k digits) (J:=J) (t:=t) (h:=h) (C:=C) (Ht:=Ht) run c) key := by
  have actual := ((ch).read_iff z c).mp success
  have old : z∘(ch).seed=selectBit X w (Epochs.seedChoice G hu he (H:=initial X R s groups k digits) (J:=J) (t:=t) (h:=h) (C:=C) (Ht:=Ht) run c) :=
    funext fun a=>(congrFun actual ((ch).seed a)).trans ((ch).original c a)
  rw [old]
  exact raw_select X fit _ key

theorem raw_prefix (z : (ch).Pin→Bool) :
    let c:=(route G hu he X R s w fit digits run order).follow z
    List.IsPrefix ((ch).counts z) ((epochsSelections G run c).map (selectionCount G)) := by
  let rr:=route G hu he X R s w fit digits run order
  have charged:=epochs_counts G hu he run order (seedChart X R s w fit) (rr.follow z)
  have eqn : (ch).counts ((ch).store (rr.follow z))=(epochsSelections G run (rr.follow z)).map (selectionCount G):= charged
  have prefix_ := rr.prefix z
  rw [eqn] at prefix_
  exact prefix_

theorem «fields» (c : (Epochs.finish G hu he run).Choice) :
    (ch).layout.map (rawAt ((ch).store c))=(epochsRanked G run order c).map (issuedProfile G) := by
  exact epochs_profiles G hu he run order (seedChart X R s w fit) c

theorem fields_of_read (z : (ch).Pin→Bool) (c : (Epochs.finish G hu he run).Choice) (selected : (ch).read z=some c) :
    (ch).layout.map (rawAt z)=(epochsRanked G run order c).map (issuedProfile G) := by
  rw [((ch).read_iff _ _).mp selected]
  exact «fields» G hu he X R s w fit digits run order c

theorem uniform : Uniform G.C (ch).layout :=
  epochs_uniform G hu he run order (seedChart X R s w fit) (by intro a ha;cases ha)

theorem pin_count :
    Fintype.card (ch).Pin=Fintype.card (Select X R s)+epochSeats G hu he run*DescentTerminalEpochBits.width G.C :=
  epochsWith_size G hu he run order (seedChart X R s w fit)

/-- The measured datum is an exponent in the original, unmodified coefficient menu. -/
theorem source_weight (c : (Epochs.finish G hu he run).Choice) :
    (Epochs.finish G hu he run).weight c=∏i : CountKey X R,(originalScalar X i)^(selected X (Epochs.seedChoice G hu he (H:=initial X R s groups k digits) (J:=J) (t:=t) (h:=h) (C:=C) (Ht:=Ht) run c) i) :=
  (Epochs.weight_initial G hu he _ run c).trans (DescentSeedRoot.original_weight X _)

theorem seed_numerator (z : (ch).Pin→Bool) (c : (Epochs.finish G hu he run).Choice) (success : (ch).read z=some c) :
    TypedWiring.value (DescentTerminalSeedChip.circuit X (ch).seed) z=(Epochs.finish G hu he run).weight c := by
  rw [DescentTerminalSeedChip.value,source_weight G hu he X R s digits run]
  apply Finset.prod_congr rfl
  intro i _
  rw [seed_read G hu he X R s w fit digits run order z c success i]

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
