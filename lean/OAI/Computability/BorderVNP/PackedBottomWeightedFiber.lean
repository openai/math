import OAI.Computability.BorderVNP.PackedBottomWeightedValue
import OAI.Computability.BorderVNP.PackedInheritedObservationFiber

/-! # Observation fibers of unlinked weighted original boxes

The positive native observation sequence has one physical work assignment for
each passing fine-wire tuple. The equivalence exposes the exact canonical
completion and its prescribed selected bits at all physical copy offsets.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomGridBank

open Crossing CellSparse CellAddresses GridBoxes BottomReports Inherited
open scoped Classical
open private checked_lane from OAI.Computability.BorderVNP.PackedBottomScalarValue

variable {D H : ℕ} {P C Q A : Type} [Fintype P] [Fintype C] [Fintype Q] [Fintype A]
variable (N : Network D P (fun _ => 1)) (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1}) {src dst : Q → C}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable (width : A → ℕ) (owner : A → C) (lane : P ↪ (a : A) × Fin (width a))
variable (aligned : ∀ p, owner (lane p).1 = cell (N.attach p))
variable {ns ne np qe qa : ℕ} (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne)
variable (portID : P ↪ Fin np) (channelID : Q ↪ Fin qe) (groupID : A ↪ Fin qa) (v : C)
variable (rules : ∀ w : {u : N.Site // cell u = v}, Rule N w.val)
variable (copies capFine capReport : ℕ) (hf : GridBoxes.stride N cell v ≤ capFine)
    (hc : Fintype.card {u : N.Site // cell u = v} ≤ capReport)

local notation "G" => grouped (src := src) (dst := dst) (H := H) N cell position width owner
local notation "s" => slab (H := H) (src := src) (dst := dst) N cell position width owner siteID edgeID portID v rules capFine capReport hf hc
local notation "state" => born N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules copies capFine capReport
local notation "box" => stored N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules capFine capReport
local notation "slice₀" => scalarSlice (src := src) (dst := dst) (H := H) N cell position width owner channelID groupID v copies
local notation "fine₀" => scalarFine N cell position pack width owner lane aligned edgeID portID channelID groupID v copies
local notation "select₀" => selectedUses N cell siteID edgeID portID v rules
local notation "pass₀" => finePass N cell edgeID portID v rules
local notation "pad" => publicPad N cell position pack width owner channelID groupID v

variable (input : Fin (incoming (BottomRepeat.wide
  (grouped (src := src) (dst := dst) (H := H) N cell position width owner) copies) v) → Bool)

set_option maxHeartbeats 450000 in
/-- Passing original guesses are precisely the inputs yielding the actual positive
native observation sequence. The inverse decodes just the fine-wire prefix of
each original copy. -/
noncomputable def weightedFiberEquiv :
    {g : Fin copies → Fin (guessedSize N cell v) → Bool //
      (∀ i, pad (slice₀ input i)) ∧ ∀ i, pass₀ (g i) (fine₀ input i)} ≃
      (state).Fiber input (List.replicate (copies*(box).length) (false,none)) := by
  let uses (g : Fin copies → Fin (s).guessed → Bool) (i : Fin copies) := select₀ (g i) (fine₀ input i)
  let E := (s).dynamicGuessEquiv copies (fine₀ input) (slice₀ input) uses
  let ok := weighted_acceptance N cell position pack width owner lane aligned siteID edgeID portID channelID groupID
    v rules copies capFine capReport hf hc input
  have decode (g : Fin copies → Fin (s).guessed → Bool) :
      (s).decodeWork copies (E g).val = g :=
    (s).decode_checked copies (fine₀ input) (slice₀ input) (uses g) g
  have passing (w : (state).Fiber input (List.replicate (copies*(box).length) (false,none))) :
      (s).DynamicChecks copies (fine₀ input) (slice₀ input) uses w.val ∧
      (∀ i, pad (slice₀ input i)) ∧ ∀ i, pass₀ ((s).decodeWork copies w.val i) (fine₀ input i) := by
    apply (ok w.val).mp
    exact congrArg Option.isSome w.property
  refine ⟨fun g => ⟨(E g.val).val,?_⟩,fun w => ⟨(s).decodeWork copies w.val,(passing w).2⟩,
    fun g => Subtype.ext (decode g.val),?_⟩
  · apply weighted_observations N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules
    apply (ok (E g.val).val).mpr
    exact ⟨(E g.val).property,g.property.1,fun i =>
      (congrArg (fun h => pass₀ (h i) (fine₀ input i)) (decode g.val)).mpr (g.property.2 i)⟩
  · intro w
    apply Subtype.ext
    let good := (s).DynamicChecks copies (fine₀ input) (slice₀ input) uses
    let w' : {work // good work} := ⟨w.val,(passing w).1⟩
    exact congrArg (fun q : {work // good work} => q.val) (E.apply_symm_apply w')

set_option maxHeartbeats 450000 in
/-- Every represented private work bit belongs to the actual one-copy completion
of its fine guesses, the packed input and the selected report values. -/
theorem weightedFiber_lane (g : {g : Fin copies → Fin (guessedSize N cell v) → Bool //
      (∀ i, pad (slice₀ input i)) ∧ ∀ i, pass₀ (g i) (fine₀ input i)})
    (i : Fin copies) (k : Fin (s).stride) :
    ((weightedFiberEquiv N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v
      rules copies capFine capReport hf hc input g).val) (finProdFinEquiv (i,k)) =
      (s).complete (g.val i) (fine₀ input i) (slice₀ input i) (select₀ (g.val i) (fine₀ input i)) k :=
  checked_lane (s) copies (fine₀ input) (slice₀ input) (fun i => select₀ (g.val i) (fine₀ input i)) g.val i k

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
