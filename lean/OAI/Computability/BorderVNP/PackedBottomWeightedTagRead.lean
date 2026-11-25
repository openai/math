import OAI.Computability.BorderVNP.PackedBottomWeightedFiber
import OAI.Computability.BorderVNP.DiagonalTaggedProgramModels

/-! # The pointwise tagged read of an original weighted sparse box

Fixing the original guesses leaves exactly one compatible passing work vector
when the corresponding term is live. Every reported scalar observation in this
box has positive sign and carries no gadget identifier.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open Inherited.Site.Programs

/-- Equality of the extracted original guess tuple is exactly agreement at
the numerical copy-stride offsets of the offset-zero birth region. -/
theorem Slab.decodeWork_eq_iff (s : Slab) (copies : ℕ) (work : Fin (copies*s.stride) → Bool)
    (guess : Fin copies → Fin s.guessed → Bool) :
    s.decodeWork copies work = guess ↔
      ∀ (i : Fin copies) (k : Fin s.guessed), extendWork work (i.val*s.stride+k.val) = guess i k := by
  have atGuess (i : Fin copies) (k : Fin s.guessed) :
      s.decodeWork copies work i k = extendWork work (i.val*s.stride+k.val) := by
    have kfit : k.val < s.stride := by
      have h := s.fineFits
      have h' := k.isLt
      simp only [Slab.stride, Slab.orig, bottomStride]
      omega
    let p := finProdFinEquiv (i,(⟨k.val,kfit⟩ : Fin s.stride))
    have ix : p.val = i.val*s.stride+k.val := by dsimp [p, finProdFinEquiv]; ac_rfl
    rw [←ix, extendWork, dite_eq_left p.isLt]
    rfl
  constructor
  · intro h i k
    exact (atGuess i k).symm.trans (congrFun (congrFun h i) k)
  · intro h
    exact funext fun i => funext fun k => (atGuess i k).trans (h i k)

end Packing.BottomReports

namespace Packing.BottomGridBank

open Crossing CellSparse CellAddresses GridBoxes BottomReports Inherited Diagonal.CellEntries
open scoped Classical

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

/-- All compatible physical observations of the weighted box, including a
canonical work vector when the designated term fails. The compatibility
predicate refers only to the original independent digits. -/
noncomputable def weightedTagRead {Param Gadget : Type*} (tag : Entry Param Gadget) (number : Gadget ↪ ℕ)
    (guess : Fin copies → Fin (guessedSize N cell v) → Bool)
    (live : tag ≠ 0 ↔ (∀ i, pad (slice₀ input i)) ∧ ∀ i, pass₀ (guess i) (fine₀ input i))
    (empty : (counters tag).2 = 0) :
    Site.TagRead state input (fun work => ∀ (i : Fin copies) (k : Fin (s).guessed),
      Site.Programs.extendWork work (i.val*(s).stride+k.val) = guess i k) tag number := by
  let uses := fun (g : Fin copies → Fin (s).guessed → Bool) i => select₀ (g i) (fine₀ input i)
  let E := (s).dynamicGuessEquiv copies (fine₀ input) (slice₀ input) uses
  have decode : (s).decodeWork copies (E guess).val = guess := E.symm_apply_apply guess
  let obs := List.replicate (copies*(box).length) ((false,none) : Bool × Option ℕ)
  refine ⟨(E guess).val, obs, ((s).decodeWork_eq_iff copies _ _).mp decode, ?_, ?_⟩
  · intro work os agree
    have gEq := ((s).decodeWork_eq_iff copies _ _).mpr agree
    have accepted := weighted_acceptance N cell position pack width owner lane aligned siteID edgeID portID
      channelID groupID v rules copies capFine capReport hf hc input work
    constructor
    · intro seen
      have pass := congrArg Option.isSome seen
      obtain ⟨checked,padding,guards⟩ := accepted.mp pass
      let w : {w // (s).DynamicChecks copies (fine₀ input) (slice₀ input) uses w} := ⟨work, checked⟩
      have orig : E.symm w = guess := gEq
      have eqWork : work = (E guess).val :=
        congrArg Subtype.val ((E.apply_symm_apply w).symm.trans (congrArg E orig))
      rw [gEq] at guards
      have value := weighted_observations N cell position pack width owner lane aligned siteID edgeID portID
        channelID groupID v rules copies capFine capReport (bits work input) pass
      exact ⟨live.mpr ⟨padding,guards⟩, eqWork, Option.some.inj (seen.symm.trans value)⟩
    · rintro ⟨alive,rfl,rfl⟩
      obtain ⟨padding,guards⟩ := live.mp alive
      apply weighted_observations N cell position pack width owner lane aligned siteID edgeID portID channelID groupID v rules
      apply accepted.mpr
      rw [decode]
      exact ⟨(E guess).property,padding,guards⟩
  · intro _ g
    simp only [obs, List.filterMap_replicate_of_none (show Prod.snd ((false,none) : Bool × Option ℕ) = none from rfl),
      List.count_nil, empty, Finsupp.zero_apply]

end Packing.BottomGridBank

end BorderVNP
end Computability
end OAI
