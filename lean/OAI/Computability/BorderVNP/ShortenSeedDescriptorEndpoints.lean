import OAI.Computability.BorderVNP.ShortenSeedDescriptorPorts

/-!
# Names of the two endpoint records of a matched segment

The seed ID, direction and side identify the terminal. The old site name and
source/destination bit identify the retained slot. The two rows share the same
cable name, width and starting ordinal in the common terminal word.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.SeedIntervals

open Crossing

/-- Public fields identifying one endpoint of a matched piece. -/
structure EndpointRecord where
  /-- Cable descriptor, including its original local offset and common matched ordinal. -/
  wire : CutDescriptor
  /-- Public address of the seed. -/
  seedId : ℕ
  /-- Axis of the terminal pair. -/
  axis : ℕ
  /-- Which end of the old cable this row represents. -/
  source : Bool
  /-- Positive or negative crossing terminal. -/
  side : Bool
  /-- Public name of the retained endpoint's site. -/
  oldSite : ℕ

variable {D : ℕ} [NeZero D] {P : Type*} {bits : P → ℕ} (N : Network D P bits)
variable {A : Type} (bin : N.Edge → Option A) (perm : Fin D → Equiv.Perm A) (m : ℕ)
variable (binName : A → ℕ) (siteName : N.Site → ℕ) (positive : N.Edge → Bool)

/-- Serialize the actual old site, seed, direction, sign and interval at a single cut end. -/
noncomputable def endpointRecord (a : A) (d : Fin D)
    (e : {e : N.Edge // bin e = some (perm d a)}) (source : Bool) : EndpointRecord :=
  ⟨descriptor N bin perm m binName e (some (d,true)), binName a, d.val, source,
    if source then positive e.val else !(positive e.val),
    siteName (if source then N.src e.val else N.dst e.val)⟩

/-- The actual cut slot to which one public endpoint record refers. -/
noncomputable def cutSlot (a : A) (d : Fin D) (e : {e : N.Edge // bin e = some (perm d a)})
    (source : Bool) : (layout N bin perm m).CutPorts ((partition N bin perm m).part a) :=
  if source then .inl (prefixEdge N bin perm m a d e).val else .inr (prefixEdge N bin perm m a d e).val

/-- The public site name agrees with the old endpoint's actual attachment in the cut network. -/
theorem endpointRecord_attach (a : A) (d : Fin D) (e : {e : N.Edge // bin e = some (perm d a)})
    (source : Bool) :
    let row := endpointRecord N bin perm m binName siteName positive a d e source
    siteName (((layout N bin perm m).cut ((partition N bin perm m).part a)).attach
      (.inr (cutSlot N bin perm m a d e source))) = row.oldSite := by
  cases source <;> rfl

/-- The axis and sign fields of the record agree with the bundle's actual terminal map. -/
theorem endpointRecord_terminal (a : A) (d : Fin D) (e : {e : N.Edge // bin e = some (perm d a)})
    (source : Bool) :
    let row := endpointRecord N bin perm m binName siteName positive a d e source
    let terminal := (bundle N bin perm m positive a).terminal (cutSlot N bin perm m a d e source)
    (terminal.1.val, terminal.2) = (row.axis, row.side) := by
  cases source <;> rfl

/-- The record's terminal-side field and relative ordinal read the old source or destination
slot, even when the orientation flag reverses the pair of terminals. -/
theorem endpointRecord_gather (a : A) (d : Fin D) (e : {e : N.Edge // bin e = some (perm d a)})
    (source : Bool) (s : Ports ((layout N bin perm m).cutWidths ((partition N bin perm m).part a)))
    (k : Fin ((layout N bin perm m).width (e.val,some (d,true)))) :
    let row := endpointRecord N bin perm m binName siteName positive a d e source
    let b := bundle N bin perm m positive a
    b.gather s (d, row.side) (b.order d ⟨prefixEdge N bin perm m a d e,k⟩) =
      if source then s (.inl (prefixEdge N bin perm m a d e).val) k
      else s (.inr (prefixEdge N bin perm m a d e).val) k := by
  let b := bundle N bin perm m positive a
  let z := (prefixEdge N bin perm m a d e).val
  cases source with
  | false =>
    have h := b.gather_order s z k (!(positive e.val))
    change b.gather s (d, !(positive e.val)) (b.order d ⟨⟨z,rfl⟩, k⟩) = s (.inr z) k
    change b.gather s (d, !(positive e.val)) (b.order d ⟨⟨z,rfl⟩, k⟩) = (if positive e.val = !(positive e.val) then s (.inl z) k else s (.inr z) k) at h
    cases hp : positive e.val <;> simpa only [hp, Bool.not_false, Bool.not_true, Bool.false_eq_true,
      Bool.true_eq_false, ite_false] using h
  | true =>
    have h := b.gather_order s z k (positive e.val)
    change b.gather s (d, positive e.val) (b.order d ⟨⟨z,rfl⟩, k⟩) = s (.inl z) k
    change b.gather s (d, positive e.val) (b.order d ⟨⟨z,rfl⟩, k⟩) = (if positive e.val = positive e.val then s (.inl z) k else s (.inr z) k) at h
    simpa only [ite_true] using h

end Shortening.SeedIntervals

end BorderVNP
end Computability
end OAI
