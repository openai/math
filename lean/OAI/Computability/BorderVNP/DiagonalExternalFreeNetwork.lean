import OAI.Computability.BorderVNP.DiagonalExternalFreeGroups
import OAI.Computability.BorderVNP.DiagonalExternalSew
import OAI.Computability.BorderVNP.DiagonalExternalSewAncestry
import OAI.Computability.BorderVNP.PackedGridExternal

/-! # The physically sewn pack with one free argument word per team and grid site

The immutable original processor ordinals give the lanes. The attained shortening
history supplies the receiving host. Every power use and every coefficient are
retained after replacing the individual free leaves by their grouped argument words.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing CellEntries
open scoped Classical BigOperators

variable {D R r w link V g : ℕ} {P Cable : Type} [Fintype Cable] {width : Cable → ℕ}
    {N : Network D P (fun _ => 1)} (B : Bundle N (FreePort R r w) Cable width)
    (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g)

/-- Terminal grouped network in the physical team-major grid-site order. -/
abbrev Bundle.freeGroups (hosts : FreeBlock R V → N.Site) :=
  B.layout.packExternal (fun _ : FreeBlock R V => g) hosts

/-- A retained site carries precisely the same free processor bits as its original
grid-site interval. The paired exterior ends have already become cables. -/
theorem Bundle.free_aligned {N₀ : Network D P (fun _ => 1)} (ret : Retains N₀ N)
    (physical : PublicPort R r w link ≃ P) (hosts : FreeBlock R V → N₀.Site)
    (leaves : ∀ p, N₀.attach (physical p) = hosts (publicLane hg room p).1)
    (named : ∀ p, B.ports (.inl p) = physical (publicPortEquiv R r w link (.inl p))) :
    ∀ p, ret.site (hosts (freeLane hg room p).1) = B.layout.attach p := by
  intro p
  change ret.site (hosts (publicLane hg room (publicPortEquiv R r w link (.inl p))).1) = N.attach (B.ports (.inl p))
  rw [named,ret.attach,leaves]

/-- The native slot table may leave unaddressed exterior and tail lanes arbitrary.
Every supplied genuine bit has exactly its original selected value. -/
theorem readExternal_fill (input : FreePort R r w → Bool) (unused : (Σ _ : FreeBlock R V, Fin g) → Bool) :
    Network.readExternal (fun _ : FreeBlock R V => g) (freeLane hg room) (fillFree hg room input unused) =
      (fun p _ => input p) := by
  funext p _
  exact fillFree_read hg room input unused p

/-- Grouping the post-sewing argument rows preserves the full tracked tensor with
all of its named unary occurrences and the sum over the physical exterior cables. -/
theorem Bundle.grouped_tensor {Team Param Gadget E : Type*} [Fintype Team] [Fintype Param]
    [CommSemiring E] {b : ℕ} (t : Tracked Team Param Gadget b N) (values : Gadget → E)
    (hosts : FreeBlock R V → N.Site) (aligned : ∀ p, hosts (freeLane hg room p).1 = B.layout.attach p)
    (input : FreePort R r w → Bool) (unused : (Σ _ : FreeBlock R V, Fin g) → Bool) :
    ((((B.tracked t).packExternal (fun _ : FreeBlock R V => g) (freeLane hg room) hosts aligned).valued values).tensor
      (fillFree hg room input unused)) =
    ∑ y : Ports width, (t.valued values).tensor (B.joined (fun p _ => input p) y) := by
  have val := B.layout.value_packExternal (fun _ : FreeBlock R V => g) (freeLane hg room) hosts aligned
    ((B.tracked t).valued values).table (fillFree hg room input unused)
  rw [readExternal_fill hg room] at val
  exact val.trans (B.tracked_tensor t values _)

/-- One public argument descriptor per original team and grid site, irrespective
of the number of literal and pinned bits on that site. -/
theorem freeGroups_port_count (R V : ℕ) : Fintype.card (FreeBlock R V) = (R+1)*V := by simp [FreeBlock]

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
