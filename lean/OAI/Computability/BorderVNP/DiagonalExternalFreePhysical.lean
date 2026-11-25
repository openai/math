import OAI.Computability.BorderVNP.DiagonalExternalFreeNetwork
import OAI.Computability.BorderVNP.DiagonalExternalSewPhysical

/-! # Contraction at the actual grouped literal and pinned processor slots -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing CellEntries TeamContraction ParseBatch
open scoped Classical BigOperators

variable {R r w link V g D : ℕ} {P : Type} {N : Network D P (fun _ => 1)}
    {physical : PublicPort R r w link ≃ P} (h : BlockHosts N physical g)
    (hg : 0 < g) (room : r*(2*w+R*link) ≤ V*g)

/-- Select the actual stored host of a named original grid block. -/
def BlockHosts.groupOwner (a : FreeBlock R V) : N.Site := h.host (a.1,a.2.val)

/-- The sewn network and the free slot packing use the same retained original
grid-block host at every literal and pin bit. -/
theorem BlockHosts.groupAligned (p : FreePort R r w) :
    h.groupOwner (freeLane hg room p).1 = h.bundle.layout.attach p := by
  let u := publicPortEquiv R r w link (.inl p)
  change h.host (u.1,(teamOrdinal u).val/g) = N.attach (physical u)
  rw [h.attach,teamOrdinal_val]
  rfl

/-- The fully sewn and grouped network retains every tracked use bit and tag. -/
noncomputable def BlockHosts.grouped {Team Param Gadget : Type*} [Fintype Team] [Fintype Param]
    {b : ℕ} (t : Tracked Team Param Gadget b N) :=
  (h.bundle.tracked t).packExternal (fun _ : FreeBlock R V => g) (freeLane hg room) h.groupOwner (h.groupAligned hg room)

variable {t d inner n : ℕ} {Edge : Type} (G : Wiring R r t d link inner n Edge)
    {physical : PublicPort R r (G.program.length+t) link ≃ P} (h : BlockHosts N physical g)
    (hg : 0 < g) (room : r*(2*(G.program.length+t)+R*link) ≤ V*g)

/-- Whatever bits the receiver stores in exterior gaps or padding, the contraction
reads exactly its actual free-field deliveries and sums over all real exterior wire
assignments. No branch depends on the contents of an unused lane. -/
theorem physical_grouped {Team Param Gadget E : Type*} [Fintype Team] [Fintype Param] [CommSemiring E]
    {b : ℕ} (t0 : Tracked Team Param Gadget b N) (values : Gadget → E) (pin : Fin d → Bool)
    (bank : Ports (fun _ : FreeBlock R V => g))
    (delivered : ∀ p, bank (freeLane hg room p).1 (freeLane hg room p).2 = freeBits G pin p) :
    ((h.grouped hg room t0).valued values).tensor bank =
      ∑ ext : Exterior R r link → Bool, (t0.valued values).tensor
        (fun p _ => Prewire.publicBits G (physical.symm p).1 pin ext (physical.symm p).2) := by
  have eq : Network.readExternal _ (freeLane hg room) bank = fun p _ => freeBits G pin p :=
    funext fun p => funext fun _ => delivered p
  have val := h.bundle.layout.value_packExternal (fun _ : FreeBlock R V => g) (freeLane hg room)
    h.groupOwner (h.groupAligned hg room) ((h.bundle.tracked t0).valued values).table bank
  rw [eq] at val
  exact val.trans (physical_tracked G h t0 values pin)

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
