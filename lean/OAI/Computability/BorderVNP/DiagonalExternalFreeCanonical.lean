import OAI.Computability.BorderVNP.DiagonalExternalFreePreparation
import OAI.Computability.BorderVNP.DiagonalExternalFreePassing
import OAI.Computability.BorderVNP.DiagonalExternalFreePhysical

/-! # The actual received free arguments on a fully assigned sewn path

A signed evaluation can use the same named input bank on every history
of a given raw substitution. The bijection leaves all assigned bits
in place and preserves the original cell factors and selected powers.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.ExternalSew

open Crossing CellEntries TeamContraction RoutingISA RoutingISA.Transmission RoutingISA.Pins
open VPVNP.BurstRAM BorderVNP.Cube
open scoped Classical

variable {R r t pins link inner n w V g : ℕ} {Edge : Type} {G : Wiring R r t pins link inner n Edge}
    (hg : 0 < g) (room : r*(2*(G.program.length+t)+R*link) ≤ V*g)

/-- History-independent Boolean input, with zero on unused grouped lanes. -/
noncomputable def canonicalBank (bits : Fin pins → Bool) : Ports (fun _ : FreeBlock R V => g) :=
  fillFree hg room (freeBits G bits) fun _ => false

/-- The bank used in the numbered row reads the true literal and the raw
substitution at every live input lane. -/
theorem canonical_read (bits : Fin pins → Bool) (z : FreePort R r (G.program.length+t)) :
    let a := freeLane hg room z
    canonicalBank (G := G) hg room bits a.1 a.2 = freeBits G bits z :=
  fillFree_read hg room (freeBits G bits) (fun _ => false) z

variable {inputPin : Fin pins → Bool} {ext : Exterior R r link → Bool} {wire : Routing.WireLayout (R+1) r link}
    {entries desc : ℕ} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
    {H : Fin (R+1) → TeamHistory w} {ib hb sb : Fin (R+1) → ℕ}
    (delivery : ReturnedDelivery G inputPin ext wire (freeDirectory R r (G.program.length+t) link V g entries desc)
      pp lp owner origin stride H (fun u => G.pinLayout u (ib u) (hb u) (sb u)))
    (bits : Fin pins → Bool)
    (subst : ∀ u, SubstitutionAt (G.pinLayout u (ib u) (hb u) (sb u)) (extendGuess bits) (H u).initial)

local notation "actual" => receivedBank (V := V) (g := g) lp owner origin stride H
local notation "fixedBank" => canonicalBank (G := G) hg room bits

include delivery subst in
/-- Every participating receiver buffer agrees with the fixed named input
bank on the coordinates used by the compressed box tables. -/
theorem received_used (z : FreePort R r (G.program.length+t)) :
    let a := freeLane hg room z
    actual a.1 a.2 = fixedBank a.1 a.2 :=
  (received_raw_bank delivery hg room bits subst z).trans (canonical_read hg room bits z).symm

variable {D B cn cd b ht K s : ℕ} {P Team Param Gadget : Type} [Fintype Team] [Fintype Param]
    {N : Network D P (fun _ => 1)} {physical : PublicPort R r (G.program.length+t) link ≃ P}
    (hosts : BlockHosts N physical g) (t0 : Tracked Team Param Gadget B N)
    (packet : PacketPlacement (D := D) (P := FreeBlock R V) (bits := fun _ => g) Team cn cd b ht K
      (hosts.bundle.freeGroups hosts.groupOwner))
    (pos : TableEntry cn b ht K s → Gadget)

/-- Each passing assignment on the actual local memories contributes one
assignment on the same dense history and canonical substituted inputs. -/
noncomputable def receivedPassingEquiv :
    packet.Passing (hosts.grouped hg room t0) actual pos ≃ packet.Passing (hosts.grouped hg room t0) fixedBank pos :=
  groupedPassingEquiv (N := hosts.bundle.layout) _ (freeLane hg room) hosts.groupOwner
    (hosts.groupAligned hg room) (hosts.bundle.tracked t0) actual fixedBank
    (received_used hg room delivery bits subst) packet pos

/-- The canonical assignment records the very same unary bits and all
the same local scalar multiplicities as the actual receiver assignment. -/
theorem receivedPassing_tally (a : packet.Passing (hosts.grouped hg room t0) actual pos) :
    packet.tally (hosts.grouped hg room t0) fixedBank pos
        (receivedPassingEquiv hg room delivery bits subst hosts t0 packet pos a) =
      packet.tally (hosts.grouped hg room t0) actual pos a :=
  grouped_passing_tally (N := hosts.bundle.layout) _ (freeLane hg room) hosts.groupOwner
    (hosts.groupAligned hg room) (hosts.bundle.tracked t0) actual fixedBank
    (received_used hg room delivery bits subst) packet pos a

end Diagonal.ExternalSew

end BorderVNP
end Computability
end OAI
