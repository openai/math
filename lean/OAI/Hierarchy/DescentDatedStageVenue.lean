import OAI.Hierarchy.DescentDatedOperandHeader
import OAI.Hierarchy.DescentDatedVenueSources
import OAI.Hierarchy.DescentSignedCableFields
import OAI.Hierarchy.DescentReached

namespace OAI
/-! # Shared physical venue of a reached ordinary or reset date -/
namespace Hierarchy.DescentSixParty
open DescentCompiler DescentPackedColony DescentColonies DescentSIMDLookup
open DescentPacking.PackedMatch.Local.Stage ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] {u : ℕ} {bits : P→ℕ} {W : MarkedWorld F u P bits}
variable {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule}
    {k age z D wire s H w : ℕ} (r : Reached W G q ε S k age z D wire s)
local notation "g₀" => S.groupCount age

/-- The world-dependent source, with the actual physical banks kept fixed
when a reached world's write-order is identified with the original one. -/
def stageVenue (wide : Fintype.card r.V≤ H) (i : Dated.Operands) (M countBits floor : ℕ)
    (rs : Fin H→Fin D→Option (Fin H)) (m : Memory w) : Prop :=
  let host:=r.vertex.trans (Fin.castLEEmb wide)
  Accessible (i.ports D) i.actors H g₀ M w floor ∧
    Mounted (i.ports D) rs m g₀ M ∧
    Reads i.actors (Prepare.actors r.placement (Function.Embedding.refl _) host) M m ∧
    (∀(x : Block k) (j : Fin (2*r.placement.cap)),Reads (i.wire x.val j.val) (fun h g=>
      DescentSignedCableCodec.encode (Prepare.signed r.placement (r.order.trans Fin.valEmbedding)
        S r.valid (Function.Embedding.refl _) host x j h g)) M m) ∧
    i.hubs.Fits w floor ∧ H ≤ i.hubs.size ∧
    (∀h : Fin H,m (i.hubs.base+h.val)=((Census.hub r.placement host h).val:Word w)) ∧
    (∀x,(i.atoms x).Fits w floor) ∧
    ∀x : Block k,DescentPackedZip.Source (i.atoms x.val)
      (fun h g=>Census.count r.placement (Equiv.refl _) host countBits h g x) M m

end
end Hierarchy.DescentSixParty

end OAI
