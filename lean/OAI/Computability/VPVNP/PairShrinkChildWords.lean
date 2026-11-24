import OAI.Computability.VPVNP.PairShrinkJobOperands
import OAI.Computability.VPVNP.PairShrinkRoleMapWitness

/-!
# Initializing the first resident map from the actual child scan

The scanned child list is the fiber of the selected shrinking term. Its
argument packets contain the independent outgoing and incoming bits of
each old site, pulled into packing coordinates at their owning vertex.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkPartyNative

open Compression Compression.PackingData Compression.ShrinkMotif NetworkKernel LocalHistory
open BurstRAM NodeArguments DFS CompressorRecords CompressorRecords.ShrinkSlots

variable {K : Type} {R : Type*} [_root_.Field K] [CommRing R] {S : BlockSchedule K}
variable (B : S.Templates) (f : B.Entry → R) (hf : B.IsSolution f) (i : Fin S.steps)
variable {g w endAddr : ℕ} (X : State (S.degreeExponent i.castSucc)
  (packingLaneBits (S.degreeExponent i.castSucc) g)) (sel : X.ShrinkSelection B.shrink)
private noncomputable local instance childBase : DecidableEq X.Base := Classical.decEq _
local notation "l" => selectedLayout X B.shrink sel
private noncomputable abbrev selectedTerm := NetworkKernel.Step.term (StatePass.step
  (X.shrinkStatePass B.shrink (f ∘ Sum.inl) ((B.solution_iff f).mp hf).1 (S.shrink i))) sel

variable (v : (X.Base × BitWord (packingTagBits (2 ^ S.degreeExponent i.castSucc))) × BitWord g)
variable (x : Placed (X.packingData.shrinkPlace (selectedLayout X B.shrink sel) ∘
  X.packingInputIso.site.symm) X.network.Half v)
variable (q : X.packingData.ResidentMap (selectedLayout X B.shrink sel) v)
variable (J : Job X B.shrink (S.shrink i) sel q.1.1 q.1.2 w)

set_option maxHeartbeats 1000000 in
-- Pulling half-wire indices from the term's fiber reduces the selected placement.
theorem Job.childWords_of_packets {L : Type} [Fintype L] {κ : L → R}
    (r : TermParsers κ (selectedTerm B f hf i X sel))
    (oldEq : J.old = Eq.rec (motive := fun u _ ↦ Placed (X.packingData.shrinkPlace l)
      (X.packingData.oldWireNetwork X.packingWidth).Half u)
      (ShrinkRole.MapWitness.placedOld B i X sel v x) q.2.symm)
    (halfOrder : ∀ (u : X.network.Site) (z : X.network.Half u), r.halfBits u z = packed X u z)
    (before : DFS.Scratch w endAddr) (priv : Word w → Word w)
    (fit : ∀ packet ∈ r.childPackets J.nodes v x, packet.Fits J.arena w endAddr)
    (nd : ((r.childPackets J.nodes v x).map Packet.node).Nodup)
    (written : DFS.scratch endAddr priv =
      writePackets J.arena (r.childPackets J.nodes v x) before) :
    J.ChildWords priv endAddr := by
  rcases q with ⟨⟨motif, party⟩, place⟩
  change X.packingData.shrinkPartySite l motif party = v at place
  subst v
  intro site eqn u hu
  let actual := X.packingInputIso.site u
  have atChild : X.packingData.shrinkPartySite l motif party =
      (selectedTerm B f hf i X sel).place actual := by
    change _ = packedSiteEquiv ((X.packingData.placement l) (X.packingInputIso.site.symm
      (X.packingInputIso.site u)))
    rw [Equiv.symm_apply_apply, ← hu, eqn]
  let packet := Packet.mk (J.nodes actual) (packed X actual (x actual atChild))
  have present : packet ∈ r.childPackets J.nodes _ x := by
    let ord := (r.order.children (X.packingData.shrinkPartySite l motif party)).entries
    obtain ⟨j, hj⟩ := ord.surjective ⟨actual, atChild⟩
    apply List.mem_ofFn.mpr
    refine ⟨j, ?_⟩
    change Packet.mk (J.nodes (ord j).val) (r.halfBits (ord j).val (x (ord j).val (ord j).prop))
      = packet
    rw [hj, halfOrder]
  have stored := written ▸ writePackets_children J.arena _ before fit nd packet present
  change (Packet.mk _ (packed X _ ((X.packingHalfEquiv u).symm
    (J.old u _)))).Fits _ _ _ ∧ (Packet.mk _ (packed X _ ((X.packingHalfEquiv u).symm
      (J.old u _)))).Stored _ _
  rw [oldEq]
  change (Packet.mk _ (packed X _ ((X.packingHalfEquiv u).symm
    (X.packingHalfEquiv u (x actual atChild))))).Fits _ _ _ ∧
    (Packet.mk _ (packed X _ ((X.packingHalfEquiv u).symm
      (X.packingHalfEquiv u (x actual atChild))))).Stored _ _
  rw [Equiv.symm_apply_apply]
  exact ⟨fit packet present, stored⟩

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
