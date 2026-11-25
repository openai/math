import OAI.Hierarchy.ProbeFixedWidePartyCircuit
import OAI.Hierarchy.TaggedWireEarnedTender
import OAI.Hierarchy.ProbeSelectedPacketWidths

namespace OAI
/-! # Local signed packet chords in the original tree-first physical installation -/
noncomputable section
namespace Hierarchy.WireTelescope.PassMatrix.PartyPins
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.Diagonal.MotifOuterTerms
open Probe AdaptiveProbe Strip ChosenPackets ChosenPackets.RowRouting
open ProtocolRAM Calendar StockCommit
open scoped Classical

variable {F E A Ball : Type} [Field F] [Fintype E] [Fintype A] [Fintype Ball]
    {n k N S : ℕ} (name : TreeSite n k≃Fin (Fintype.card (TreeSite n k)))
    (roles : E→DistinctPair (TreeSite n k)) (req : A→E) (place : Ball×TreeSite n k↪Fin S)
    (u : Ball) (rt : Fin (Fintype.card (TreeSite n k)))
variable (P : Packet F (fun e=>@DistinctPair.chord _ _ ⟨name⟩ (roles e)) req) (copies : ℕ) (phys : Fin N→Chord S)
    (g : Installs (Sum.elim (reportedRole place roles u) (reportedRole place (treeEnds n k) u)) phys)
    {r : ℕ} (ord : Fin r≃Σi,Fin ((g.steps (treeFirst E (TreeLink n k))) i).length)
local notation "R" => stripTender name roles req place u rt P copies phys g ord
local notation "chosen" => stripPacket name roles req place u rt P

theorem strip_aligned (z : Fin (Fintype.card (E⊕TreeLink n k))) :
    Installs.starts (source:=(R).source) (R).order z=physicalChord (chosen).place
      (localRows name (fun e=>@DistinctPair.chord _ _ ⟨name⟩ (roles e)) z) := by
  change Sum.elim (reportedRole place roles u) (reportedRole place (treeEnds n k) u)
    (treeFirst E (TreeLink n k) z)=physicalChord (name.symm.toEmbedding.trans (ballEmbedding place u))
    (Sum.elim (fun e=>@DistinctPair.chord _ _ ⟨name⟩ (roles e))
      (fun j=>@DistinctPair.chord _ _ ⟨name⟩ (treeEnds n k j)) (treeFirst E (TreeLink n k) z))
  cases treeFirst E (TreeLink n k) z with
  | inl e => exact (physicalChord_role name (ballEmbedding place u) (roles e)).symm
  | inr f => exact (physicalChord_role name (ballEmbedding place u) (treeEnds n k f)).symm

omit [Fintype Ball] in
theorem strip_native [Nonempty (Fin (Fintype.card (TreeSite n k)))] {W spare d rows : ℕ}
    {b : Batch (P.terms+spare) d} {st : StockCommit} {mem : Computability.VPVNP.BurstRAM.Memory W}
    {layout : PortPlan st b mem rows} {j : Fin rows} (nr : NativePacketRow P spare b layout j) :
    chosen=nr.placed (name.symm.toEmbedding.trans (ballEmbedding place u)) rt (treeGraph name) (tree_connected name) := rfl

end Hierarchy.WireTelescope.PassMatrix.PartyPins

end
end OAI
