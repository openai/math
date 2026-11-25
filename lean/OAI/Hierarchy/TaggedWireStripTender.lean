import OAI.Hierarchy.TaggedWireRoutedPackets
import OAI.Hierarchy.TaggedWirePacketRoleOrder

namespace OAI
/-! # Install the actual signed strip with native selector words in the low positions -/

noncomputable section
namespace Hierarchy.WireTelescope.ChosenPackets.RowRouting
open LinearAlgebra.SpectralBooks ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open AdaptiveProbe Strip Probe
open scoped BigOperators Classical
variable {F E A Ball : Type} [Field F] [Fintype E] [Fintype A] [Fintype Ball]
    {n k N S : ℕ} (name : TreeSite n k≃Fin (Fintype.card (TreeSite n k)))
    (roles : E→DistinctPair (TreeSite n k)) (req : A→E) (place : Ball×TreeSite n k↪Fin S)
    (u : Ball) (rt : Fin (Fintype.card (TreeSite n k)))
variable (P : Packet F (fun e=>@DistinctPair.chord _ _ ⟨name⟩ (roles e)) req)

def stripPacket : Placed F S where
  sites:=Fintype.card (TreeSite n k)
  nonemptySites:=⟨rt⟩
  Edges:=E
  Requests:=A
  Tree:=TreeLink n k
  edge:=fun e=>@DistinctPair.chord _ _ ⟨name⟩ (roles e)
  wanted:=req
  data:=P
  place:=name.symm.toEmbedding.trans (ballEmbedding place u)
  root:=rt
  graph:=treeGraph name
  connected:=tree_connected name

local notation "Q" => stripPacket name roles req place u rt P

omit [Fintype Ball] in
theorem strip_output (copies : ℕ) (t : Histogram (Fin P.terms) copies) :
    (Row.packet Q copies).output t=optionWidths (reportedRole place roles u) (histWidth P.count t)+
      optionWidths (reportedRole place (treeEnds n k) u) (fun _=>copies*P.selectorBits) := by
  have sites : (fun e=>physicalChord (name.symm.toEmbedding.trans (ballEmbedding place u))
      (@DistinctPair.chord _ _ ⟨name⟩ (roles e)))=reportedRole place roles u := by
    funext e
    exact physicalChord_role name (ballEmbedding place u) (roles e)
  exact congrArg₂ (·+·) (congrArg (fun f=>optionWidths f (histWidth P.count t)) sites)
    (placed_tree place u name (copies*P.selectorBits))

def stripTender (copies : ℕ) (phys : Fin N→Chord S)
    (installed : Installs (Sum.elim (reportedRole place roles u) (reportedRole place (treeEnds n k) u)) phys)
    {r : ℕ} (ordinal : Fin r≃Σi,Fin ((installed.steps (treeFirst E (TreeLink n k))) i).length) :
    RowRouting (Row.packet Q copies) phys :=
  of_strip roles place u (histWidth P.count) (copies*P.selectorBits)
    (strip_output name roles req place u rt P copies) installed (treeFirst E (TreeLink n k)) ordinal

theorem bits_ordered (copies : ℕ) (phys : Fin N→Chord S)
    (installed : Installs (Sum.elim (reportedRole place roles u) (reportedRole place (treeEnds n k) u)) phys)
    {r : ℕ} (ordinal : Fin r≃Σi,Fin ((installed.steps (treeFirst E (TreeLink n k))) i).length)
    (t : Histogram (Fin P.terms) copies) (i : Fin (Fintype.card (E⊕TreeLink n k))) :
    let tender:=stripTender name roles req place u rt P copies phys installed ordinal
    tender.bits t (tender.order i)=
      Sum.elim (histWidth P.count t) (fun _=>copies*P.selectorBits) (treeFirst E (TreeLink n k) i) := rfl

end Hierarchy.WireTelescope.ChosenPackets.RowRouting

end
end OAI
