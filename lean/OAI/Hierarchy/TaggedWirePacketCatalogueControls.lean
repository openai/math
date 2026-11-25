import OAI.Hierarchy.TaggedWidePacketMenuControls
import OAI.Hierarchy.TaggedWireStripPacketReads

namespace OAI
/-! # Both actual strip ballots publish native install and low-carry columns -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open LinearAlgebra.SpectralBooks ChordGraph AdaptiveProbe Strip
open WireTelescope StripPaths ChosenPackets.RowRouting
open scoped Classical
variable {S : ProbeStage.PurchaseSampler} {h d k n D : ℕ} {A B : Type} [Fintype A] [Fintype B]
local notation "C" => TreeColumn n
local notation "X" => TreeSite n k
local notation "R" => ColumnWires.Role C (Fin n) (A⊕B) k
local notation "T" => TreeLink n k
def StripPorts.catalogueControls (p : StripPorts S h d k C (Fin n) B) (extra : A⊕B→DistinctPair X)
    (b : Board) (shift : ℕ) (site : X→Expr) (stock : A→Expr) (qty : R⊕T→Expr)
    (M originalRows start shelfSize bits : ℕ) (siteBase : Bank) (participant : X) :
    Fin ((M*3)*5+D)→Expr :=
  let enum:=treeFirst R T
  let order:=(Fintype.equivFin ((i : Fin (Fintype.card (R⊕T))) × Fin (menuLen (enum i)))).symm
  menuControls extra enum order site (readPrimary stock shift (p.primary b)) (emitterMate (A:=A) p b shift)
    (emitterTree (A:=A) p b shift) qty M originalRows start shelfSize bits siteBase (site participant)
end Hierarchy.ProtocolRAM.Calendar.CatalogueRows

end
end OAI
