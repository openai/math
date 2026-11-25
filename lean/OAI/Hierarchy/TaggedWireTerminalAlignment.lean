import OAI.Hierarchy.TaggedWireTerminalPorts
import OAI.Hierarchy.ProtocolRAMCatalogueAlignment

namespace OAI
/-! # Original chronological rows determine the old-state half-bit locations -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.HistoryRoles.Terminal
open ProtocolRAM Calendar AdaptiveProbe ReportSockets WireTelescope
open LinearAlgebra.SpectralBooks ChordGraph
open ProtocolRAMEmit
open scoped Classical

variable {h W k attempts M den w R : ℕ} {board : CatalogueRows.Board} {S : PurchaseSampler}
    {π : Equiv.Perm (Fin (2^h))} {depth : ℕ} {marked : Marks h W k attempts}
    (unique : Exclusive marked) (B : Mount (S:=S) π (name (W:=W) (k:=k)) board.rows)
    (pad : Chord (siteLast h (2^W) k+1))
    {fixed : Fin board.rows→ℕ} {stock : Goods h W k→ℕ} {reserved used : Catalysts h W k→ℕ}
    {rows : Fin board.rows→ProtocolRAMEmit.Row} {G : Geometry (boardLayout h (2^W) k w R) M den rows}
    (H : MatrixReceipt B fixed stock reserved used G) {original : Catalogue S π depth marked→Fin board.rows}
    (A : CatalogueRows.Alignment board S π depth marked M rows fixed original)

include H in
theorem aligned_chords (i : {j // 0<fixed j}) :
    filledChord B.actual pad i.val=sorted S π depth marked (.inl (A.ident i)) :=
  positions_of_reported S π depth marked B pad fixed stock reserved used A.ident H A.joins i

include H in
theorem aligned_site (p : NamedAperture.LiveEnd (SettledMatrix.Layout.bits fixed stock reserved used)) :
    name (site S (ports S π depth marked unique fixed stock reserved used A.ident p))=
      (portGraph _).vertex ((B.matrixLayout (siteNumber h (2^W) k).injective pad).family p.val.1) p.val.2 :=
  native_site S π depth marked unique B pad fixed stock reserved used A.ident p (aligned_chords B pad H A)

end Hierarchy.ProbeStage.CoreBoard.HistoryRoles.Terminal

end
end OAI
