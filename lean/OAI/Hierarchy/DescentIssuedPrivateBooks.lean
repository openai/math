import OAI.Hierarchy.DescentIssuedCommonChart
import OAI.Hierarchy.DescentReachedOrdinaryBook

namespace OAI
/-! # Live private occurrences in the two genuine contractions of an issued ordinary step -/
namespace Hierarchy.DescentStageEdgeReceipt
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.StarKeys DescentKernelHistory DescentBundleHistory
open DescentHostDirectory DescentHostDegree
open scoped Classical
noncomputable section
variable {F P H : Type} [Field F] [Fintype H] [DecidableEq H] {d p R : ℕ} {bits : P→ℕ}
variable {W : MarkedWorld F d P bits} {G : PoweredGadget F} {u ε : ℝ}
variable {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice} {old : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)}
  {root : H↪ℕ} {U : MarkedWorld F d P bits} {n : Normalize U} {t : Tape n.result.graph.Edge} {pair : ScanNumbers he T}
local notation "sel" => scanWorld he T c
variable (hp : 0<p) {B : BitDescription (scanWorld he T c)} (before : WorldShape p R B) (unit : p∣T.z)

theorem IssuedRows.private_books (issued : IssuedRows he T c old root U n t pair) (state : U=sel)
    (cut : Normalize.CutsEqual T.z n) :
    ∃ (b : IssuedDonorChart he T H) (books : SiteBooks hp
      (WorldShape.follow hp T.unitPos unit n cut (before.transport state.symm)) (before.coalesced (b.key he T c) b.hub T.k (gainExponent 20 T.Δ))),
      ∀x : (rawGraph he T c).Site,books.home (n.destination (rawInput he T c state x))=
        MarkedWorld.address sel (b.key he T c) b.hub T.k (gainExponent 20 T.Δ)
          (GadgetNetwork.newSite W.graph (BitDescription.scannedRows he T).pick
            (bestLayout (branchWidth G (fun _ : (BitDescription.scannedRows he T).pairs => T.z) ((BitDescription.scannedRows he T).profile c)))
            (BitDescription.scannedRows he T).pack x) := by
  obtain ⟨b,_,all⟩:=issued.common_chart he T c state
  obtain ⟨book,home,_⟩:=all hp before unit cut
  exact ⟨b,book,home⟩
end
end Hierarchy.DescentStageEdgeReceipt

end OAI
