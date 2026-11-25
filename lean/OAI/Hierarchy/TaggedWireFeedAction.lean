import OAI.Hierarchy.TaggedWireSpillMatrix

namespace OAI
/-! # The tensor action of a balanced feed transfer -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.FeedTransfer
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe WireTelescope
open scoped Classical BigOperators
variable {h d k K edges r : ℕ} {F : Type*} [Field F]
abbrev Data h d k := Commodity (Fin (2^h)) (Stages h d) k

structure Transfer (h d k : ℕ) where
  old : Data h d k→ℕ
  active : Data h d k→ℕ
  held : Data h d k→ℕ
  kept : Data h d k→ℕ
  spill : Data h d k→ℕ
  balanced : ∀i,old i+active i=held i+kept i+spill i

variable {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))} {place : Site h d k→Fin K}
    (B : Mount (S:=S) π place edges) (inj : Function.Injective place) (pad : Chord K)
    (enum : Fin r≃RouteOccurrence B.ordinary (Empty.elim : Empty→List (Fin edges)))
    (carry : Widths K)

def input (T : Transfer h d k) := carry+(commodityGraph π place).chordWidths T.old+
  (commodityGraph π place).chordWidths T.active

def output (T : Transfer h d k) := carry+(commodityGraph π place).chordWidths T.held+
  (commodityGraph π place).chordWidths T.kept+B.actual.chordWidths (routeLoad B.ordinary T.spill)

def matrix (T : Transfer h d k) :
    SiteMatrix (State (input (π:=π) (place:=place) carry T)) (State (output B carry T)) F :=
  LedgerStep.matrix (commodityGraph π place) carry T.old T.active T.held T.kept T.spill T.balanced
    (B.onlySpill inj pad T.spill enum)

theorem action (T : Transfer h d k) (v : ∀s,State (input (π:=π) (place:=place) carry T) s) :
    (raw F _).coeff v=SiteMatrix.act (matrix B inj pad enum carry T) (raw F _).coeff v :=
  LedgerStep.action (commodityGraph π place) carry T.old T.active T.held T.kept T.spill T.balanced
    (B.onlySpill inj pad T.spill enum) (B.onlySpill_action inj pad T.spill enum) v

end Hierarchy.ProbeStage.CoreBoard.FeedTransfer

end
end OAI
