import OAI.Hierarchy.TaggedWireSpillMatrix

namespace OAI
/-! # The actual mixed-radix input of a carried spill -/
noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard.LedgerStep
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open AdaptiveProbe WireTelescope
open scoped Classical BigOperators
variable {F : Type*} [Field F] {K : ℕ} {J : Type} [Fintype J]
variable (G : PortGraph (Fin K) J) (pass : Widths K) (old active held kept spill : J→ℕ)
    (balanced : ∀i,old i+active i=held i+kept i+spill i)

theorem feedShape (balanced : ∀i,old i+active i=held i+kept i+spill i) : (pass+G.chordWidths held+G.chordWidths kept)+G.chordWidths spill=pass+G.chordWidths old+G.chordWidths active := by
  simpa only [add_assoc] using congrArg (pass+·) (held_split G old active held kept spill balanced).symm

def repartition (s : Fin K) (x : State (pass+G.chordWidths old+G.chordWidths active) s) : State ((pass+G.chordWidths held+G.chordWidths kept)+G.chordWidths spill) s :=
  cast (congrArg (fun q=>State q s) (feedShape G pass old active held kept spill balanced).symm) x

omit [Field F] in
private theorem apply_rebase {A B U : Widths K} (head : A=B) (M : SiteMatrix (State A) (State U) F)
    (s : Fin K) (x : State B s) (y : State U s) :
    rebase head rfl M s x y=M s (cast (congrArg (fun w=>State w s) head.symm) x) y := by
  cases head
  rfl

theorem matrix_repartition {U : Widths K} (M : SiteMatrix (State (G.chordWidths spill)) (State U) F)
    (s : Fin K) (x : State (pass+G.chordWidths old+G.chordWidths active) s) (y : State ((pass+G.chordWidths held+G.chordWidths kept)+U) s) :
    matrix G pass old active held kept spill balanced M s x y =
      carry M (pass+G.chordWidths held+G.chordWidths kept) s (repartition G pass old active held kept spill balanced s x) y :=
  apply_rebase (feedShape G pass old active held kept spill balanced) _ _ _ _

end Hierarchy.ProbeStage.CoreBoard.LedgerStep
end

end OAI
