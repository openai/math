import OAI.ThreeFlat.Diagonal.ShrinkChildAssemblyOrder
import OAI.ThreeFlat.Diagonal.NavigationNodeArchive

namespace OAI
/-! # The width-generic physical shrink and refresh word-visit cases -/

namespace ThreeFlat.Diagonal.NavigationPass
open Computability.VPVNP.BurstRAM RAM RAM.NavigationNodeRows RAM.PhysicalProcedure PhysicalStage
open CompressorPacking Native NavigationDirectory HistoryContraction
open scoped Classical BigOperators
noncomputable section
variable {F : Type} [Field F]

def RecordedWordStep {W : ℕ} (K : ℕ) (cur ctr : Word W) (headerEnd heapEnd : ℕ)
    (final : Memory W) (Pins : Type) (allow : StaticMotif F→Prop) : Run.WordVisit F Pins :=
  fun R i L w O charge row=>ShrinkWordVisit K cur ctr headerEnd heapEnd final allow R i L w O charge row ∨
    RefreshWordVisit K cur ctr headerEnd heapEnd final allow R i L w O charge row

theorem RecordedWordStep.transfer {W K headerEnd heapEnd : ℕ} {cur ctr : Word W} {final out : Memory W}
    (same : ∀ x,x<heapEnd→ out x=final x) {Pins : Type} {allow : StaticMotif F→Prop} {d l D m : ℕ} {A : State d l}
    (R : Move F A D m) (b : Fin R.rules.count) (L : A.Words Pins) (w : R.WordStep Pins L b)
    (O : A.ArchiveSites) (charge : (R.next b).Site→ℕ) (row : R.ArchiveStep b O charge) :
    RecordedWordStep K cur ctr headerEnd heapEnd final Pins allow R b L w O charge row →
      RecordedWordStep K cur ctr headerEnd heapEnd out Pins allow R b L w O charge row :=
  Or.imp (fun s=>s.transfer same) (fun r=>r.transfer same)


end
end ThreeFlat.Diagonal.NavigationPass

end OAI
