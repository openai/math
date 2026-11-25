import OAI.Hierarchy.ProbeSiteAddress
import OAI.Hierarchy.ProbeCoreReserve
import OAI.Hierarchy.TaggedPruning

namespace OAI
/-! # Open port locations on the numbered physical board -/

noncomputable section
namespace Hierarchy.ProbeStage.CoreBoard
open AdaptiveProbe TaggedPrune Tagged Catalyst
open scoped Classical

variable {h d k w K : ℕ} {b : Fin k → ℕ}

/-- Tags are checked at the source row's origin; payload ends attach to the
two exterior fabric columns and catalyst ends to their public reserve column. -/
def outerPort (place : Site h d k → Fin K) (column : Wire b → Columns h d) :
    OpenPins h w b → Fin K
  | .inr (v,side) => place (column v,some (v.1,side))
  | .inl i => match (portIndex h w).symm i with
    | .inl (a,_) => place (.inl a,none)
    | .inr (.inl (a,_)) => place (.inl a,none)
    | .inr (.inr (a,_)) => place (.inr (.inr a),none)

def outerLayout (place : Site h d k → Fin (K+1)) (column : Wire b → Columns h d)
    (layer : Fin (K+1) → CorrectionFrame.Location k) (sites : ∀ c l,layer (place (c,l))=l) :
    Layout h w b where
  last := K
  layer := layer
  port := outerPort place column
  located i := by
    rcases i with i|⟨v,s⟩
    · rcases word : (portIndex h w).symm i with ⟨a,j⟩ | (⟨a,j⟩ | ⟨a,j⟩) <;>
        simp only [outerPort,word,CorrectionFrame.location,sites]
    · exact sites _ _

def boardLayout (h d k w R : ℕ) :
    Layout h w (fun _ : Fin k=>Fintype.card (Columns h d)*R) :=
  outerLayout (siteNumber h d k) (fun v=>(reserveLocation h d k R v).1)
    (fun i=>((siteNumber h d k).symm i).2) (fun c l=>by simp)

@[simp] theorem boardLayer (h d k w R : ℕ) (c : Columns h d) (l : ColumnLayer k) :
    (boardLayout h d k w R).layer (siteNumber h d k (c,l))=l := by
  simp [boardLayout,outerLayout]

end Hierarchy.ProbeStage.CoreBoard

end
end OAI
