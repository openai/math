import OAI.ThreeFlat.Diagonal.CompressorStageAddress
import OAI.ThreeFlat.Diagonal.HistoryRelabel
import OAI.ThreeFlat.Diagonal.ShrinkOwnerKernel
import OAI.ThreeFlat.Diagonal.RefreshWireShapes
import OAI.ThreeFlat.Diagonal.SlotRefinement

namespace OAI
/-! # Isomorphisms from physical lifted slots to the input of either stage

A choice-dependent previous history may group its site coordinates in
either of two orders. A single equivalence from the physical base/lane
pair to that site's chart handles both, independently of edge labels.
-/

namespace ThreeFlat.Diagonal.CompressorPacking.StageAddress
open Computability.VPVNP.Compression LinearAlgebra.SpectralBooks HistoryContraction
noncomputable section
variable {V X S H Tag L : Type} {d c : ℕ}
variable [Fintype V] [Fintype X] [Fintype S] [Fintype H] [Fintype Tag] [Fintype L]
variable [AddCommGroup X] [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]

def portGraph (G : LiftedSlots V d X) (chart : V × X ≃ S) : PortGraph S ((V × Fin d) × X) :=
  ⟨fun e => chart (site e),fun e => chart (site (G.actualTarget e))⟩

def shape (G : LiftedSlots V d X) (chart : V × X ≃ S) (width : (V × Fin d) × X → ℕ) : Shape :=
  SlotRefinement.shape (portGraph G chart) (fun e => Fin (2^(width e)))

def shrinkInputIso (G : LiftedSlots V d X) (chart : V × X ≃ S) (u : X ≃+ BitWord c × H × Tag × L)
    (P : PackingData V H Tag L d c) (agree : packedGraph P = changeLanes G u)
    (width : (V × Fin d) × X → ℕ) :
    HistoryRelabel.Iso (shape G chart width) (oldShape P (width ∘ (splitEdge u).symm)) where
  site := chart.symm.trans (splitSite u)
  edge := splitEdge u
  label e := finCongr (by
    change (V × Fin d) × X at e
    exact congrArg (fun z => 2^(width z)) ((splitEdge u).symm_apply_apply e).symm)
  vertex e b := by
    change (V × Fin d) × X at e
    cases b with
    | false =>
      change sourcePosition (splitEdge u e) = splitSite u (chart.symm (chart (site e)))
      rw [chart.symm_apply_apply,split_source]
    | true =>
      change sourcePosition (P.actual (splitEdge u e)) =
        splitSite u (chart.symm (chart (site (G.actualTarget e))))
      rw [chart.symm_apply_apply,split_target G u P agree]

def refreshInputIso (G : LiftedSlots V d X) (chart : V × X ≃ S) (u : X ≃+ H × L)
    (port : Fin d ≃ H) (width : (V × Fin d) × X → ℕ) :
    HistoryRelabel.Iso (shape G chart width)
      (RefreshTies.oldShape (RefreshTies.arrival (changeLanes G u) port)
        (fun e => Fin (2^(width ((refreshEdge u port).symm e))))) where
  site := chart.symm.trans (refreshSite u port)
  edge := refreshEdge u port
  label e := finCongr (by
    change (V × Fin d) × X at e
    exact congrArg (fun z => 2^(width z)) ((refreshEdge u port).symm_apply_apply e).symm)
  vertex e b := by
    change (V × Fin d) × X at e
    cases b with
    | false =>
      change refreshVertex (refreshEdge u port e) = refreshSite u port (chart.symm (chart (site e)))
      rw [chart.symm_apply_apply,refresh_source]
    | true =>
      change refreshVertex (RefreshTies.arrival (changeLanes G u) port (refreshEdge u port e)) =
        refreshSite u port (chart.symm (chart (site (G.actualTarget e))))
      rw [chart.symm_apply_apply,refresh_target]

end
end ThreeFlat.Diagonal.CompressorPacking.StageAddress

end OAI
