import OAI.Computability.MultitapeWeakETH.HistoryKernelSpec

/-! # Global exponents of the selected refresh reader -/

namespace OAI.Computability.MultitapeWeakETH.NativeGrid

open IntegerMultiplication Code VPVNP Compression Compression.Refresh Compression.DegreeRefresh
open CompressorRecords NetworkKernel PairSimulation LocalHistory PortRefresh RefreshMapOperands PortRefresh.TraversalPlan
open private fixedEmission from OAI.Computability.MultitapeWeakETH.HistoryKernelSpec
open scoped Classical Fin.CommRing
noncomputable section

variable {k R : Type} [_root_.Field k] [CommRing R] {S : BlockSchedule k} {B : S.Templates}
    {hist g : ℕ} (order : B.Entry ≃ Fin hist) (f : B.Entry → R) (hf : B.IsSolution f)

local notation "hE" => Nat.two_pow_pos S.expanderExponent
local notation "hC" => And.left (S.port_bound.connected_and_pos S.port_order)

set_option maxRecDepth 8000 in
set_option maxHeartbeats 1800000 in
theorem refresh_kernel_spec (Z : State S.portExponent (S.portExponent+g))
    (choice : DyadicRefreshChoice (a₀:=S.degreeExponent 0) (g:=g) Z S.graph hE hC B.refresh)
    (port : (Z.Base × BitWord g) × Fin (2^S.portExponent))
    (old : Placed (TraversalPlan.place (S:=S) Z) Z.network.Half (promotedSites port))
    (new : (dyadicRefreshNext Z S.graph hE hC B.refresh S.port_order S.degree_bounds.2 choice).network.Half
      (promotedSites port)) (run : Option (List Tally))
    (checked : run = (TraversalPlan.emitted B order Z choice port (old _ (TraversalPlan.old_place (S:=S) Z port)) new).map (List.map (tally ∘ Fin.val))) :
    KernelSpec order ((originReader B f hf (PassOrigin.refresh Z) choice).read (promotedSites port) old new).encode
      ((originReader B f hf (PassOrigin.refresh Z) choice).witness (promotedSites port) old new).exponents
      (fun bits => run.bind fun labels => some (labels,bits)) := by
  subst run
  exact fixedEmission order _ _ _ (TraversalPlan.origin_emitted_iff B order Z choice port new old f hf)
    (TraversalPlan.origin_kernelBits B f hf Z choice port old new)
    (TraversalPlan.origin_emitted_count B order Z choice port new old f hf)

end
end OAI.Computability.MultitapeWeakETH.NativeGrid
