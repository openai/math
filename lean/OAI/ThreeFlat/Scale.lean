import OAI.Geometry.HyperbolicGroups.MetricHexagon
import OAI.LinearAlgebra.SpectralBooks.PriceBlowup

namespace OAI
namespace ThreeFlat

open Filter HyperbolicObstruction LinearAlgebra.SpectralBooks
open scoped Topology

/-- Multiplication of all distances by a positive scalar preserves spectral prices. -/
noncomputable def scaledSpectralPrices {F X : Type*} [Field F] [MetricSpace X]
    (P : SpectralPlacementPrices F X) (o : X) (r : ℝ) (hr : 0 < r) :
    SpectralPlacementPrices F (MetricScale.Space r hr X) :=
  P.blowup (pure ()) (fun _ => r⁻¹) (fun _ => inv_pos.mpr hr)
    (fun _ x => x.val) ⟨o⟩ fun x y => by
      simpa only [MetricScale.dist_eq, div_inv_eq_mul, mul_comm (dist x.val y.val) r] using
        (tendsto_const_nhds (x := r * dist x.val y.val) :
          Tendsto _ ((pure () : Ultrafilter Unit) : Filter Unit) (𝓝 _))

end ThreeFlat

end OAI
