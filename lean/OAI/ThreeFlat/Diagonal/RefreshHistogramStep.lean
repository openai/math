import OAI.ThreeFlat.Diagonal.RefreshSlotRewrite
import OAI.ThreeFlat.Diagonal.RefreshConnectedSupply
import OAI.ThreeFlat.Diagonal.FixedMotifTile
import OAI.ThreeFlat.Diagonal.HistogramPortKernel

namespace OAI
/-! # Histogram-indexed history rewrite with one external bundle per refresh port -/

namespace ThreeFlat.Diagonal.RefreshTies

open Computability.VPVNP.Compression LinearAlgebra.SpectralBooks HistoryContraction Expander
open MotifOuterTerms
open private sum_congr_instances from OAI.ThreeFlat.Diagonal.RefreshKernel
open scoped Classical BigOperators
noncomputable section

variable {V C L F : Type} [Fintype V] [Fintype L] [AddCommGroup C] [AddCommGroup L] [Field F]
variable {m h : ℕ} (G : LiftedSlots V m (C × L)) (port : Fin m ≃ C) (c : Fin m → Fin m → ℕ)

abbrev profile (w : Address (V × L) m → ℕ) (u : V × L) (e : Bool × Fin m × Fin m) :=
  w (addr (arrival G port) u e)

variable (w : Address (V × L) m → ℕ) (base : V × L → (Bool × Fin m × Fin m) → ℕ)
  (r : V × L → ℕ)
  (T : ∀ u : V × L, FixedMotifTile (RefreshMotif.denseGraph m) (RefreshTies.ports c) (base u) F)
  (fits : ∀ u e, profile G port w u e ≤ base u e * r u)

abbrev Histories := ∀ u : V × L, Histogram (T u).Alphabet (r u)

def sparseWidth (x : Histories c base r T) (u : V × L) (e : Arc c) :=
  histWidth (T u).output (x u) e + r u * (T u).bits

/-- Each physical history term stores only one canonical histogram per block.
The actual sparse selector travels on the internal wires, and the dense tie
identity preserves just one shared external bundle at each output port. -/
def histogramStep (hm : 2 ≤ m) (hh : 0 < h) (pad : ℕ)
    (sym : ∀ x y, c x y = c y x) (rows : ∀ x, ∑ y, c x y = h) (zero : ∀ x, c x x = 0)
    {γ : ℝ} (bound : Bound (transition c h) ℝ γ) :
    Rewrite (oldShape (arrival G port) (fun a => Fin (2^w a))) F := by
  letI : Nonempty (Fin m) := ⟨⟨0,by omega⟩⟩
  let S := DoublePorts.connectedSupply c hh rows sym bound
  let H := fun u : V × L => Histogram (T u).Alphabet (r u)
  let B := fun (u : V × L) (z : H u) (e : Arc c) =>
    (Fin (r u) → Fin (2^(T u).bits)) × Fin (2^histWidth (T u).output z e)
  let s := fun (u : V × L) (z : H u) (e : Arc c) => histWidth (T u).output z e+r u*(T u).bits
  let M := fun u => histogramKernel (RefreshMotif.denseGraph m) S (profile G port w u) (base u)
    (fits u) (T u).output (T u).encode (T u).entry
  exact slotRewrite G port c hm pad sym rows zero w H B s
    (fun u z e => SlotRefinement.selectorWord (r u) (T u).bits (histWidth (T u).output z e)) M
    (by
      intro u x
      refine (histogram_port_kernel (RefreshMotif.denseGraph m) S (profile G port w u) (base u)
        (fits u) (T u).output (T u).encode (T u).entry (T u).identity x).trans ?_
      apply sum_congr_instances
      intro z
      unfold PortGraph.contraction
      apply sum_congr_instances
      intro a
      rfl)

end
end ThreeFlat.Diagonal.RefreshTies

end OAI
