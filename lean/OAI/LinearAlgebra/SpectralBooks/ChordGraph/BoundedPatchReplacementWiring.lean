import OAI.LinearAlgebra.SpectralBooks.ChordGraph.ChordWiring
import OAI.LinearAlgebra.SpectralBooks.PortWiring

/-! # The coordinate wiring of an integer-width polygon graph -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

open OAI.MatrixMultiplication

open scoped Classical BigOperators
noncomputable section

namespace ChordGraph

open SiteTensor

variable {k : ℕ}

/-- A bundle of parallel wires is one chord. Unused chords have singleton alphabet. -/
def portGraph (k : ℕ) : PortGraph (Fin k) (Chord k) := ⟨fun e => e.1.1, fun e => e.1.2⟩

abbrev Index (g : Widths k) (e : Chord k) := Fin (2 ^ g e)

abbrev State (g : Widths k) (i : Fin k) := (portGraph k).State (Index g) i

/-- Equality of the two copies of every chord index in the independent vertex states. -/
def raw (F : Type*) [Field F] (g : Widths k) : Raw.{0} (Fin k) F :=
  ⟨State g, fun _ => inferInstance, (portGraph k).wiring (Index g)⟩

theorem sum_port_width (g : Widths k) (i : Fin k) :
    ∑ p : (portGraph k).Port i, g p.1.1 = load i g := by
  induction g using Finsupp.induction_linear with
  | zero => simp
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, Finset.sum_add_distrib, hx,hy]
  | single e m =>
    rw [load_single]
    rw [← Finset.sum_subtype (Finset.univ.filter (fun p : Chord k × Bool => (portGraph k).vertex p.1 p.2 = i)) (by simp) (fun p => Finsupp.single e m p.1)]
    rw [Finset.sum_filter]
    rw [Fintype.sum_prod_type]
    classical
    simp only [Fintype.sum_bool]
    rw [Finset.sum_eq_single e]
    · simp only [Finsupp.single_eq_same, PortGraph.vertex, portGraph, add_mul, ite_mul, one_mul,
        zero_mul]
      simp only [@eq_comm _ i, add_comm]
    · intro f _ h
      simp [Finsupp.single_eq_of_ne h]
    · simp

theorem card_state (g : Widths k) (i : Fin k) : Fintype.card (State g i) = 2^(load i g) := by
  rw [← sum_port_width]
  simp [State, PortGraph.State, Index, Fintype.card_pi, Finset.prod_pow_eq_pow_sum]

end ChordGraph

end

end SpectralBooks
end LinearAlgebra
end OAI
