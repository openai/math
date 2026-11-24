import OAI.Computability.VPVNP.PackedShrinkStep
import OAI.Computability.VPVNP.ShrinkLayout

/-!
# Exact contraction of the shrinking step

For any list of admissible six-party terms, one common layout minimizes
surviving energy. This determines the placement of every old factor and the
regular lift carrying the surviving payloads. Equation (7.1) sums the placed
kernels on these lifts, with one shared value on each new wire.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.PackingData

open NetworkKernel WireTensor MotifGrid MotifBlocks MotifConversion MotifSelector
open ShrinkMotif ShrinkEnergy

variable {V H Tag L : Type} {d c d' pad : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
variable (P : PackingData V H Tag L d c)
variable {k : Type*} [Field k] {H' δ : ℝ} (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) H')
variable {R : Type*} [CommRing R] (κ : (parameterData B).Entry → R)
variable (hκ : (parameterData B).IsSolution κ) (hc : 2 ≤ c) (hd : 0 < d)
variable (number : P.BundleNumbering) (order : P.ThickNumbering) (w : Arc V H Tag L d c → ℕ)
variable (ready : Ready d c d' δ) {next : Equiv.Perm (V × Tag)}
variable (I : ∀ l : Bool, P.ShrinkIndex l (subdivisions d c d') next d' pad)

/-- Select one layout for all motifs using their aggregate supply energies. -/
noncomputable def shrinkTermLayout (s : ∀ m, P.ShrinkChoice number w B m) : Bool :=
  chosenLayout (equalArcMass (Position V H Tag L c) d) (fun t ↦ (relativeMass t : ℝ))
    (P.termWidths B number w s)

/-- The complete shrinking kernel, with the actual six-party identities,
padded output arcs, and local contractions of absorbed wire values. -/
noncomputable def shrinkStep : Step R (P.oldWireNetwork w) := by
  let C := P.ShrinkChoice number w B
  let W (m : P.Motif) (i : C m) := P.shrinkSupplyWidths number w B m i
  let X (m : P.Motif) (i : C m) := (e : Bool × Fin 4) → Word (W m i e)
  let l (s : ∀ m, C m) := P.shrinkTermLayout B number w s
  let T (s : ∀ m, C m) := P.shrinkLayout hc hd number order w (l s) (subdivisions d c d')
    (fun m ↦ W m (s m)) (I (l s)) ready.count_pos (fun m ↦ P.shrinkMap number w B κ m (s m))
  refine Step.ofMotifProduct C X (P.demandCoeff hc hd number order w)
    (fun m i z a ↦ ∏ j, P.shrinkMap number w B κ m i j
      (P.shrinkDemandArg hc hd number order w m a j) (edgeAssignment supply.src supply.dst z j))
    (P.oldWireNetwork_coeff hc hd number order w)
    (P.shrinkDemand_identity hc hd number order w B κ hκ)
    T (fun s ↦ P.shrinkAssignmentsEquiv (l s) (subdivisions d c d')
      (fun m ↦ W m (s m)) (I (l s)) ready.count_pos) ?_
  exact fun s x a ↦ P.shrinkLayout_group hc hd number order w (l s) (subdivisions d c d')
    (fun m ↦ W m (s m)) (I (l s)) ready.count_pos (fun m ↦ P.shrinkMap number w B κ m (s m)) x a

/-- The lift and widths passed to the next substep. -/
theorem shrinkStep_output (s : ∀ m, P.ShrinkChoice number w B m) :
    let l := P.shrinkTermLayout B number w s
    ((P.shrinkStep B κ hκ hc hd number order w ready I).term s).output =
      P.shrinkOutput l (subdivisions d c d') (fun m t ↦ P.termWidths B number w s m l t)
        (I l) := rfl

/-- A selected term moves each complete old position once. -/
theorem shrinkStep_place (s : ∀ m, P.ShrinkChoice number w B m) :
    ((P.shrinkStep B κ hκ hc hd number order w ready I).term s).place =
      P.shrinkPlace (P.shrinkTermLayout B number w s) := rfl

end Compression.PackingData

end VPVNP
end Computability
end OAI
