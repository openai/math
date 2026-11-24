import OAI.Computability.VPVNP.ShrinkStep
import OAI.Computability.VPVNP.ShrinkFieldBounds
import OAI.Computability.VPVNP.MotifEntryWitness

/-!
# Monomial witnesses of the shrinking kernels

For fixed old half-wires and new half-wires, a vertex first chooses each
absorbed word owned by it. It then performs the syntactic entry check of
every six-party map resident at that vertex. The successful choices retain
their parameter multiplicities in any coefficient ring.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.ShrinkMotif

open NetworkKernel

variable {M V Label : Type} [Fintype M] [DecidableEq V] [Fintype Label]
variable {R : Type*} [CommRing R] {κ : Label → R}

/-- At one packed site only the resident motif-party occurrences contribute
choices or labels to the product. -/
noncomputable def partyProductWitness (site : M → Fin 6 → V) (v : V)
    {factor : ∀ m j, v = site m j → R}
    (W : ∀ m j h, MonomialWitness κ (factor m j h)) :
    MonomialWitness κ (partyProduct site v factor) :=
  (MonomialWitness.prod (fun r : {p : M × Fin 6 // site p.1 p.2 = v} ↦
    W r.1.1 r.1.2 r.2.symm)).changeValue (partyProduct_eq_resident site v factor).symm

/-- The degree of one successful product is the sum of the individual
degrees at its resident map occurrences. -/
theorem partyProductWitness_totalExponent (site : M → Fin 6 → V) (v : V)
    {factor : ∀ m j, v = site m j → R}
    (W : ∀ m j h, MonomialWitness κ (factor m j h)) (c : (partyProductWitness site v W).Choice) :
    ∑ l, (partyProductWitness site v W).exponents c l =
      ∑ r : {p : M × Fin 6 // site p.1 p.2 = v}, ∑ l,
        (W r.1.1 r.1.2 r.2.symm).exponents (c r) l :=
  Finset.sum_comm

end Compression.ShrinkMotif

namespace Compression.PackingData

open NetworkKernel WireTensor MotifGrid MotifBlocks MotifConversion MotifDemandPadding ShrinkMotif

variable {V H Tag L : Type} {d c d' pad : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
variable (P : PackingData V H Tag L d c)
variable (hc : 2 ≤ c) (hd : 0 < d) (number : P.BundleNumbering) (order : P.ThickNumbering)
variable (w : Arc V H Tag L d c → ℕ) (l : Bool) (subdiv : Fin 4 → ℕ)
variable (width : P.Motif → Bool × Fin 4 → ℕ) {next : Equiv.Perm (V × Tag)}
variable {R : Type*} [CommRing R]

/-- Product of the individual map witnesses in one concrete shrinking
layout. All row and column arguments come from the site's own old fields,
absorbed words and outgoing-network half-wires. -/
noncomputable def shrinkLayoutEntryWitness
    (I : P.ShrinkIndex l subdiv next d' pad) (hpos : ∀ t, 0 < subdiv t)
    (matrix : ∀ m j, HalfBits demandSource demandTarget (P.shrinkDemandWidths number w m) j →
      HalfBits supply.src supply.dst (width m) j → R)
    {Label : Type} [Fintype Label] {κ : Label → R}
    (W : ∀ m j x y, MonomialWitness κ (matrix m j x y)) :
    let T := P.shrinkLayout hc hd number order w l subdiv width I hpos matrix
    ∀ v a h z, MonomialWitness κ (T.entry v a h z) :=
  fun v a h z ↦ partyProductWitness (P.shrinkPartySite l) v fun m j hv ↦
    W m j (P.shrinkLocalDemandArg hc hd number order w l m j (hv ▸ a))
      (P.shrinkLocalSupplyArg l subdiv width I hpos m j (hv ▸ h) (hv ▸ z))

variable {k : Type*} [Field k] {H' δ : ℝ}
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) H')
variable (κ : (parameterData B).Entry → R) (hκ : (parameterData B).IsSolution κ)
variable (ready : Ready d c d' δ)
variable (I : ∀ l : Bool, P.ShrinkIndex l (subdivisions d c d') next d' pad)

/-- Witness for the actual kernel selected in (7.2). The outer witness
selects the absorbed words, and the inner witnesses count one parameter
per accepted copy of each resident matrix. -/
noncomputable def shrinkKernelWitness :
    ∀ s v a z, MonomialWitness κ
      (((P.shrinkStep B κ hκ hc hd number order w ready I).term s).kernel v a z) :=
  fun s ↦
    let l := P.shrinkTermLayout B number w s
    let width := fun m ↦ P.shrinkSupplyWidths number w B m (s m)
    let matrix := fun m ↦ P.shrinkMap number w B κ m (s m)
    let T := P.shrinkLayout hc hd number order w l (subdivisions d c d')
      width (I l) ready.count_pos matrix
    T.kernelWitness (P.shrinkLayoutEntryWitness hc hd number order w l (subdivisions d c d')
      width (I l) ready.count_pos matrix fun m j x y ↦
        entryWitness κ (entry B demandMass_pos (P.shrinkDemandWidths number w m) (s m).val j x y))

/-- In a successful shrinking-kernel witness the degree is exactly the
total number of base repetitions read by its resident map occurrences.
The choice of absorbed words does not itself contribute a parameter. -/
theorem shrinkKernelWitness_totalExponent (s : ∀ m, P.ShrinkChoice number w B m)
    (v : (V × Tag) × L) (a z)
    (x : (P.shrinkKernelWitness hc hd number order w B κ hκ ready I s v a z).Choice) :
    (∑ label, (P.shrinkKernelWitness hc hd number order w B κ hκ ready I s v a z).exponents
      x label) = ∑ t : {q : P.Motif × Fin 6 // P.shrinkPartySite
        (P.shrinkTermLayout B number w s) q.1 q.2 = v},
        repetitions B (P.shrinkDemandWidths number w t.1.1) := by
  let J := {q : P.Motif × Fin 6 // P.shrinkPartySite (P.shrinkTermLayout B number w s) q.1 q.2 = v}
  change (∑ label, ∑ t : J, _) = _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro t _
  exact entryWitness_totalExponent κ _ _

/-- The complete kernel degree at a site obeys a linear envelope in the
largest incoming width, uniformly over selected layouts and witnesses. -/
theorem shrinkKernelWitness_degree_le (s : ∀ m, P.ShrinkChoice number w B m)
    (v : (V × Tag) × L) (a z)
    (x : (P.shrinkKernelWitness hc hd number order w B κ hκ ready I s v a z).Choice)
    {W : ℕ} (hw : ∀ e, w e ≤ W) :
    (∑ label, (P.shrinkKernelWitness hc hd number order w B κ hκ ready I s v a z).exponents
      x label) ≤ (6 * (d * pieceCount d c) * fieldFactor B) * (W + 1) := by
  rw [P.shrinkKernelWitness_totalExponent]
  exact P.shrinkSite_repetitions_le hc hd number w hw B _ _

end Compression.PackingData

end VPVNP
end Computability
end OAI
