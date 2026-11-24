import OAI.Computability.VPVNP.ShrinkLocalMaps
import OAI.Computability.VPVNP.ShrinkSupplyLocal

/-!
# Regrouping all six-party matrices at the sites of the shrinking step

For one choice of outer term at every motif, the layout uses one new
numbered wire per surviving subdivision. Each absorbed wire is internal
to a single site. The product of the six-party matrices agrees with the
product of the entries at the new sites for every original assignment.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.ShrinkMotif

variable {M V k : Type*} [Fintype M] [DecidableEq V] [CommMonoid k]

/-- Computing a site entry requires precisely its list of resident map occurrences. -/
theorem partyProduct_eq_resident (site : M → Fin 6 → V) (v : V)
    (factor : ∀ m j, v = site m j → k) :
    partyProduct site v factor =
      ∏ z : {p : M × Fin 6 // site p.1 p.2 = v}, factor z.1.1 z.1.2 z.2.symm := by
  let f (z : M × Fin 6) : k := if h : v = site z.1 z.2 then factor z.1 z.2 h else 1
  change (∏ m, ∏ j, f (m,j)) = _
  rw [← Fintype.prod_prod_type f,
    ← Fintype.prod_subtype_mul_prod_subtype (fun z ↦ site z.1 z.2 = v) f]
  have hother (z : {p : M × Fin 6 // ¬ site p.1 p.2 = v}) : f z.1 = 1 :=
    by simp [f,Ne.symm z.2]
  simp only [hother, Finset.prod_const_one, mul_one]
  apply Finset.prod_congr rfl
  intro z _
  simp [f, z.2.symm]

end Compression.ShrinkMotif

namespace Compression.PackingData

open NetworkKernel WireTensor MotifDemandPadding ShrinkMotif

variable {V H Tag L : Type} {d c : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
variable (P : PackingData V H Tag L d c)
variable [Fintype V] [Fintype H] [Fintype Tag] [Fintype L]
variable [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
variable (hc : 2 ≤ c) (hd : 0 < d) (number : P.BundleNumbering) (order : P.ThickNumbering)
variable (w : Arc V H Tag L d c → ℕ) (l : Bool) (subdiv : Fin 4 → ℕ)
variable (width : P.Motif → Bool × Fin 4 → ℕ) {d' pad : ℕ} {next : Equiv.Perm (V × Tag)}
variable (I : P.ShrinkIndex l subdiv next d' pad) (hpos : ∀ t, 0 < subdiv t)
variable {R : Type*} [CommSemiring R]
variable (matrix : ∀ m j,
  HalfBits demandSource demandTarget (P.shrinkDemandWidths number w m) j →
  HalfBits supply.src supply.dst (width m) j → R)

/-- Layout of the selected six-party terms, including each absorbed word's
owner and the arguments available to every map at its site. -/
noncomputable def shrinkLayout : Layout R (P.oldWireNetwork w) where
  output := P.shrinkOutput l subdiv (fun m t ↦ width m (l,t)) I
  place := P.shrinkPlace l
  Internal := P.Motif × Fin 4
  internalFintype := inferInstance
  Label := ShrinkMotif.internalLabel width l
  labelFintype _ := inferInstance
  owner := P.shrinkInternalOwner l
  entry v a h z := partyProduct (P.shrinkPartySite l) v fun m j hv ↦
    matrix m j (P.shrinkLocalDemandArg hc hd number order w l m j (hv ▸ a))
      (P.shrinkLocalSupplyArg l subdiv width I hpos m j (hv ▸ h) (hv ▸ z))

/-- Regrouping the selected motif factors, the final hypothesis of
`Step.ofMotifProduct` for the actual padded output graph. -/
theorem shrinkLayout_group (x : (m : P.Motif) → (e : Bool × Fin 4) → Fin (2 ^ width m e))
    (a : ∀ u, (P.oldWireNetwork w).Half u) :
    let T := P.shrinkLayout hc hd number order w l subdiv width I hpos matrix
    let z := P.shrinkAssignmentsEquiv l subdiv width I hpos x
    (∏ m, ∏ j, matrix m j (P.shrinkDemandArg hc hd number order w m a j)
      (edgeAssignment supply.src supply.dst (x m) j)) =
      ∏ v, T.entry v (fun u _ ↦ a u) (fun e _ ↦ z.2 e)
        (edgeAssignment T.output.src T.output.dst z.1 v) := by
  let : DecidableEq (P.shrinkOutput l subdiv (fun m t ↦ width m (l,t)) I).Site :=
    inferInstanceAs (DecidableEq ((V × Tag) × L))
  dsimp only [shrinkLayout]
  erw [prod_partyProduct]
  apply Finset.prod_congr rfl
  intro m _
  apply Finset.prod_congr rfl
  intro j _
  congr 1
  · exact (P.shrinkLocalDemandArg_eval hc hd number order w l m j a).symm
  · exact (P.shrinkLocalSupplyArg_eval l subdiv width I hpos m j x).symm

end Compression.PackingData

end VPVNP
end Computability
end OAI
