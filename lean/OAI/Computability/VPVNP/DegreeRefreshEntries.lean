import OAI.Computability.VPVNP.DegreeRefreshCosts
import OAI.Computability.VPVNP.MotifEntryWitness

/-!
# Scalar entries in an actual degree-refresh branch

After the old and new incident indices have been fixed, the port first
tests its two diagonal ties. Passing these tests leaves the single
parameter list of the selected motif entry. The description uses only
the wire indices, and its polynomial can be evaluated at any solution
of the fixed equations.
-/

namespace OAI
namespace Computability
namespace VPVNP

open scoped Classical

namespace Compression.Refresh

open MotifGrid MotifBlocks MotifConversion SpectralGeometry NetworkKernel WireTensor DegreeRefresh

variable {k : Type*} [Field k] {D dH d₀ : ℕ} {K K' : ℝ}
  {V E L : Type} [Fintype V] [Fintype E] [Fintype L] [AddCommGroup E] [AddCommGroup L]
  (G : LiftedSlots V D (E × L)) (port : E ≃ Fin D) (w : (V × Fin D) × (E × L) → ℕ)
  (P : RegularArcGraph (Fin D) dH) (hdH : 0 < dH) (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : FixedBlock k tieSource tieTarget (expanderSupply P hdH hconn)
    (realWidths tieMass) (realWidths (expanderMass d₀)) K K')
  (hD : 1 < D) (hd : dH + 1 ≤ d₀) (c : BlockChoices G port w P hdH hconn F)

/-- The output network and its half-wires depend only on the branch's selected widths. -/
noncomputable abbrev expanderBranchGraph :=
  actualWireGraph (degreeRefresh G P.toSlotGraph hD hd)
    (actualWidths hd port w (blockSupplyWidths G port w P hdH hconn F c))

omit [Fintype V] [Fintype E] [Fintype L] [AddCommGroup E] [AddCommGroup L] in
private theorem promoted_original (p : (V × L) × Fin D) :
    promotedSites p = refreshPositions port (originalSites port p) := by
  simp [promotedSites, originalSites, refreshPositions]

/-- The common scalar indices for one local kernel, after checking the two
diagonal segment equalities. The site is given in block and port coordinates. -/
noncomputable def refreshEntryIndices (p : (V × L) × Fin D)
    (a : Placed (refreshPositions port) (actualWireGraph G w).Half (promotedSites p))
    (z : (expanderBranchGraph G port w P hdH hconn F hD hd c).Half (promotedSites p)) :
    Option (Fin (repetitions F (blockDemandWidths G port w p.1)) → (parameterData F).Entry) := by
  let t := oldPortMatching G port
  let widths := groupedWidths port w
  let dst := bundleTarget G
  let n := blockSupplyWidths G port w P hdH hconn F c
  let A := fun s e ↦ Fin (2 ^ n s e)
  let old := originalIso G port w
  let new := promotedIso G port w P.toSlotGraph hD hd A n (fun s e ↦ (wordIndex (n s e)).symm)
  let x := old.pullHalf p (a (originalSites port p) (promoted_original port p))
  let u := new.pullHalf p z
  let seg := incidentPortSegments t dst (oldPortMatching_bundle G port) widths p
    (u.1 (.inl p) rfl) (u.2 (.inl (dst.symm p)) (dst.apply_symm_apply p).symm)
  let y := supplyHalf (R := ℤ) dst widths Prod.fst (fun e ↦ (P.reverse e).1) A (d₀ - (dH + 1)) p u
  exact if x.1 ((p.1,p.2),p.2) rfl = seg.1 p.2 ∧
      seg.2 p.2 = incomingHalf (R := ℤ) t widths p.1 p.2 p.2 x then
    entry F (fun _ ↦ zero_lt_one) (blockDemandWidths G port w p.1) (c p.1).val p.2
      (portInput (R := ℤ) t widths p.1 p.2 x seg) y
  else none

private theorem eval_checked {Label A : Type*} [CommRing A] {m : ℕ}
    (κ : Label → A) (indices : Option (Fin m → Label)) (a b : Prop) [Decidable a] [Decidable b] :
    (if a then 1 else 0) * (if b then 1 else 0) * evalEntry κ indices =
      evalEntry κ (if a ∧ b then indices else none) := by
  by_cases ha : a <;> by_cases hb : b <;> simp [ha, hb, evalEntry]

/-- Reading the common indices and multiplying the selected scalars gives
the actual kernel coefficient over any ring satisfying the equations. -/
theorem refreshEntryIndices_spec (p : (V × L) × Fin D)
    (a : Placed (refreshPositions port) (actualWireGraph G w).Half (promotedSites p))
    (z : (expanderBranchGraph G port w P hdH hconn F hD hd c).Half (promotedSites p))
    {R : Type*} [CommRing R] (κ : (parameterData F).Entry → R) (hκ : (parameterData F).IsSolution κ) :
    ((expanderRefreshStep G port w P hdH hconn F κ hκ hD hd).term c).kernel (promotedSites p) a z =
      evalEntry κ (refreshEntryIndices G port w P hdH hconn F hD hd c p a z) := by
  simp only [expanderRefreshStep, actualRefreshStep, Step.reindex, Term.reindex, promotedIso,
    refreshStep, refreshTerm, refreshFactor, portDiagonal,
    segmentTest, refreshEntryIndices]
  erw [Equiv.piCongrLeft_apply_apply]
  rw [eval_checked]
  congr 1
  apply ite_congr <;> intros <;> rfl

/-- The integral entry polynomial is either zero or a monomial of coefficient
one and degree at most the number of copies used by this block. -/
theorem refreshEntryIndices_monomial (p : (V × L) × Fin D)
    (a : Placed (refreshPositions port) (actualWireGraph G w).Half (promotedSites p))
    (z : (expanderBranchGraph G port w P hdH hconn F hD hd c).Half (promotedSites p)) :
    let poly := evalEntry (MvPolynomial.X (R := ℤ)) (refreshEntryIndices G port w P hdH hconn F hD hd c p a z)
    (poly = 0 ∨ ∃ f, poly = MvPolynomial.monomial f 1) ∧
      poly.totalDegree ≤ repetitions F (blockDemandWidths G port w p.1) := by
  cases h : refreshEntryIndices G port w P hdH hconn F hD hd c p a z with
  | none => simp [evalEntry]
  | some i => exact ⟨Or.inr ⟨_, MotifParameters.prod_entries_eq_monomial i⟩,
      MotifParameters.prod_entries_degree_le i⟩

/-- A kernel entry witness at an actual port. A failed list has no witnesses,
and a successful list gives one witness independently of the scalar values. -/
noncomputable def expanderKernelWitness {R : Type*} [CommRing R]
    [Fintype (parameterData F).Entry] (κ : (parameterData F).Entry → R)
    (hκ : (parameterData F).IsSolution κ) (v : (V × Fin D) × L)
    (a : Placed (refreshPositions port) (actualWireGraph G w).Half v)
    (z : (expanderBranchGraph G port w P hdH hconn F hD hd c).Half v) :
    MonomialWitness κ (((expanderRefreshStep G port w P hdH hconn F κ hκ hD hd).term c).kernel v a z) :=
  let p := promotedSites.symm v
  (entryWitness κ (refreshEntryIndices G port w P hdH hconn F hD hd c p a z)).changeValue
    (refreshEntryIndices_spec G port w P hdH hconn F hD hd c p a z κ hκ).symm

/-- For every surviving witness the total multiplicity is bounded linearly
in the maximum old width, uniformly over all networks of this fixed degree. -/
theorem expanderKernelWitness_exponents {R : Type*} [CommRing R]
    [Fintype (parameterData F).Entry] (κ : (parameterData F).Entry → R)
    (hκ : (parameterData F).IsSolution κ) (v : (V × Fin D) × L)
    (a : Placed (refreshPositions port) (actualWireGraph G w).Half v)
    (z : (expanderBranchGraph G port w P hdH hconn F hD hd c).Half v)
    (b : (expanderKernelWitness G port w P hdH hconn F hD hd c κ hκ v a z).Choice)
    {W : ℕ} (hw : ∀ e, w e ≤ W) :
    (∑ l, (expanderKernelWitness G port w P hdH hconn F hD hd c κ hκ v a z).exponents b l) ≤
      Fintype.card (Tie D) * W := by
  let p := promotedSites.symm v
  refine (entryWitness_totalExponent κ
    (refreshEntryIndices G port w P hdH hconn F hD hd c p a z) b).le.trans ?_
  apply term_repetitions_le F
  intro e
  unfold blockDemandWidths internalWidth
  split_ifs <;> exact hw _

end Compression.Refresh

end VPVNP
end Computability
end OAI
