import OAI.Computability.VPVNP.CompressionDegreeCoverage
import OAI.Computability.VPVNP.RefreshProcedureRecords
import OAI.Computability.VPVNP.RefreshProcedureWitness
import OAI.Computability.VPVNP.ShrinkProcedureHistory
import OAI.Computability.VPVNP.ShrinkProcedureWitness

/-!
# Parameter degrees of the local compressor maps

Every accepted shrinking map reads one label per base repetition, and every
resident occurrence of that map contributes its own record. The refresh
reads the labels of a single motif entry after its two diagonal checks.
This identifies the total parameter multiplicity with the sum of the
degrees stored in the actual records of each selected substep.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace Compression.State

open NetworkKernel MotifBlocks MotifGrid MotifConversion PackingData ShrinkMotif

variable {a b g : ℕ} {δ factor : ℝ} (X : State a (packingLaneBits a g))
variable {k : Type*} [Field k]
variable (B : FixedBlock k demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable {R : Type*} [CommRing R] (κ : (parameterData B).Entry → R)
variable (hκ : (parameterData B).IsSolution κ)
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ)

set_option maxHeartbeats 1200000 in
-- Matching the reindexed kernel unfolds the dyadic state pass.
/-- The recorded resident maps account for all labels of a shrinking-site witness. -/
theorem shrinkStateKernelWitness_degree_eq (s : X.ShrinkSelection B) (v x z)
    (w : (X.shrinkStateKernelWitness B κ hκ ready s v x z).Choice) :
    (∑ label, (X.shrinkStateKernelWitness B κ hκ ready s v x z).exponents w label) =
      ∑ j, ((X.shrinkStatePass B κ hκ ready).slotRecords
        (X.shrinkExtraRecords B κ hκ ready) s v).degree j := by
  classical
  exact X.packingData.shrinkKernelWitness_totalExponent (two_le_packingColors a)
    (Nat.two_pow_pos a) X.shrinkNumber X.shrinkOrder X.packingWidth B κ hκ ready
    (X.shrinkStateIndex ready) s v _ _ w

end Compression.State

namespace Compression.Refresh

open NetworkKernel SpectralGeometry DegreeRefresh MotifConversion

variable {a g a₀ dH : ℕ} {k : Type*} [Field k] {K K' : ℝ}
variable (X : State a (a + g)) (P : RegularArcGraph (Fin (2 ^ a)) dH) (hdH : 0 < dH)
  (hconn : (arcSupportGraph P.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply P hdH hconn) (2 ^ a₀) K K')
  (hD : 1 < 2 ^ a) (hd : dH + 1 ≤ 2 ^ a₀)
variable {R : Type*} [CommRing R] (κ : (parameterData F).Entry → R)
  (hκ : (parameterData F).IsSolution κ)

set_option maxHeartbeats 1200000 in
-- The recorded degree and accepted entry are in different port coordinates.
/-- The motif entry supplies the full recorded degree of an accepted refresh port. -/
theorem dyadicRefreshKernelWitness_degree_eq (c : DyadicRefreshChoice X P hdH hconn F) (v x z)
    (w : (dyadicRefreshKernelWitness X P hdH hconn F hD hd κ hκ c v x z).Choice) :
    (∑ label, (dyadicRefreshKernelWitness X P hdH hconn F hD hd κ hκ c v x z).exponents w label) =
      ∑ j, ((dyadicRefreshPass X P hdH hconn F hD hd κ hκ).slotRecords
        (refreshLocalRecords X P hdH hconn F hD hd κ hκ) c v).degree j := by
  let p := promotedSites.symm v
  have h := entryWitness_totalExponent κ (refreshEntryIndices (splitSlots X)
    (bitWordFinEquiv a) (splitWidths X) P hdH hconn F hD hd c p _ _) w
  refine h.trans ?_
  change _ = ∑ j : Fin 3, if j = 0 then repetitions F _ else 0
  simp [p, promotedSites]

end Compression.Refresh

namespace NetworkKernel.MonomialWitness

variable {L M : Type} [Fintype L] [Fintype M] {R : Type*} [CommRing R] {a : R}

/-- Using the shrinking summand preserves the total degree. -/
theorem left_totalExponent (f : L ⊕ M → R) (W : MonomialWitness (f ∘ Sum.inl) a) (w : W.Choice) :
    (∑ l, (W.left f).exponents w l) = ∑ l, W.exponents w l := by
  simp [left, Fintype.sum_sum_type]

/-- Using the refresh summand preserves the total degree. -/
theorem right_totalExponent (f : L ⊕ M → R) (W : MonomialWitness (f ∘ Sum.inr) a) (w : W.Choice) :
    (∑ l, (W.right f).exponents w l) = ∑ l, W.exponents w l := by
  simp [right, Fintype.sum_sum_type]

end NetworkKernel.MonomialWitness

namespace Compression.BlockSchedule.Templates

open NetworkKernel Refresh
open private recordsAt from OAI.Computability.VPVNP.ShrinkProcedureHistory

variable {k : Type*} [Field k] {S : BlockSchedule k} (B : S.Templates)
variable {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f)

set_option maxHeartbeats 1200000 in
-- The lane equality transports both records and witnesses.
/-- At the scheduled lane count the tagged shrinking witnesses fit their actual records. -/
theorem shrinkPass_degreeCovered (i : Fin S.steps) {g n : ℕ}
    (h : n = packingLaneBits (S.degreeExponent i.castSucc) g)
    (X : State (S.degreeExponent i.castSucc) n) :
    (B.shrinkPassAt f hf i h X).DegreeCovered (B.shrinkPassWitnesses f hf i h X)
      (recordsAt B f hf i h X) := by
  subst n
  intro s v x z w
  let hκ := ((B.solution_iff f).mp hf).1
  let W := X.shrinkStateKernelWitness B.shrink (f ∘ Sum.inl) hκ (S.shrink i)
  exact (MonomialWitness.left_totalExponent f (W s v x z) w).le.trans
    (X.shrinkStateKernelWitness_degree_eq B.shrink (f ∘ Sum.inl) hκ (S.shrink i) s v x z w).le

set_option maxHeartbeats 1200000 in
-- The type of the local witness depends on its concrete refresh branch.
/-- Each tagged refresh witness fits the records of its chosen port and branch. -/
theorem refreshPass_degreeCovered (g : ℕ) (X : State S.portExponent (S.portExponent + g)) :
    let conn := (S.port_bound.connected_and_pos S.port_order).1
    let hκ := ((B.solution_iff f).mp hf).2
    let p := dyadicRefreshPass X S.graph (Nat.two_pow_pos _) conn B.refresh S.port_order
      S.degree_bounds.2 (f ∘ Sum.inr) hκ
    p.DegreeCovered (fun c v x z ↦ MonomialWitness.right f
      (dyadicRefreshKernelWitness X S.graph (Nat.two_pow_pos _) conn B.refresh
        S.port_order S.degree_bounds.2 (f ∘ Sum.inr) hκ c v x z))
      (p.slotRecords (refreshLocalRecords X S.graph (Nat.two_pow_pos _) conn B.refresh
        S.port_order S.degree_bounds.2 (f ∘ Sum.inr) hκ)) := by
  intro conn hκ p c v x z w
  let W := dyadicRefreshKernelWitness X S.graph (Nat.two_pow_pos _) conn B.refresh
    S.port_order S.degree_bounds.2 (f ∘ Sum.inr) hκ
  exact (MonomialWitness.right_totalExponent f (W c v x z) w).le.trans
    (dyadicRefreshKernelWitness_degree_eq X S.graph (Nat.two_pow_pos _) conn B.refresh
      S.port_order S.degree_bounds.2 (f ∘ Sum.inr) hκ c v x z w).le

end Compression.BlockSchedule.Templates

end VPVNP
end Computability
end OAI
