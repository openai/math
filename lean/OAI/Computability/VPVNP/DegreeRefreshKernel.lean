import OAI.Computability.VPVNP.DegreeRefreshTopology
import OAI.Computability.VPVNP.WireTensor
import Mathlib.Algebra.BigOperators.Fin

/-!
# Exact external-wire contraction in the degree refresh

Section 7.3 of *VP and VNP differ over every field* consumes one port index
per lane and concatenates all port payloads on each old base arc in source
port order. At each block, outgoing and incoming half-wires are tied to their
segments of the appropriate external wires. Summing the external payloads
restores the old network coefficient for every assignment of its half-wires.
-/

namespace OAI
namespace Computability
namespace VPVNP

open scoped Classical

namespace Compression.Refresh

/-- A block and slot index the external bundle. The final coordinate gives an old source port. -/
abbrev Arc (B : Type*) (d : ℕ) := (B × Fin d) × Fin d

/-- A payload of a given bit width. -/
abbrev Word (width : ℕ) := Fin width → Bool

variable {B H L V : Type*} {d : ℕ}

/-- Reindex the old matching by its block, slot and source port. -/
def oldPortMatching [AddCommGroup H] [AddCommGroup L] (G : LiftedSlots V d (H × L))
    (label : H ≃ Fin d) : Equiv.Perm (Arc (V × L) d) :=
  (bundleCoordinates label).symm.trans (G.actualTarget.trans (bundleCoordinates label))

@[simp] theorem oldPortMatching_apply [AddCommGroup H] [AddCommGroup L]
    (G : LiftedSlots V d (H × L)) (label : H ≃ Fin d) (s : (V × L) × Fin d) (j : Fin d) :
    oldPortMatching G label (s,j) = (bundleTarget G s, bundlePort G label s j) :=
  actualTarget_bundleCoordinates G label s j

/-- Each old slot endpoint belongs to its block at the indicated port. -/
def source (a : Arc B d) : B × Fin d := (a.1.1,a.2)

/-- External strings are concatenated in order of the old source ports. -/
abbrev External (w : Arc B d → ℕ) := (s : B × Fin d) → Word (∑ j : Fin d, w (s,j))

/-- Extract one old payload from the concatenated external string. -/
def segment (w : Arc B d → ℕ) (z : External w) (a : Arc B d) : Word (w a) :=
  fun i ↦ z a.1 (finSigmaFinEquiv (n := fun j ↦ w (a.1,j)) ⟨a.2,i⟩)

/-- The bit offset of a segment is the sum of the preceding source-port widths. -/
theorem segment_offset (w : Arc B d → ℕ) (s : B × Fin d) (j : Fin d) (i : Fin (w (s,j))) :
    (finSigmaFinEquiv (n := fun k ↦ w (s,k)) ⟨j,i⟩ : ℕ) =
      (∑ k : Fin j, w (s, Fin.castLE j.isLt.le k)) + i := finSigmaFinEquiv_apply _

/-- Ordered concatenation and segment extraction are mutually inverse, including
for bundles containing zero-width fields. -/
def segmentsEquiv (w : Arc B d → ℕ) : External w ≃ ((a : Arc B d) → Word (w a)) where
  toFun := segment w
  invFun x s i :=
    let p := (finSigmaFinEquiv (n := fun j ↦ w (s,j))).symm i
    x (s,p.1) p.2
  left_inv z := by
    funext s i
    simp [segment]
  right_inv x := by
    funext a i
    rcases a with ⟨s,j⟩
    exact congrArg (fun p : (k : Fin d) × Fin (w (s,k)) ↦ x (s,p.1) p.2)
      ((finSigmaFinEquiv (n := fun k ↦ w (s,k))).symm_apply_apply ⟨j,i⟩)

variable (R : Type*) [CommSemiring R]

/-- A segment tie has coefficient one exactly when its two words agree. -/
noncomputable def segmentTest {α : Type*} (a b : α) : R :=
  by classical exact if a = b then 1 else 0

variable [Fintype B]

/-- The unexpanded wire tensor on the individual old ports. -/
noncomputable def oldNetwork (t : Equiv.Perm (Arc B d)) (w : Arc B d → ℕ) :=
  VPVNP.WireTensor.wireNetwork (k := R) source (fun a ↦ source (t a)) (fun a ↦ Word (w a))

variable {R}

/-- The source half-wire is tied to the matching segment at the outgoing slot's port. -/
noncomputable def outgoingTest (t : Equiv.Perm (Arc B d)) (w : Arc B d → ℕ)
    (x : (v : B × Fin d) → (oldNetwork R t w).Basis v) (z : External w) (a : Arc B d) : R :=
  segmentTest R ((x (source a)).1 a rfl) (segment w z a)

/-- At an incoming slot, the external segment uses the order of its original source.
Inverting the old slot permutation recovers both its source port and its width. -/
noncomputable def incomingTest (t : Equiv.Perm (Arc B d)) (w : Arc B d → ℕ)
    (x : (v : B × Fin d) → (oldNetwork R t w).Basis v) (z : External w) (q : Arc B d) : R :=
  let a := t.symm q
  segmentTest R (segment w z a) ((x (source (t a))).2 a rfl)

/-- All segment ties in a block. For a slot equal to the old port its tie is local. -/
noncomputable def blockTies (t : Equiv.Perm (Arc B d)) (w : Arc B d → ℕ)
    (x : (v : B × Fin d) → (oldNetwork R t w).Basis v) (z : External w) (s : B) : R :=
  ∏ i : Fin d, ∏ j : Fin d, outgoingTest t w x z ((s,i),j) * incomingTest t w x z ((s,i),j)

private theorem prod_blockTies (t : Equiv.Perm (Arc B d)) (w : Arc B d → ℕ)
    (x : (v : B × Fin d) → (oldNetwork R t w).Basis v) (z : External w) :
    ∏ s, blockTies t w x z s =
      (∏ a : Arc B d, outgoingTest t w x z a) * (∏ a : Arc B d, incomingTest t w x z (t a)) := by
  rw [Equiv.prod_comp t (incomingTest t w x z), ← Finset.prod_mul_distrib]
  simp only [Fintype.prod_prod_type, blockTies]

/-- Before the internal demand networks are converted, summing the external
bundle assignments gives the old wire equality tensor entrywise. -/
theorem external_contraction (t : Equiv.Perm (Arc B d)) (w : Arc B d → ℕ)
    (x : (v : B × Fin d) → (oldNetwork R t w).Basis v) :
    (oldNetwork R t w).coeff x = ∑ z : External w, ∏ s, blockTies t w x z s := by
  classical
  let u (a : Arc B d) := (x (source a)).1 a rfl
  let v (a : Arc B d) := (x (source (t a))).2 a rfl
  let F (y : (a : Arc B d) → Word (w a)) :=
    (∏ a, segmentTest R (u a) (y a)) * (∏ a, segmentTest R (y a) (v a))
  have hprod (z : External w) : (∏ s, blockTies t w x z s) = F (segmentsEquiv w z) := by
    rw [prod_blockTies]
    change _ * _ = (∏ a, outgoingTest t w x z a) * ∏ a, segmentTest R (segment w z a) (v a)
    congr 1
    exact Finset.prod_congr rfl fun a _ ↦
      congrArg (fun q ↦ segmentTest R (segment w z q) (v q)) (t.symm_apply_apply a)
  simp_rw [hprod]
  rw [(segmentsEquiv w).sum_comp F]
  have htest (a b : (e : Arc B d) → Word (w e)) :
      (∏ e, segmentTest R (a e) (b e)) = segmentTest R a b := by
    by_cases hab : a = b
    · subst b; simp [segmentTest]
    · obtain ⟨e, he⟩ := Function.ne_iff.mp hab
      rw [Finset.prod_eq_zero (Finset.mem_univ e) (by simp [segmentTest, he])]
      simp [segmentTest, hab]
  have hentry : (oldNetwork R t w).coeff x = ∏ a, segmentTest R (u a) (v a) := by
    apply Finset.prod_congr rfl
    intro a _
    simp [segmentTest, u, v]
  rw [hentry, htest]
  simp only [F, htest]
  simp [segmentTest]

end Compression.Refresh

end VPVNP
end Computability
end OAI
