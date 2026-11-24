import OAI.Computability.VPVNP.DegreeRefresh
import OAI.Computability.VPVNP.DegreeRefreshKernel

/-!
# The internal demand tensor of a degree refresh

In Section 7.3 of *VP and VNP differ over every field*, the nonlocal segment
ties in one block form two copies of the directed complete graph on the
ports, with its loops removed. The omitted ties are diagonal checks performed
locally. The remaining ties are evaluated on the binary wire basis used in
Theorem 6.1. An ordinary sum identity for this motif thus substitutes directly
into the external-wire contraction.
-/

namespace OAI
namespace Computability
namespace VPVNP

open scoped Classical

namespace Compression.Refresh

open WireTensor DegreeRefresh

variable {B R : Type*} {d : ℕ}

/-- Each demand edge starts at the port bearing the old half-wire. -/
def tieSource (e : Tie d) : Fin d := e.2.val.1

/-- Its other endpoint is the slot port bearing the external segment. -/
def tieTarget (e : Tie d) : Fin d := e.2.val.2

/-- The old arc supplying this segment is recovered by inverting the port
permutation when the tie belongs to an incoming slot. -/
def internalWidth (t : Equiv.Perm (Arc B d)) (w : Arc B d → ℕ) (s : B) (e : Tie d) : ℕ :=
  if e.1 then w ((s,tieTarget e),tieSource e) else w (t.symm ((s,tieTarget e),tieSource e))

/-- The equality tensor of the two off-diagonal copies, in the basis
`Fin (2 ^ width)` of the fixed-motif theorem. -/
noncomputable def internalDemand (R : Type*) [CommSemiring R] (t : Equiv.Perm (Arc B d))
    (w : Arc B d → ℕ) (s : B) :=
  wireNetwork (k := R) tieSource tieTarget (fun e ↦ Fin (2 ^ internalWidth t w s e))

/-- Segment lists for the two external half-wires incident to a port, in
source-port order for the outgoing list and destination-port order for the incoming one. -/
abbrev PortSegments (t : Equiv.Perm (Arc B d)) (w : Arc B d → ℕ) (s : B) (i : Fin d) :=
  ((j : Fin d) → Word (w ((s,i),j))) × ((j : Fin d) → Word (w (t.symm ((s,i),j))))

/-- Read the two incident external wires in the prescribed segment order. -/
def portSegments (t : Equiv.Perm (Arc B d)) (w : Arc B d → ℕ) (z : External w)
    (s : B) (i : Fin d) : PortSegments t w s i :=
  (fun j ↦ segment w z ((s,i),j), fun j ↦ segment w z (t.symm ((s,i),j)))

/-- Encode a port's Boolean payload as the binary index of its motif wire. -/
def wordIndex (n : ℕ) : Word n ≃ Fin (2 ^ n) :=
  ((Equiv.refl _).arrowCongr finTwoEquiv.symm).trans finFunctionFinEquiv

variable [CommSemiring R] [Fintype B]

/-- Read an incoming half-wire directly from its destination port. -/
def incomingHalf (t : Equiv.Perm (Arc B d)) (w : Arc B d → ℕ) (s : B) (i j : Fin d)
    (x : (oldNetwork R t w).Basis (s,i)) : Word (w (t.symm ((s,j),i))) :=
  x.2 (t.symm ((s,j),i)) (congrArg source (t.apply_symm_apply ((s,j),i))).symm

/-- The argument of a motif map at a single port. Its first coordinates read
the old incident wires, and its second coordinates read external segments. -/
noncomputable def portInput (t : Equiv.Perm (Arc B d)) (w : Arc B d → ℕ) (s : B) (i : Fin d)
    (x : (oldNetwork R t w).Basis (s,i)) (z : PortSegments t w s i) :
    (internalDemand R t w s).Basis i := by
  refine ⟨?_, ?_⟩
  · rintro ⟨b,⟨⟨p,j⟩,hpj⟩⟩ h
    change i = p at h
    subst p
    cases b
    · exact wordIndex _ (incomingHalf t w s i j x)
    · exact wordIndex _ (x.1 ((s,j),i) rfl)
  · rintro ⟨b,⟨⟨p,j⟩,hpj⟩⟩ h
    change i = j at h
    subst j
    cases b
    · exact wordIndex _ (z.2 p)
    · exact wordIndex _ (z.1 p)

/-- Both diagonal ties are tested inside their common port. -/
noncomputable def portDiagonal (t : Equiv.Perm (Arc B d)) (w : Arc B d → ℕ) (s : B)
    (i : Fin d) (x : (oldNetwork R t w).Basis (s,i)) (z : PortSegments t w s i) : R :=
  segmentTest R (x.1 ((s,i),i) rfl) (z.1 i) *
    segmentTest R (z.2 i) (incomingHalf t w s i i x)

private theorem incomingTest_at (t : Equiv.Perm (Arc B d)) (w : Arc B d → ℕ)
    (x : (v : B × Fin d) → (oldNetwork R t w).Basis v) (z : External w)
    (s : B) (p j : Fin d) :
    incomingTest t w x z ((s,j),p) =
      segmentTest R ((portSegments t w z s j).2 p) (incomingHalf t w s p j (x (s,p))) := by
  have hx (a : Arc B d) (v : B × Fin d) (hv : v = source (t a)) :
      (x (source (t a))).2 a rfl = (x v).2 a hv := by subst v; rfl
  exact congrArg (segmentTest R (segment w z (t.symm ((s,j),p))))
    (hx _ _ (congrArg source (t.apply_symm_apply ((s,j),p))).symm)

private def diagEquiv (d : ℕ) :
    Fin d ≃ {q : Fin d × Fin d // ¬q.1 ≠ q.2} where
  toFun i := ⟨(i,i), by simp⟩
  invFun q := q.val.1
  left_inv _ := rfl
  right_inv q := Subtype.ext (Prod.ext rfl (not_not.mp q.property))

private theorem splitPortProduct (f : Fin d → Fin d → R) :
    (∏ j, ∏ p, f p j) =
      (∏ i, f i i) * ∏ q : {q : Fin d × Fin d // q.1 ≠ q.2}, f q.val.1 q.val.2 := by
  let F (q : Fin d × Fin d) := f q.1 q.2
  calc
    _ = ∏ q, F q := by rw [Fintype.prod_prod_type, Finset.prod_comm]
    _ = _ := by
      rw [← Fintype.prod_subtype_mul_prod_subtype (fun q : Fin d × Fin d ↦ q.1 ≠ q.2) F, mul_comm]
      exact congrArg (· * _) ((diagEquiv d).prod_comp (fun q ↦ F q.val)).symm

private theorem testIndex {n : ℕ} (u v : Word n) :
    segmentTest R u v = segmentTest R (wordIndex n u) (wordIndex n v) := by
  simp [segmentTest]

private theorem testIndexRev {n : ℕ} (u v : Word n) :
    segmentTest R v u = segmentTest R (wordIndex n u) (wordIndex n v) := by
  simp [segmentTest, eq_comm]

/-- Entrywise decomposition into all local checks and the nonlocal binary
demand tensor, with each old half-wire and external segment read at its port. -/
theorem blockTies_factor (t : Equiv.Perm (Arc B d)) (w : Arc B d → ℕ)
    (x : (v : B × Fin d) → (oldNetwork R t w).Basis v) (z : External w) (s : B) :
    blockTies t w x z s =
      (∏ i, portDiagonal t w s i (x (s,i)) (portSegments t w z s i)) *
      (internalDemand R t w s).coeff
        (fun i ↦ portInput t w s i (x (s,i)) (portSegments t w z s i)) := by
  let out (p j : Fin d) := outgoingTest t w x z ((s,j),p)
  let inc (p j : Fin d) := incomingTest t w x z ((s,j),p)
  change (∏ j, ∏ p, out p j * inc p j) = _
  rw [splitPortProduct (fun p j ↦ out p j * inc p j)]
  congr 1
  · exact Finset.prod_congr rfl fun i _ ↦ congrArg (_ * ·) (incomingTest_at t w x z s i i)
  · change _ = ∏ e : Tie d, _
    rw [Fintype.prod_prod_type, Fintype.prod_bool, ← Finset.prod_mul_distrib]
    apply Finset.prod_congr rfl
    rintro ⟨⟨p,j⟩,hne⟩ _
    dsimp only [out, inc, portInput, tieSource, tieTarget, portSegments, internalDemand]
    rw [incomingTest_at]
    exact congrArg₂ (· * ·)
      (testIndex (R := R) ((x (s,p)).1 ((s,j),p) rfl) (segment w z ((s,j),p)))
      (testIndexRev (R := R) (incomingHalf t w s p j (x (s,p))) (segment w z (t.symm ((s,j),p))))

/-- Replacing the nonlocal ties with an ordinary sum of supply maps.
Each diagonal check is absorbed into the matrix at its own port. -/
theorem blockTies_expansion {I : Type*} [Fintype I] (t : Equiv.Perm (Arc B d))
    (w : Arc B d → ℕ) (s : B) (Y : I → Tensor R (Fin d))
    (M : ∀ a i, (internalDemand R t w s).Basis i → (Y a).Basis i → R)
    (h : (internalDemand R t w s).coeff = ∑ a, applyLocal (M a) (Y a).coeff)
    (x : (v : B × Fin d) → (oldNetwork R t w).Basis v) (z : External w) :
    blockTies t w x z s = ∑ a, ∑ y : (i : Fin d) → (Y a).Basis i,
      (∏ i, portDiagonal t w s i (x (s,i)) (portSegments t w z s i) *
        M a i (portInput t w s i (x (s,i)) (portSegments t w z s i)) (y i)) *
        (Y a).coeff y := by
  rw [blockTies_factor, h, Finset.sum_apply, Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [applyLocal, Finset.mul_sum]
  simp only [Finset.prod_mul_distrib, mul_assoc]
  congr 1
  exact Finset.ext fun i ↦ by simp

end Compression.Refresh

end VPVNP
end Computability
end OAI
