import OAI.LinearAlgebra.SpectralBooks.PlanarSurgery.PlanarFirstReturn
import OAI.Geometry.HyperbolicGroups.BoundaryList

/-! # The return permutation inside each glued occurrence -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace PlanarSurgery

open Equiv Equiv.Perm HyperbolicObstruction.PictureSwitch

variable {D A S T : Type*} [Fintype D] [Fintype A] (p : Perm D) (q : Perm A)
  (j : S ↪ D) (k : T ↪ A) (hp : Covers p j) (hq : Covers q k)
  (ι : D → A) (ιs : S → T)
  (hturn : ∀ x, ι (p x) = q (ι x)) (hmark : ∀ s, ι (j s) = k (ιs s))
  (hreflect : ∀ x, ι x ∈ Set.range k → x ∈ Set.range j)

include hturn hmark hreflect in
theorem firstStub_map (x : D) : firstStub q k hq (ι x) = ιs (firstStub p j hp x) := by
  induction x using (measure (arrivalTime p j hp)).wf.induction with
  | h x ih =>
    by_cases hx : x ∈ Set.range j
    · obtain ⟨s,rfl⟩ := hx
      rw [hmark, firstStub_mark, firstStub_mark]
    · have h₁ : ι x ∉ Set.range k := fun h => hx (hreflect x h)
      have h₂ : arrivalTime p j hp (p x) < arrivalTime p j hp x := by
        rw [arrivalTime_advance p j hp hx]
        exact Nat.lt_succ_self _
      rw [← firstStub_advance q k hq h₁, ← hturn, ← firstStub_advance p j hp hx]
      exact ih _ h₂

include hturn hmark hreflect in
theorem onStubs_map [Fintype S] [Fintype T] (s : S) :
    onStubs q k hq (ιs s) = ιs (onStubs p j hp s) := by
  rw [onStubs_apply, ← hmark, ← hturn]
  exact firstStub_map p q j k hp hq ι ιs hturn hmark hreflect _

/-- Surjectivity on genuine stubs and equality of the local rotation words
identify two maps' returns on the common boundary. -/
theorem onStubs_eq_of_local [Fintype S] {B : Type*} [Fintype B]
    (j' : S ↪ B) (q' : Perm B) (hq' : Covers q' j') {I : Type*} {U : I → Type*}
    [∀ i, DecidableEq (U i)] (index : (i : I) → U i → S)
    (cover : ∀ s, ∃ i u, index i u = s) (word : ∀ i, List (U i))
    (old : ∀ i u, onStubs p j hp (index i u) = index i ((word i).formPerm u))
    (new_ : ∀ i u, onStubs q' j' hq' (index i u) = index i ((word i).formPerm u)) :
    onStubs p j hp = onStubs q' j' hq' := by
  ext s
  obtain ⟨i,u,rfl⟩ := cover s
  exact (old i u).trans (new_ i u).symm

end PlanarSurgery

end

end SpectralBooks
end LinearAlgebra
end OAI
