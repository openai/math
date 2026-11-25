import OAI.Hierarchy.ABPFirstCutRank
import OAI.Computability.BorderVNP.Model

namespace OAI
/-! # Splitting the slots of a cut into their individual tensor legs

A slot state can be assembled from the labels of its incident legs. At a cut
of the slots this substitution acts separately on the row and column indices
of the flattening. It thus preserves every upper bound on the flattening rank,
including for each summand inside a Zariski closure of sums.
-/

namespace Hierarchy.ABPFirstCut

open scoped BigOperators
open Computability.BorderVNP MvPolynomial
noncomputable section

variable {V P : Type} {τ : V → Type} {ν : P → Type} {F : Type*} [Field F]

/-- The slot state at a vertex is assembled from the labels on its own legs. -/
def slotRead (owner : P → V)
    (assemble : ∀ v, (∀ p : {p // owner p = v}, ν p.val) → τ v)
    (x : ∀ p, ν p) (v : V) : τ v := assemble v (fun p => x p.val)

variable [Fintype P] [DecidableEq V]

/-- The physical legs attached to slots in `U`. -/
def legsOfCut (owner : P → V) (U : Finset V) : Finset P :=
  Finset.univ.filter fun p => owner p ∈ U

@[simp] theorem mem_legsOfCut {owner : P → V} {U : Finset V} {p : P} :
    p ∈ legsOfCut owner U ↔ owner p ∈ U := by simp [legsOfCut]

variable [DecidableEq P]

private def readInside (owner : P → V)
    (assemble : ∀ v, (∀ p : {p // owner p = v}, ν p.val) → τ v)
    (U : Finset V) (x : Inside ν (legsOfCut owner U)) : Inside τ U :=
  fun v => assemble v.val (fun p => x ⟨p.val, mem_legsOfCut.mpr (by simpa only [p.property] using v.property)⟩)

private def readOutside (owner : P → V)
    (assemble : ∀ v, (∀ p : {p // owner p = v}, ν p.val) → τ v)
    (U : Finset V) (y : Outside ν (legsOfCut owner U)) : Outside τ U :=
  fun v => assemble v.val (fun p => y ⟨p.val, fun h => v.property (p.property ▸ mem_legsOfCut.mp h)⟩)

private theorem slotRead_join (owner : P → V)
    (assemble : ∀ v, (∀ p : {p // owner p = v}, ν p.val) → τ v)
    (U : Finset V) (x : Inside ν (legsOfCut owner U)) (y : Outside ν (legsOfCut owner U)) :
    slotRead owner assemble (join (legsOfCut owner U) x y) =
      join U (readInside owner assemble U x) (readOutside owner assemble U y) := by
  funext v
  by_cases hv : v ∈ U
  · simp only [slotRead, join, hv, dite_true, readInside]
    apply congrArg (assemble v)
    funext p
    have hp : p.val ∈ legsOfCut owner U := mem_legsOfCut.mpr (by simpa only [p.property] using hv)
    simp [hp]
  · simp only [slotRead, join, hv, dite_false, readOutside]
    apply congrArg (assemble v)
    funext p
    have hp : p.val ∉ legsOfCut owner U := fun h => hv (p.property ▸ mem_legsOfCut.mp h)
    simp [hp]

variable [Fintype V] [∀ v, Fintype (τ v)] [∀ p, Fintype (ν p)]

/-- The flattening of the tensor on individual legs is a submatrix of the
flattening on slot states. This holds for arbitrary local assembly maps. -/
theorem flatten_rank_slotRead (owner : P → V)
    (assemble : ∀ v, (∀ p : {p // owner p = v}, ν p.val) → τ v)
    (U : Finset V) (T : (∀ v, τ v) → F) :
    (flatten (legsOfCut owner U) (T ∘ slotRead owner assemble)).rank ≤ (flatten U T).rank := by
  have eq : flatten (legsOfCut owner U) (T ∘ slotRead owner assemble) =
      (flatten U T).submatrix (readInside owner assemble U) (readOutside owner assemble U) := by
    ext x y
    exact congrArg T (slotRead_join owner assemble U x y)
  rw [eq]
  exact Matrix.rank_submatrix_le ..

variable {C : Type*} [Fintype C]

/-- Sums indexed by a family of cuts, each summand having rank at most `s`
across the cut at its index. Several indices may specify the same cut. -/
def rankSumsOn (cuts : C → Finset V) (s : ℕ) : Set ((∀ v, τ v) → F) :=
  { T | ∃ t : C → (∀ v, τ v) → F, (∀ a, T a = ∑ c, t c a) ∧
      ∀ c, (flatten (cuts c) (t c)).rank ≤ s }

/-- Package the pointwise decomposition as an ordinary sum of tensors, as
used by the spectral-price summand selection theorem. -/
theorem rankSumsOn_decomposition (cuts : C → Finset V) {s : ℕ} {T : (∀ v, τ v) → F}
    (h : T ∈ rankSumsOn cuts s) : ∃ Y : C → (∀ v, τ v) → F,
    (∑ c, Y c) = T ∧ ∀ c, (flatten (cuts c) (Y c)).rank ≤ s := by
  obtain ⟨Y, heq, hrank⟩ := h
  refine ⟨Y, ?_, hrank⟩
  funext x
  simpa only [Finset.sum_apply] using (heq x).symm

/-- The attainable set is precisely the image obtained by adding tensors
satisfying the separate cut constraints. -/
theorem rankSumsOn_eq_image (cuts : C → Finset V) (s : ℕ) :
    rankSumsOn (F := F) (τ := τ) cuts s =
      (fun Y : C → (∀ v, τ v) → F => ∑ c, Y c) '' { Y | ∀ c, (flatten (cuts c) (Y c)).rank ≤ s } := by
  ext T
  constructor
  · intro h
    obtain ⟨Y, heq, hrank⟩ := rankSumsOn_decomposition cuts h
    exact ⟨Y, hrank, heq⟩
  · rintro ⟨Y, hrank, rfl⟩
    exact ⟨Y, fun x => by simp only [Finset.sum_apply], hrank⟩

/-- Coordinate substitution transports the entire closure of sums to the
corresponding closure on physical legs, retaining the same summand index. -/
theorem closure_rankSumsOn_slotRead (owner : P → V)
    (assemble : ∀ v, (∀ p : {p // owner p = v}, ν p.val) → τ v)
    (cuts : C → Finset V) {s : ℕ} {T : (∀ v, τ v) → F}
    (h : T ∈ imageClosure (rankSumsOn cuts s)) :
    T ∘ slotRead owner assemble ∈ imageClosure (rankSumsOn (fun c => legsOfCut owner (cuts c)) s) := by
  have hmap := imageClosure_polynomial h (fun x => X (slotRead owner assemble x))
  simp only [eval_X] at hmap
  apply imageClosure_mono _ hmap
  rintro _ ⟨_, ⟨t, heq, hrank⟩, rfl⟩
  exact ⟨fun c => t c ∘ slotRead owner assemble, fun x => heq _,
    fun c => (flatten_rank_slotRead owner assemble (cuts c) (t c)).trans (hrank c)⟩

end
end Hierarchy.ABPFirstCut

end OAI
