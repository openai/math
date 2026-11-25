import OAI.Computability.IntegerMultiplication.Net.Tensor

/-! Cube projectors as chart slices. -/

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Tensor
open Finset Matrix
namespace Plate
variable {I J T : Type}
abbrev Spec (I T : Type) := I → Option T

variable [Fintype I] [DecidableEq I] [Fintype J] [DecidableEq J]
/-- cube spec σ is pattern of pinned and free axes -/
def tile (idx : I → T → J) (σ : Spec I T) : Finset (I → J) :=
  Fintype.piFinset fun i => (σ i).elim univ fun t => {idx i t}

omit [DecidableEq J] in
@[simp] theorem inside (idx : I → T → J) (σ : Spec I T) (x) :
    x ∈ tile idx σ ↔ ∀ i t, σ i = some t → x i = idx i t := by
  rw [tile, Fintype.mem_piFinset]
  constructor
  · intro a i t h
    specialize a i
    simpa [h] using a
  intro a i
  cases e : σ i with
  | none => simp
  | some t => simpa using a i t e

omit [DecidableEq J] in
theorem area (idx : I → T → J) (σ : Spec I T) :
    (tile idx σ).card =
      ∏ i, (if (σ i).isSome then 1 else Fintype.card J) := by
  rw [tile, Fintype.card_piFinset]
  refine Finset.prod_congr rfl ?_
  intro i _
  cases σ i <;> simp

omit [DecidableEq J] in
theorem encloses (idx : I → T → J) (σ τ : Spec I T)
    (h : ∀ i t, τ i = some t → σ i = some t) : tile idx σ ⊆ tile idx τ := by
  intro x hx; rw [inside] at *
  exact fun i t ht => hx i t (h i t ht)

variable {R : Type} [CommRing R]
def shade (R : Type) [CommRing R] {A : Type} [DecidableEq A] (u : Finset A) : Vec A R :=
  fun i => if i∈u then 1 else 0

theorem shadow (idx : I → T → J) (σ : Spec I T) :
    shade R (tile idx σ) =
      vec (fun i k => (σ i).elim 1 (fun t => if k=idx i t then 1 else 0)) := by
  classical
  funext x
  let p := fun i => ∀ t, σ i = some t → x i = idx i t
  have e : ∀ i, ((σ i).elim (1:R) (fun t => if x i=idx i t then 1 else 0)) =
      if p i then 1 else 0 := by
    intro i
    dsimp only [p]
    cases eq : σ i with
    | none => simp
    | some t =>
      by_cases h : x i = idx i t
      · have hp : p i := fun u q => by
          have : t=u := by simp_all
          simp_all
        simp [p] at hp
        simp [h]
      simp [h]
  unfold vec shade
  simp_rw [e]
  rw [prod_indicator (p:=p)]
  simp [p]

theorem sdiff {A : Type} [DecidableEq A] (U V : Finset A) (h : V ⊆ U) :
    shade R (U\V) = shade R U - shade R V := by
  funext t
  by_cases u : t∈U <;> by_cases v : t∈V
  · simp [shade,u,v]
  · simp [shade,u,v]
  · exact (u (h v)).elim
  simp [shade,u,v]
theorem disjsum {A : Type} [DecidableEq A] (U V : Finset A) (h : Disjoint U V) :
    shade R (U∪V) = shade R U + shade R V := by
  funext t
  by_cases u : t∈U <;> by_cases v : t∈V
  · exact (Finset.disjoint_left.mp h u v).elim
  all_goals simp [shade,u,v]

def cube (P : T → Mat J R) (σ : Spec I T) : Mat (I → J) R :=
  mat (fun i => (σ i).elim 1 P)
theorem model (σ : Spec I T) (idx : I → T → J) (P : T → Mat J R)
    (Z : I → Chart J R)
    (fit : ∀ i t, σ i = some t → P t = (Z i).ray (idx i t)) :
    cube P σ = (weave Z).slice (shade R (tile idx σ)) := by
  rw [cube, shadow, slice]
  congr 1
  funext i
  cases e : σ i
  · simp [Chart.slice_unit]
  · simp [fit _ _ e, Chart.slice_one_at]
end Plate
end Net.Tensor

end IntegerMultiplication
end Computability
end OAI
