import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic

namespace OAI
/-! # Trivalent contact trees with ordered sublist transfers -/

namespace Hierarchy.DescentContactTree
open scoped Classical BigOperators
noncomputable section
variable {I : Type*} [Fintype I] {K : Type*} [CommSemiring K]

abbrev Node (d : ℕ) := Fin d → Bool

/-- The finite prefix of the destination leaf of one actual old bundle. -/
def prefixAt (dest : I → ℕ → Bool) (d : ℕ) (i : I) : Node d := fun a => dest i a.val
abbrev Cell (dest : I → ℕ → Bool) (d : ℕ) (v : Node d) :=
  {i : I // prefixAt dest d i=v}

/-- The alphabet of the one parent wire of a site contains exactly the old
bundles whose destination has this prefix. -/
abbrev State (A : I → Type*) (dest : I → ℕ → Bool) (d : ℕ) :=
  (v : Node d) → (i : Cell dest d v) → A i.val

def packed (A : I → Type*) (dest : I → ℕ → Bool) (d : ℕ) :
    ((i : I) → A i) ≃ State A dest d where
  toFun x _ i := x i.val
  invFun y i := y (prefixAt dest d i) ⟨i,rfl⟩
  left_inv _ := rfl
  right_inv y := by funext v i; rcases i with ⟨i,rfl⟩;rfl

variable {A : I → Type*} [∀i,Fintype (A i)] {dest : I → ℕ → Bool}

/-- The two child wires are distinguished by the next destination bit.
This local tensor sees just one old word and its two disjoint child words. -/
def tap (d : ℕ) (v : Node d) (x : (i : Cell dest d v) → A i.val)
    (y : State A dest (d+1)) : K :=
  if ∀ i : Cell dest d v, x i = y (prefixAt dest (d+1) i.val) ⟨i.val,rfl⟩ then 1 else 0

omit [Fintype I] in
/-- The carrier of both child ports has size two even if one word is empty. -/
theorem child_prefix (d : ℕ) (v : Node d) (i : Cell dest d v) :
    (fun j : Fin d => prefixAt dest (d+1) i.val j.castSucc)=v := i.property

/-- The only physical child ports of v are the two one-bit extensions of
v, including any child whose subword has width zero. -/
def children (d : ℕ) (v : Node d) : Finset (Node (d+1)) :=
  Finset.univ.image fun b : Bool => Fin.lastCases b v

theorem children_card (d : ℕ) (v : Node d) : (children d v).card≤2 :=
  Finset.card_image_le.trans (by simp)

omit [Fintype I] in
theorem child_mem (d : ℕ) (v : Node d) (i : Cell dest d v) :
    prefixAt dest (d+1) i.val∈children d v := by
  refine Finset.mem_image.mpr ⟨dest i.val d,Finset.mem_univ _,?_⟩
  funext j
  refine Fin.lastCases ?_ (fun z => ?_) j
  · simp [prefixAt]
  · rw [Fin.lastCases_castSucc]
    change v z = dest i.val z.val
    exact (congrFun i.property z).symm

omit [(i : I) → Fintype (A i)] in
/-- Changing any other site's states leaves the local table unchanged. -/
theorem tap_local (d : ℕ) (v : Node d) (x : (i : Cell dest d v) → A i.val)
    (y z : State A dest (d+1)) (agree : ∀ w∈children d v,y w=z w) :
    tap (K:=K) d v x y=tap d v x z := by
  have same (i : Cell dest d v) :
      y (prefixAt dest (d+1) i.val) ⟨i.val,rfl⟩=z (prefixAt dest (d+1) i.val) ⟨i.val,rfl⟩ :=
    congrFun (agree _ (child_mem d v i)) _
  simp only [tap,same]

def step (d : ℕ) (x : State A dest d) (y : State A dest (d+1)) : K :=
  ∏ v, tap d v (x v) y

omit [(i : I) → Fintype (A i)] in
theorem step_eq (d : ℕ) (x : State A dest d) (y : State A dest (d+1)) :
    step (K:=K) d x y =
      if (packed A dest d).symm x=(packed A dest (d+1)).symm y then 1 else 0 := by
  classical
  by_cases eqn : (packed A dest d).symm x=(packed A dest (d+1)).symm y
  · rw [ite_eq_left eqn]
    apply Finset.prod_eq_one
    intro v _
    apply ite_eq_left
    rintro ⟨i,rfl⟩
    exact congrFun eqn i
  · rw [ite_eq_right eqn]
    obtain ⟨i,hi⟩ := Function.ne_iff.mp eqn
    apply Finset.prod_eq_zero (Finset.mem_univ (prefixAt dest d i))
    apply ite_eq_right
    intro h
    exact hi (h ⟨i,rfl⟩)

/-- Direct evaluation of the tree recursively sums over every intermediate
collection of true parent-edge labels once. -/
def route : (d : ℕ) → State A dest 0 → State A dest d → K
  | 0,x,y => if x=y then 1 else 0
  | d+1,x,y => ∑ z : State A dest d, route d x z * step d z y

theorem route_eq (d : ℕ) (x : State A dest 0) (y : State A dest d) :
    route (K:=K) d x y =
      if (packed A dest 0).symm x=(packed A dest d).symm y then 1 else 0 := by
  classical
  induction d with
  | zero => simp [route]
  | succ d ih =>
    rw [route,Finset.sum_eq_single_of_mem
      (packed A dest d ((packed A dest 0).symm x)) (Finset.mem_univ _)]
    · simp [ih,step_eq]
    · intro z _ ne
      have diff : (packed A dest 0).symm x≠(packed A dest d).symm z := by
        intro h
        exact ne ((packed A dest d).symm_apply_eq.mp h.symm)
      simp [ih,diff]

/-- At each level every bundle inhabits exactly one wire. -/
theorem level_width (wt : I → ℕ) (d : ℕ) (dst : I → ℕ → Bool) :
    (∑ v : Node d,∑ i : Cell dst d v,wt i.val)=∑ i,wt i := by
  classical
  let e : (Σ v, Cell dst d v) ≃ I := (Equiv.sigmaFiberEquiv (prefixAt dst d))
  calc
    _ = ∑ q : Σ v, Cell dst d v, wt q.2.val :=
      (Fintype.sum_sigma (fun q : Σ v, Cell dst d v => wt q.2.val)).symm
    _ = _ := e.sum_comp wt

/-- Includes the wire at the root and the wires at the leaves. -/
theorem route_cost (wt : I → ℕ) (h : ℕ) (dst : I → ℕ → Bool) :
    (∑ d∈Finset.range (h+1),∑ v : Node d,∑ i : Cell dst d v,wt i.val)=
      (h+1)*(∑i,wt i) := by simp [level_width]

end
end Hierarchy.DescentContactTree

end OAI
