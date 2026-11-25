import OAI.Computability.BorderVNP.CrossingNetwork

/-!
# Subdividing ordinary wires and pinning padding in Proposition 7.2

Each hop of a chosen route has its own internal cable index. An equality table at each
intermediate position compares the words on the two adjacent hops. The new zero-padded
cables have unary zero pins at both endpoints.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Network

open scoped Classical

variable {D : ℕ} {P : Type*} {bits : P → ℕ}

/-- Ordered interior positions on every chosen route, including routes with no interior site. -/
structure WireRoutes (N : Network D P bits) where
  /-- Number of inserted equality sites on each internal edge. -/
  interior : N.Edge → ℕ
  /-- Location of each equality site in the specified unit ball. -/
  place : (e : N.Edge) → Fin (interior e) → {z : EuclideanSpace ℝ (Fin D) // ‖z‖ ≤ 1}

variable (N : Network D P bits) (routes : WireRoutes N)

/-- Distinct hops of the same original wire have distinct shared indices. -/
def subdivide : Network D P bits where
  Site := N.Site ⊕ ((e : N.Edge) × Fin (routes.interior e))
  Edge := (e : N.Edge) × Fin (routes.interior e + 1)
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src j := Fin.cases (.inl (N.src j.1)) (fun i ↦ .inr ⟨j.1, i⟩) j.2
  dst j := Fin.lastCases (.inl (N.dst j.1)) (fun i ↦ .inr ⟨j.1, i⟩) j.2
  width j := N.width j.1
  attach p := .inl (N.attach p)
  position := Sum.elim N.position (fun j ↦ (routes.place j.1 j.2).val)
  in_ball := by rintro (v | j); exact N.in_ball v; exact (routes.place j.1 j.2).property

/-- Extend an ordinary wire assignment by copying its word to every hop. -/
def hopLift (a : N.Assignment) : (N.subdivide routes).Assignment := fun j ↦ a j.1

/-- The first hop recovers the original wire's word. -/
def firstHop (z : (N.subdivide routes).Assignment) : N.Assignment := fun e ↦ z ⟨e, 0⟩

/-- Adjacent hop words agree at every inserted equality site. -/
def HopsAgree (z : (N.subdivide routes).Assignment) : Prop :=
  ∀ j : (e : N.Edge) × Fin (routes.interior e), z ⟨j.1, j.2.castSucc⟩ = z ⟨j.1, j.2.succ⟩

/-- The local comparisons determine every hop from the first one. -/
theorem hopsAgree_iff (z : (N.subdivide routes).Assignment) :
    N.HopsAgree routes z ↔ z = N.hopLift routes (N.firstHop routes z) := by
  constructor
  · intro hz
    funext j
    rcases j with ⟨e, i⟩
    change z ⟨e, i⟩ = z ⟨e, 0⟩
    induction i using Fin.induction with
    | zero => rfl
    | succ i ih => exact (hz ⟨e, i⟩).symm.trans ih
  · intro hz j
    have h₁ := congrFun hz ⟨j.1, j.2.castSucc⟩
    have h₂ := congrFun hz ⟨j.1, j.2.succ⟩
    exact h₁.trans h₂.symm

/-- There is exactly one hop assignment above every original wire assignment. -/
theorem unique_hop_extension (a : N.Assignment) :
    ∃! z, N.HopsAgree routes z ∧ N.firstHop routes z = a := by
  refine ⟨N.hopLift routes a, ⟨fun _ ↦ rfl, rfl⟩, ?_⟩
  intro z hz
  exact ((N.hopsAgree_iff routes z).mp hz.1).trans (congrArg (N.hopLift routes) hz.2)

/-- Old sites read from their incident endpoint hop. Each inserted site is a binary equality
factor on consecutive hop words. A loop can read its source hop. -/
noncomputable def subdivideTables {K : Type*} [Zero K] [One K] (table : N.Tables K) :
    (N.subdivide routes).Tables K := by
  classical
  intro v a x
  cases v with
  | inl v =>
    apply table v
    · intro e
      if h : N.src e.val = v then
        exact a ⟨⟨e.val, 0⟩, Or.inl (congrArg Sum.inl h)⟩
      else
        have hd := e.property.resolve_left h
        exact a ⟨⟨e.val, Fin.last _⟩, Or.inr (by simp [subdivide, hd])⟩
    · exact fun p ↦ x ⟨p.val, congrArg Sum.inl p.property⟩
  | inr j =>
    exact if a ⟨⟨j.1, j.2.castSucc⟩, Or.inr (by simp [subdivide])⟩ =
      a ⟨⟨j.1, j.2.succ⟩, Or.inl (by simp [subdivide])⟩ then 1 else 0

variable {K : Type*} [CommSemiring K]

private theorem lifted_read (table : N.Tables K) (a : N.Assignment) (x : Ports bits) (v : N.Site) :
    (N.subdivide routes).read (N.subdivideTables routes table) (N.hopLift routes a) x (.inl v) =
      N.read table a x v := by
  change table v _ _ = table v _ _
  congr 1
  funext e
  by_cases he : N.src e.val = v <;> simp [he, hopLift]

private theorem hop_product (table : N.Tables K) (z : (N.subdivide routes).Assignment) (x : Ports bits) :
    (∏ v, (N.subdivide routes).read (N.subdivideTables routes table) z x v) =
      if N.HopsAgree routes z then ∏ v, N.read table (N.firstHop routes z) x v else 0 := by
  change (∏ v : N.Site ⊕ ((e : N.Edge) × Fin (routes.interior e)), _) = _
  erw [Fintype.prod_sum_type]
  change _ * (∏ j : (e : N.Edge) × Fin (routes.interior e),
    if z ⟨j.1, j.2.castSucc⟩ = z ⟨j.1, j.2.succ⟩ then (1 : K) else 0) = _
  rw [Fintype.prod_boole]
  by_cases hz : N.HopsAgree routes z
  · unfold HopsAgree at hz ⊢
    simp only [ite_eq_left hz, mul_one]
    apply Finset.prod_congr rfl
    intro v _
    conv_lhs => rw [(N.hopsAgree_iff routes z).mp hz]
    exact lifted_read N routes table _ x v
  · unfold HopsAgree at hz ⊢
    simp only [ite_eq_right hz, mul_zero]

/-- The routed network computes exactly the original tensor on every external port assignment,
over any commutative semiring, including a polynomial ring in the private entries. -/
theorem value_subdivide (table : N.Tables K) (x : Ports bits) :
    (N.subdivide routes).value (N.subdivideTables routes table) x = N.value table x := by
  classical
  unfold value
  simp_rw [hop_product]
  rw [← Finset.sum_filter]
  have himg : Finset.univ.filter (N.HopsAgree routes) = Finset.univ.image (N.hopLift routes) := by
    ext z
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hz
      exact ⟨N.firstHop routes z, ((N.hopsAgree_iff routes z).mp hz).symm⟩
    · rintro ⟨a, rfl⟩
      exact fun _ ↦ rfl
  have inj : Function.Injective (N.hopLift routes) :=
    fun _ _ he ↦ congrArg (N.firstHop routes) he
  rw [himg, Finset.sum_image inj.injOn]
  rfl

/-- Add the unused portions of directed cables. Every added word has two unary endpoint
factors at the requested locations, which may coincide with any other site positions. -/
def padCables {Q : Type} [Fintype Q] (extra : Q → ℕ)
    (place : Q → Bool → {z : EuclideanSpace ℝ (Fin D) // ‖z‖ ≤ 1}) : Network D P bits where
  Site := N.Site ⊕ (Q × Bool)
  Edge := N.Edge ⊕ Q
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src := Sum.elim (.inl ∘ N.src) (fun q ↦ .inr (q, false))
  dst := Sum.elim (.inl ∘ N.dst) (fun q ↦ .inr (q, true))
  width := Sum.elim N.width extra
  attach p := .inl (N.attach p)
  position := Sum.elim N.position (fun p ↦ (place p.1 p.2).val)
  in_ball := by rintro (v | p); exact N.in_ball v; exact (place p.1 p.2).property

variable {Q : Type} [Fintype Q] (extra : Q → ℕ)
  (place : Q → Bool → {z : EuclideanSpace ℝ (Fin D) // ‖z‖ ≤ 1})

/-- The original tables use their original words. A pad at either endpoint contributes one
precisely when the whole extra word is zero. -/
noncomputable def padTables (table : N.Tables K) : (N.padCables extra place).Tables K := by
  classical
  intro v a x
  cases v with
  | inl v =>
    exact table v (fun e ↦ a ⟨.inl e.val, e.property.imp (congrArg Sum.inl) (congrArg Sum.inl)⟩)
      (fun p ↦ x ⟨p.val, congrArg Sum.inl p.property⟩)
  | inr p =>
    have incident : (N.padCables extra place).src (.inr p.1) = .inr p ∨
        (N.padCables extra place).dst (.inr p.1) = .inr p := by
      rcases p with ⟨p, b⟩; cases b; exact Or.inl rfl; exact Or.inr rfl
    exact if a ⟨.inr p.1, incident⟩ = fun _ ↦ false then 1 else 0

private def padAssignments : (N.padCables extra place).Assignment ≃ N.Assignment × Ports extra :=
  Equiv.sumPiEquivProdPi _

private theorem pad_product (table : N.Tables K) (a : N.Assignment) (pad : Ports extra)
    (x : Ports bits) : (∏ v, (N.padCables extra place).read (N.padTables extra place table)
      ((padAssignments N extra place).symm (a, pad)) x v) =
    if pad = (fun _ _ ↦ false) then ∏ v, N.read table a x v else 0 := by
  change (∏ v : N.Site ⊕ (Q × Bool), _) = _
  erw [Fintype.prod_sum_type]
  change (∏ v, N.read table a x v) * (∏ p : Q × Bool,
    if pad p.1 = fun _ ↦ false then (1 : K) else 0) = _
  rw [Fintype.prod_boole]
  have hc : (∀ p : Q × Bool, pad p.1 = fun _ ↦ false) ↔ pad = fun _ _ ↦ false :=
    ⟨fun h ↦ funext fun q ↦ h (q, false), fun h p ↦ congrFun h p.1⟩
  by_cases h : pad = fun _ _ ↦ false
  · simp only [ite_eq_left (hc.mpr h), ite_eq_left h, mul_one]
  · simp only [ite_eq_right (h ∘ hc.mp), ite_eq_right h, mul_zero]

/-- Both zero pins force exactly one possible word on each padding cable. Summing those
words preserves the network value even in positive characteristic. -/
theorem value_padCables (table : N.Tables K) (x : Ports bits) :
    (N.padCables extra place).value (N.padTables extra place table) x = N.value table x := by
  classical
  unfold value
  rw [← (padAssignments N extra place).symm.sum_comp, Fintype.sum_prod_type]
  simp_rw [pad_product]
  simp

/-- The complete layout with separate hop words, adjacent equality tests and zero padding
computes the original contraction on the same external input. -/
theorem value_routed_padded (table : N.Tables K) (x : Ports bits) :
    ((N.subdivide routes).padCables extra place).value
      ((N.subdivide routes).padTables extra place (N.subdivideTables routes table)) x =
      N.value table x :=
  (value_padCables ..).trans (N.value_subdivide routes table x)

end Crossing.Network

end BorderVNP
end Computability
end OAI
