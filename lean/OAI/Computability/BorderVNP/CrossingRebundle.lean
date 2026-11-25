import OAI.Computability.BorderVNP.CrossingNetwork

/-!
# Combining the external bit strings of a parallel network

At each terminal, a local table reads the combined external port and forwards each block to
its original site. Every feeder has length zero when the copies share the terminal placement.
The sum over its words introduces no multiplicity.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Network

open scoped BigOperators

variable {D t : ℕ} {P : Type} [Fintype P] {bits : P → ℕ}
variable (N : Network D (Fin t × P) (fun ip => bits ip.2))

/-- Add one terminal site per port and one internal feeder from it to each old port.
The reference copy supplies the terminal's position in the unit ball. -/
def rebundle (base : Fin t) : Network D P (fun p => t * bits p) where
  Site := N.Site ⊕ P
  Edge := N.Edge ⊕ (Fin t × P)
  finiteSite := inferInstance
  finiteEdge := inferInstance
  src := Sum.elim (Sum.inl ∘ N.src) (Sum.inr ∘ Prod.snd)
  dst := Sum.elim (Sum.inl ∘ N.dst) (Sum.inl ∘ N.attach)
  width := Sum.elim N.width (fun ip => bits ip.2)
  attach := Sum.inr
  position := Sum.elim N.position (fun p => N.position (N.attach (base, p)))
  in_ball := by rintro (v | p); exact N.in_ball v; exact N.in_ball (N.attach (base, p))

/-- The input to each of the old ports is its contiguous slice of the terminal word. -/
def portSlices (x : Ports (fun p => t * bits p)) : Ports (fun ip : Fin t × P => bits ip.2) :=
  fun ip k => x ip.2 (finProdFinEquiv (ip.1, k))

/-- The original sites read their old external input from their new feeders. Each new terminal
checks that all its feeder words agree with the respective slices of its external word. -/
noncomputable def rebundleTables {K : Type*} [Zero K] [One K] (base : Fin t)
    (table : N.Tables K) : (N.rebundle base).Tables K := by
  classical
  intro v
  cases v with
  | inl v =>
    exact fun e _ => table v
      (fun f => e ⟨Sum.inl f.val, f.property.imp (congrArg Sum.inl) (congrArg Sum.inl)⟩)
      (fun p => e ⟨Sum.inr p.val, Or.inr (congrArg Sum.inl p.property)⟩)
  | inr p =>
    exact fun e x => if ∀ i : Fin t, e ⟨Sum.inr (i, p), Or.inl rfl⟩ =
        fun k => x ⟨p, rfl⟩ (finProdFinEquiv (i, k)) then 1 else 0

/-- The rebundled network is attached to the same terminals. -/
theorem rebundle_placedAt (base : Fin t) {place : P → EuclideanSpace ℝ (Fin D)}
    (hp : N.PlacedAt (fun ip => place ip.2)) : (N.rebundle base).PlacedAt place :=
  fun p => hp (base, p)

/-- Feeder cables have coincident endpoints and contribute zero total length. -/
theorem rebundle_cost (base : Fin t) {place : P → EuclideanSpace ℝ (Fin D)}
    (hp : N.PlacedAt (fun ip => place ip.2)) : (N.rebundle base).cost = N.cost := by
  classical
  rw [cost]
  change (∑ e : N.Edge ⊕ (Fin t × P), _) = N.cost
  rw [Fintype.sum_sum_type]
  have h (ip) : N.position (N.attach ip) = place ip.2 := hp ip
  simp [rebundle, h, cost]

private def assignmentEquiv (base : Fin t) :
    (N.rebundle base).Assignment ≃ N.Assignment × Ports (fun ip : Fin t × P => bits ip.2) :=
  Equiv.sumPiEquivProdPi (fun e => Fin ((N.rebundle base).width e) → Bool)

private theorem rebundle_product {K : Type*} [CommSemiring K] (base : Fin t) (table : N.Tables K)
    (x : Ports (fun p => t * bits p)) (a : N.Assignment) (z : Ports (fun ip : Fin t × P => bits ip.2)) :
    (∏ v, (N.rebundle base).read (N.rebundleTables base table)
      ((assignmentEquiv N base).symm (a, z)) x v) =
      if z = portSlices x then ∏ v, N.read table a z v else 0 := by
  classical
  change (∏ v : N.Site ⊕ P, _) = _
  erw [Fintype.prod_sum_type]
  have hin (v : N.Site) :
      (N.rebundle base).read (N.rebundleTables base table)
        ((N.assignmentEquiv base).symm (a, z)) x (.inl v) = N.read table a z v := rfl
  have hout (p : P) :
      (N.rebundle base).read (N.rebundleTables base table)
        ((N.assignmentEquiv base).symm (a, z)) x (.inr p) =
          if ∀ i : Fin t, z (i, p) = portSlices x (i, p) then (1 : K) else 0 := by
    unfold read rebundleTables
    dsimp only
    split <;> split <;> first | rfl | contradiction
  simp_rw [hin, hout]
  rw [Fintype.prod_boole]
  have h : (∀ p, ∀ i : Fin t, z (i, p) = portSlices x (i, p)) ↔ z = portSlices x :=
    ⟨fun hall => funext (fun ip => hall ip.2 ip.1), fun he _ _ => congrFun he _⟩
  by_cases he : z = portSlices x
  · simp [he]
  · simp [he, h.not.mpr he]

/-- Summing all feeder assignments forces the unique assignment of terminal slices,
so the contraction computes exactly the original tensor on those slices. -/
theorem rebundle_value {K : Type*} [CommSemiring K] (base : Fin t) (table : N.Tables K)
    (x : Ports (fun p => t * bits p)) :
    (N.rebundle base).value (N.rebundleTables base table) x = N.value table (portSlices x) := by
  classical
  unfold value
  rw [← (assignmentEquiv N base).symm.sum_comp, Fintype.sum_prod_type]
  simp_rw [rebundle_product]
  simp

end Crossing.Network

end BorderVNP
end Computability
end OAI
