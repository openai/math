import OAI.ThreeFlat.Diagonal.RefreshWireShapes
import OAI.ThreeFlat.Diagonal.SlotRefinement

namespace OAI
/-! # A refresh step of an adaptive physical contraction history -/

namespace ThreeFlat.Diagonal.RefreshTies

open Computability.VPVNP.Compression LinearAlgebra.SpectralBooks HistoryContraction
open private sum_congr_instances from OAI.ThreeFlat.Diagonal.RefreshKernel
open scoped Classical BigOperators
noncomputable section

private theorem prod_congr_instances {I K : Type*} [CommMonoid K] {u v : Fintype I}
    {f g : I → K} (h : ∀ i, f i = g i) :
    (∏ i ∈ @Finset.univ I u, f i) = ∏ i ∈ @Finset.univ I v, g i := by
  cases Subsingleton.elim u v
  exact Finset.prod_congr rfl (fun i _ => h i)

variable {V C L : Type} [Fintype V] [Fintype L] [AddCommGroup C] [AddCommGroup L] {m : ℕ}
variable (G : LiftedSlots V m (C × L)) (port : Fin m ≃ C)

/-- Destination site of the new single external arc leaving one port. -/
def externalSite (p : (V × L) × Fin m) : (V × L) × Fin m :=
  (((G.base.target (p.1.1,p.2)).1, p.1.2+(G.displacement (p.1.1,p.2)).2), (G.base.target (p.1.1,p.2)).2)

omit [Fintype V] [Fintype L] in
theorem external_site (e : Address (V × L) m) :
    externalSite G (e.1,e.2.2) = ((arrival G port e).1,(arrival G port e).2.2) := rfl

variable {K : Type} [Field K] (A : Address (V × L) m → Type) [∀ e, Fintype (A e)]
variable (H S : V × L → Type) [∀ u, Fintype (H u)] [∀ u, Fintype (S u)]
variable (P : ∀ u, PortGraph (Fin m) (S u)) (B : ∀ u, H u → S u → Type) [∀ u h s, Fintype (B u h s)]
variable (M : ∀ u h v, (RefreshMotif.denseGraph m).State (fun e => A (addr (arrival G port) u e)) v →
  (P u).State (B u h) v → K)

def localEntry (h : ∀ u, H u) (p : (V × L) × Fin m)
    (a : (oldPortGraph (arrival G port)).State A p)
    (b : (rawGraph (externalSite G) P).State (rawLabel A (fun u => B u (h u))) p) : K :=
  M p.1 (h p.1) p.2 (portFields (arrival G port) p.1 p.2 (oldAt (arrival G port) p.1 p.2 a)
    (bundleAt (arrival G port) (externalSite G) (external_site G port) P A _ p.1 p.2 b))
    (sparseAt (externalSite G) P A _ p.1 p.2 b)

variable (tile : ∀ u x, (RefreshMotif.denseGraph m).wiring (fun e => A (addr (arrival G port) u e)) x =
  ∑ h, ∑ w : ∀ e, B u h e, ∏ v, M u h v (x v) ((P u).atVertex w v))

include tile in
theorem old_wiring_eq_raw (a : ∀ j, (oldPortGraph (arrival G port)).State A j) :
    (oldPortGraph (arrival G port)).wiring A a =
      ∑ h : ∀ u, H u, (rawGraph (externalSite G) P).contraction
        (fun p b => localEntry G port A H S P B M h p (a p) b) := by
  have old : (oldPortGraph (arrival G port)).wiring A a =
      (if ends (arrival G port) a false = ends (arrival G port) a true then (1 : K) else 0) := by
    unfold PortGraph.wiring
    by_cases wired : ends (arrival G port) a false=ends (arrival G port) a true
    · rw [ite_eq_left wired]
      exact ite_eq_left fun e=>congrFun wired e
    · rw [ite_eq_right wired]
      exact ite_eq_right fun e=>wired (funext e)
  rw [old, refresh_kernel G port A H S P B M tile]
  apply Finset.sum_congr rfl
  intro h _
  let f (z : ∀ e,rawLabel A (fun u=>B u (h u)) e) :=
    ∏ p, localEntry G port A H S P B M h p (a p) ((rawGraph (externalSite G) P).atVertex z p)
  refine Eq.trans ?_ (((rawAssignment A (fun u=>B u (h u))).sum_comp f).trans ?_)
  · rw [Fintype.sum_prod_type]
    apply sum_congr_instances
    intro z
    apply sum_congr_instances
    intro w
    dsimp only [f]
    conv_rhs => rw [Fintype.prod_prod_type]
    apply prod_congr_instances
    intro u
    apply prod_congr_instances
    intro v
    unfold localEntry
    rw [oldAt_eq]; rfl
  · unfold PortGraph.contraction
    apply sum_congr_instances
    intro z
    rfl

/-- Assemble one complete refresh step. The supplied physical numbering
puts bundles, sparse arcs, and singleton padding onto the public slot graph.
There is one history component for every simultaneous choice of port tiles. -/
def refreshRewrite {D : Type} [Fintype D] (T : PortGraph ((V × L) × Fin m) D)
    (C' : (∀ u, H u) → D → Type) [∀ h j, Fintype (C' h j)]
    (physical : ∀ h : ∀ u, H u, SlotRefinement.Refines (rawGraph (externalSite G) P)
      (rawLabel A (fun u => B u (h u))) T (C' h)) :
    Rewrite (oldShape (arrival G port) A) K where
  count := Fintype.card (∀ u, H u)
  target t := SlotRefinement.shape T (C' ((Fintype.equivFin _).symm t))
  owner _ := id
  kernel t v a b := localEntry G port A H S P B M _ v (a ⟨v,rfl⟩) ((physical _).read v b)
  wire_eq a := by
    let f (h : ∀ u,H u) := T.contraction (fun v (b : T.State (C' h) v) =>
      localEntry G port A H S P B M h v (a v) ((physical h).read v b))
    change (oldPortGraph (arrival G port)).wiring A a =
      ∑ t, f ((Fintype.equivFin (∀ u,H u)).symm t)
    rw [old_wiring_eq_raw G port A H S P B M tile a,
      (Fintype.equivFin (∀ u,H u)).symm.sum_comp f]
    apply Finset.sum_congr rfl
    intro h _
    let g (z : ∀ e,C' h e) := ∏ v,localEntry G port A H S P B M h v (a v)
      ((physical h).read v (T.atVertex z v))
    refine Eq.trans ?_ ((physical h).boundary.sum_comp g)
    unfold PortGraph.contraction
    apply sum_congr_instances
    intro z
    dsimp only [g]
    simp only [(physical h).read_at]

end
end ThreeFlat.Diagonal.RefreshTies

end OAI
