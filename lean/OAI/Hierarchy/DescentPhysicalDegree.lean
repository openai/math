import OAI.Hierarchy.DescentPhysicalSplit

namespace OAI
/-! # Exact size and degree of the physically split binary network -/

namespace Hierarchy.DescentPhysicalSplit
open Computability.BorderVNP.Crossing DescentRotor
open scoped Classical BigOperators
noncomputable section
variable {D : ℕ} {P : Type} [Fintype P] {bits : P→ℕ} (N : Network D P bits)

private def recover : Vertex N → Option (Leg N)
  | ⟨v,.inr i⟩ => some (name N v i)
  | ⟨_,.inl _⟩ => none

theorem tap_injective : Function.Injective (tap N) := by
  intro a b h
  have same := congrArg (recover N) h
  simpa [tap,recover,name] using same

private def orientation (s : Bool) (p : Spine N) : Vertex N :=
  ⟨p.1,if s then Attachment.nextSite p.2 else Attachment.prevSite p.2⟩

private theorem oriented_inj (s : Bool) : Function.Injective (orientation N s) := by
  rintro ⟨v,i⟩ ⟨w,j⟩ same
  have vw : v=w := congrArg Sigma.fst same
  subst w
  apply congrArg (Sigma.mk v)
  have loc := eq_of_heq (Sigma.mk.inj same).2
  cases s
  · change Attachment.prevSite i=Attachment.prevSite j at loc
    revert loc
    refine Fin.cases ?_ (fun t=>?_) i <;> refine Fin.cases ?_ (fun u=>?_) j <;> simp [Attachment.prevSite]
  · change Attachment.nextSite i=Attachment.nextSite j at loc
    revert loc
    refine Fin.lastCases ?_ (fun t=>?_) i <;> refine Fin.lastCases ?_ (fun u=>?_) j <;> simp [Attachment.nextSite]

private def edges : Leg (graph N) ≃ Leg N ⊕ (Spine N × Bool) where
  toFun
    | .inl p => .inl (.inl p)
    | .inr (.inl e,b) => .inl (.inr (e,b))
    | .inr (.inr p,b) => .inr (p,b)
  invFun
    | .inl (.inl p) => .inl p
    | .inl (.inr (e,b)) => .inr (.inl e,b)
    | .inr (p,b) => .inr (.inr p,b)
  left_inv := by rintro (p|⟨e|k,b⟩) <;> rfl
  right_inv := by rintro ((p|⟨e,b⟩)|⟨k,b⟩) <;> rfl

private def kind : Leg N ⊕ (Spine N × Bool) → Fin 3
  | .inl _ => 2
  | .inr (_,false) => 0
  | .inr (_,true) => 1

private theorem owner_edges (p : Leg N ⊕ (Spine N × Bool)) :
    owner (graph N) ((edges N).symm p)=Sum.elim (tap N) (fun z=>orientation N z.2 z.1) p := by
  rcases p with (p|⟨e,b⟩)|⟨k,b⟩
  · rfl
  · cases b <;> rfl
  · cases b <;> rfl

private theorem named_full (p q : Leg N ⊕ (Spine N × Bool))
    (pos : owner (graph N) ((edges N).symm p)=owner (graph N) ((edges N).symm q))
    (tag : kind N p=kind N q) : p=q := by
  simp only [owner_edges] at pos
  rcases p with a|⟨k,(_|_)⟩ <;> rcases q with b|⟨l,(_|_)⟩ <;> simp_all [kind]
  all_goals first
    | exact tap_injective N pos
    | exact oriented_inj N false pos
    | exact oriented_inj N true pos

/-- This counts every public pin, both ends of a loop and parallel incidences
separately. A tap has at most one of each of three possible port kinds. -/
theorem degree (v : Vertex N) : (graph N).bitDegree v≤3 := by
  let f : Fibre (graph N) v → Fin 3 := fun p=>kind N (edges N p.val)
  have inj : Function.Injective f := by
    intro p q tag
    apply Subtype.ext
    apply (edges N).injective
    apply named_full N _ _ _ tag
    simpa using p.property.trans q.property.symm
  calc
    (graph N).bitDegree v = count (graph N) v := (count_eq_degree (graph N) v).symm
    _ ≤ 3 := (Fintype.card_le_of_injective f inj).trans (by simp)

theorem site_count : Fintype.card (graph N).Site=∑v,(count N v+2) := by
  change Fintype.card (Vertex N)=_
  simp [Vertex,Fintype.card_sigma,Nat.add_comm]

/-- The original edge count is preserved, and the allocated private wires
are precisely the count(v)+1 edges of the path at each vertex. -/
theorem cable_count : Fintype.card (graph N).Edge=Fintype.card N.Edge+∑v,(count N v+1) := by
  change Fintype.card (Cable N)=_
  simp [Cable,Spine,Fintype.card_sigma]

theorem wires : (∑e,(graph N).width e) =
    (∑e,N.width e)+∑v,(count N v+1)*∑i,localWidth N v i := by
  let cost : Cable N → ℕ := (graph N).width
  change (∑ e, cost e) = _
  rw [Fintype.sum_sum_type cost,Fintype.sum_sigma (fun k : Spine N => cost (.inr k))]
  simp [cost,graph,smul_eq_mul]

theorem local_sum : (∑v,∑i,localWidth N v i)=(∑q,bits q)+2*∑e,N.width e := by
  have one (v) : (∑i,localWidth N v i)=∑ l : Fibre N v,width N l.val :=
    ((index N v).symm.sum_comp (fun l=>width N l.val))
  simp_rw [one]
  rw [←Fintype.sum_sigma' (fun v (l : Fibre N v) => width N l.val)]
  calc
    _ = ∑ e : Leg N, width N e := (Equiv.sigmaFiberEquiv (owner N)).sum_comp (width N)
    _ = _ := by
      rw [Fintype.sum_sum_type (width N),Fintype.sum_prod_type (fun p => width N (.inr p))]
      simp [width,two_mul,Finset.sum_add_distrib]

/-- Include the external boundary once. The right-hand side is exactly the
sum of the site-local bills which charged each old exterior leg. -/
theorem total_le : (∑e,(graph N).width e)+(∑q,bits q)≤
    ∑v,(count N v+2)*∑i,localWidth N v i := by
  rw [wires]
  have costs : (∑v,(count N v+2)*∑i,localWidth N v i)=
      (∑v,(count N v+1)*∑i,localWidth N v i)+(∑v,∑i,localWidth N v i) := by
    rw [←Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun v _=>by ring
  rw [costs,local_sum]
  omega

end
end Hierarchy.DescentPhysicalSplit

end OAI
