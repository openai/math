import OAI.Hierarchy.DescentTerminalGraphPositions

namespace OAI
/-! # Paid row volume from the actual terminal incidences -/

namespace Hierarchy.DescentTerminalGraphVolume
open Computability.BorderVNP.Crossing DescentTerminalGraphPositions DescentTerminalGraphRows DescentTerminalRecipeRows
open ThreeFlat.Routing
open scoped Classical BigOperators
noncomputable section

variable {D S p : ℕ} {P : Type} [Fintype P] {bits : P→ℕ} (G : Network D P bits)
abbrev Incidence := (v : G.Site) × DescentTerminalGraphRows.Part G p v
abbrev EdgeBundle := (e : G.Edge) × Fin (poolBatchCount (G.width e) p)
abbrev Exterior := (z : P) × Fin (poolBatchCount (bits z) p)

private def occurrence : Incidence (p:=p) G → (Bool×EdgeBundle (p:=p) G) ⊕ Exterior (p:=p) (bits:=bits)
  | ⟨v,.inl e,k⟩=>.inl (decide (G.src e.val≠v),⟨e.val,k⟩)
  | ⟨_,.inr z,k⟩=>.inr ⟨z.val,k⟩

private def restore : (Bool×EdgeBundle (p:=p) G) ⊕ Exterior (p:=p) (bits:=bits) → Incidence (p:=p) G
  | .inl (false,⟨e,k⟩)=>⟨G.src e,.inl ⟨e,.inl rfl⟩,k⟩
  | .inl (true,⟨e,k⟩)=>⟨G.dst e,.inl ⟨e,.inr rfl⟩,k⟩
  | .inr ⟨z,k⟩=>⟨G.attach z,.inr ⟨z,rfl⟩,k⟩

omit [Fintype P] in
private theorem restored : Function.LeftInverse (restore G) (occurrence (p:=p) G) := by
  rintro ⟨v,(⟨e,he⟩|⟨port,hp⟩),j⟩
  · by_cases h : G.src e=v
    · subst v;simp [occurrence,restore]
    · have hd := he.resolve_left h
      subst v;simp [occurrence,restore,h]
  · subst v;rfl

def bundleBudget := 2*(∑e,poolBatchCount (G.width e) p)+(∑z,poolBatchCount (bits z) p)

/-- Loops contribute one actual site incidence, even though the estimate
allows two endpoint appearances for every internal bundle. -/
theorem incidence_le : (∑v,arity G p v) ≤ bundleBudget (p:=p) G := by
  have h := Fintype.card_le_of_injective _ (restored (p:=p) G).injective
  simpa [Incidence,DescentTerminalGraphRows.Part,arity,EdgeBundle,Exterior,bundleBudget,Fintype.card_sigma] using h

variable {G} (order : Order G S p)

theorem source_budget (i : Fin S) : (∑g,(order.site i).size g) ≤ ∑v,(order.site i).arity v := by
  let src := (g : Fin (Fintype.card (order.Group i))) × Fin (order.size i g)
  let arg := (v : order.Nodes i) × DescentTerminalGraphRows.Part G p v.val
  have existsSrc (r : src) : ∃ u : arg,name G u.2=order.catalog i r := by
    obtain ⟨v,u,hu⟩ := (((order.inGroup i ((order.groups i).symm r.1)).symm r.2).property.1)
    exact ⟨⟨v,u⟩,hu⟩
  choose select present using existsSrc
  have inj : Function.Injective select := by
    intro x y h
    exact (order.catalog i).injective ((present x).symm.trans
      ((congrArg (fun u : arg=>name G u.2) h).trans (present y)))
  have injBound := Fintype.card_le_of_injective _ inj
  have targetSum : (∑v,(order.site i).arity v)=∑v : order.Nodes i,arity G p v.val :=
    (order.nodes i).symm.sum_comp (fun v=>arity G p v.val)
  rw [targetSum]
  change (∑g,order.size i g) ≤ ∑v : order.Nodes i,arity G p v.val
  simpa only [src,arg,Fintype.card_sigma,Fintype.card_fin,DescentTerminalGraphRows.Part,arity] using injBound

theorem total_arity : (∑i,∑v,(order.site i).arity v)=∑v,arity G p v := by
  calc
    _ = ∑i,∑v : order.Nodes i,arity G p v.val :=
      Finset.sum_congr rfl (fun i _=>(order.nodes i).symm.sum_comp _)
    _ = _ := Fintype.sum_fiberwise _ _

/-- The charge is linear in active bundle incidence divided by slots per
row, plus one padding term per nonempty neighbor/exterior group and two
rows per common position. -/
theorem paid_rows {q : ℕ} (slotPositive : 0<q) :
    (∑i,(order.site i).rows q)*q ≤ 3*bundleBudget (p:=p) G + ((∑i,(order.site i).groups)+2*S)*q := by
  have per (i : Fin S) : (order.site i).rows q*q ≤
      3*(∑v,(order.site i).arity v)+(order.site i).groups*q+2*q := by
    have b := (order.site i).rows_bound slotPositive
    have ls := source_budget order i
    omega
  have h := Finset.sum_le_sum (s:=Finset.univ) (fun i _=>per i)
  rw [←Finset.sum_mul] at h
  simp only [Finset.sum_add_distrib,←Finset.mul_sum,←Finset.sum_mul,Finset.sum_const,Finset.card_univ,
    Fintype.card_fin,nsmul_eq_mul,total_arity] at h
  have vol := incidence_le (p:=p) G
  calc
    _ ≤ _ := h
    _ ≤ _ := by nlinarith only [vol]

end
end Hierarchy.DescentTerminalGraphVolume

end OAI
