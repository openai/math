import OAI.Computability.BorderVNP.PackedSubdivisionGateFields
import OAI.Computability.BorderVNP.PackedSubdivisionGateNames

/-! # Exact live row names of the physical subdivision frame -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision.Gates

open Crossing Shortening Shortening.PublicCapacity ParseBatchSort VPVNP.VerifierNetwork
open scoped Classical

variable {D np extra : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
    {s : Shape} (old : Rows s N) (portID : P ↪ Fin np)

/-- Public slot of one old whole-word copy, using the unique source-side slot for an old loop. -/
noncomputable def nameOld (v : N.Site) : Placement.Row N v ↪ Old s.edges np where
  toFun
    | .inl z => .inl (old.edge z.val,decide (N.src z.val=v))
    | .inr p => .inr (portID p.val)
  inj' := by
    rintro (e | p) (f | q) h
    · exact congrArg Sum.inl (Subtype.ext (old.edge.injective (congrArg Prod.fst (Sum.inl.inj h))))
    · contradiction
    · contradiction
    · exact congrArg Sum.inr (Subtype.ext (portID.injective (Sum.inr.inj h)))

omit [Fintype P] in
/-- A present old endpoint candidate belongs to precisely its incident site. -/
theorem nameOld_site {v u : N.Site} (r : Placement.Row N v) (t : Placement.Row N u)
    (h : nameOld old portID v r = nameOld old portID u t) : v = u := by
  rcases r with e | p <;> rcases t with f | q
  · obtain ⟨he,side⟩ := Prod.mk.inj (Sum.inl.inj h)
    have eqn : e.val = f.val := old.edge.injective he
    by_cases hs : N.src e.val = v
    · have hu : N.src f.val = u := of_decide_eq_true (side.symm.trans (decide_eq_true hs))
      exact hs.symm.trans ((congrArg N.src eqn).trans hu)
    · have hu : N.src f.val ≠ u := of_decide_eq_false (side.symm.trans (decide_eq_false hs))
      exact (e.property.resolve_left hs).symm.trans ((congrArg N.dst eqn).trans (f.property.resolve_left hu))
  · contradiction
  · contradiction
  · exact p.property.symm.trans ((congrArg N.attach (portID.injective (Sum.inr.inj h))).trans q.property)

variable {C C' d d' k k' w : ℕ} {σ : Type*} [Fintype σ]
variable (oldF : CellAddressCircuit.Fields s.sites s.edges np C d k w σ)
variable (newF : CellAddressCircuit.Fields (s.sites+extra*s.edges) ((extra+1)*s.edges) np C' d' k' w σ)
variable (work extent : Fin s.sites → Fin w → σ) (present : Fin ((extra+1)*s.edges) → σ)
variable {x : σ → Bool} (oldData : Views.EndpointData N oldF old.site old.edge portID x)

local notation3 "input" => inputs oldF newF work extent present

private theorem active_old (r : Old s.edges np) :
    (input).eval x (.inl r,.inl ()) = true ↔
      r.elim (fun p => 0 < value (x ∘ oldF.edgeWidth p.1) ∧ (p.2=true ∨
        value (x ∘ oldF.ptr (Layer.edgeEnd p.1 true)) ≠ value (x ∘ oldF.ptr (Layer.edgeEnd p.1 false))))
        (fun p => 0 < value (x ∘ oldF.portWidth p)) := by
  rw [inputs,Frame.subst_eval,source_enable]
  cases r <;> simp [widthPins,tableFields,table,Function.comp_def]

include oldData in
/-- There are no spurious old commands. Every enabled candidate is the unique
stable name of a true nonempty old incidence, and every such incidence is enabled. -/
theorem old_enabled_iff (a : Old s.edges np) :
    (input).eval x (.inl a,.inl ()) = true ↔
      ∃ v, ∃ r : Placement.Row N v, 0 < Placement.width N v r ∧ nameOld old portID v r = a := by
  rw [active_old oldF newF work extent present]
  constructor
  · intro live
    rcases a with ⟨i,side⟩ | i
    · obtain ⟨hw,hs⟩ := live
      obtain ⟨e,rfl⟩ : i ∈ Set.range old.edge := by
        by_contra h
        exact (Nat.ne_of_gt hw) (oldData.edgeHole i h)
      have width : 0 < N.width e := (oldData.edge e) ▸ hw
      cases side with
      | true =>
        exact ⟨N.src e,.inl ⟨e,.inl rfl⟩,width,by change Sum.inl (old.edge e,decide (N.src e=N.src e)) = _; simp⟩
      | false =>
        have diff := hs.resolve_left (by simp)
        have ne : N.src e ≠ N.dst e := by
          intro same
          exact diff ((oldData.src e).trans ((congrArg (fun v => (oldF.sites (old.site v)).val) same).trans (oldData.dst e).symm))
        exact ⟨N.dst e,.inl ⟨e,.inr rfl⟩,width,by change Sum.inl (old.edge e,decide (N.src e=N.dst e)) = _; rw [decide_eq_false ne]⟩
    · obtain ⟨p,rfl⟩ : i ∈ Set.range portID := by
        by_contra h
        exact (Nat.ne_of_gt live) (oldData.portHole i h)
      refine ⟨N.attach p,.inr ⟨p,rfl⟩,?_,rfl⟩
      change 0 < value (x ∘ oldF.portWidth (portID p)) at live
      exact live.trans_eq (oldData.port p)
  · rintro ⟨v,(e|p),hw,rfl⟩
    · change 0 < value (x ∘ oldF.edgeWidth (old.edge e.val)) ∧ _
      refine ⟨(oldData.edge e.val).symm ▸ hw,?_⟩
      by_cases h : N.src e.val=v
      · exact Or.inl (decide_eq_true h)
      · refine Or.inr (fun eqn => h ?_)
        change value (x ∘ oldF.ptr (Layer.edgeEnd (old.edge e.val) true)) =
          value (x ∘ oldF.ptr (Layer.edgeEnd (old.edge e.val) false)) at eqn
        have same := (oldData.src e.val).symm.trans (eqn.trans (oldData.dst e.val))
        exact (old.site.injective (oldF.sites.injective (Fin.ext same))).trans (e.property.resolve_left h)
    · change 0 < value (x ∘ oldF.portWidth (portID p.val))
      exact hw.trans_eq (oldData.port p.val).symm

variable (route : N.WireRoutes) (fit : ∀ e, route.interior e ≤ extra)
variable (live : ∀ i, x (present i) = true ↔ i ∈ Set.range (old.subdivide route extra fit).edge)
omit [Fintype P] in
include live in
/-- Every occupied new equality site produces its single relay command, with no
row at an unused position of a short or entirely absent stripe. -/
theorem relay_enabled_iff (i : Fin s.edges) (j : Fin extra) :
    (input).eval x (.inr (i,j),.inl ()) = true ↔
      ∃ e, old.edge e = i ∧ j.val < route.interior e := by
  rw [inputs,Frame.subst_eval,source_enable]
  simp only [tableFields,table,Frame.withInput_eval_inl,Sum.elim_inr]
  exact (live (hop i j.succ)).trans (relay_live_iff old route fit i j)

end Packing.Inherited.Subdivision.Gates

end BorderVNP
end Computability
end OAI
