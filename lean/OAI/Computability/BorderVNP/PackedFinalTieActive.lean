import OAI.Computability.BorderVNP.PackedSubdivisionGateActive

/-! # Active rows and real owners of the final incidence-binding table

Every present cable or port contributes a record even when its word width is zero.
Only the duplicated destination of a self-loop is suppressed. The physical owner
of each surviving record is its final site's pointer, before cell grouping.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalTies

open Crossing Shortening.PublicCapacity Subdivision CellAddressCircuit ParseBatchSort
open scoped Classical

variable {ns m np C d k w : ℕ} {σ : Type*} (F : CellAddressCircuit.Fields ns m np C d k w σ)
variable (occupied : Fin m → σ) (portUsed : Fin np → Bool)

/-- The final row enable test on the physical directory, independently of its width. -/
noncomputable def enabled (x : σ → Bool) : Subdivision.Gates.Old m np → Bool
  | .inl (e,side) => x (occupied e) && (side || decide
      (value (x ∘ F.ptr (Layer.edgeEnd e true)) ≠ value (x ∘ F.ptr (Layer.edgeEnd e false))))
  | .inr u => portUsed u

/-- The actual sparse site code that owns the final absolute binding record. -/
def owner (x : σ → Bool) (r : Subdivision.Gates.Old m np) : ℕ := value (x ∘ F.ptr (Subdivision.Gates.oldEnd r))

/-- Present, nonduplicated physical row with a particular final-site pointer. -/
noncomputable def atKey (x : σ → Bool) (key : ℕ) (r : Subdivision.Gates.Old m np) : Bool :=
  enabled F occupied portUsed x r && decide (owner F x r = key)

variable {D : ℕ} {P : Type*} {bits : P → ℕ} {N : Network D P bits}
variable (rows : Rows ⟨ns,m⟩ N) (portID : P ↪ Fin np)
variable {x : σ → Bool} (data : Views.EndpointData N F rows.site rows.edge portID x)
variable (used : ∀ i, x (occupied i) = true ↔ i ∈ Set.range rows.edge)
variable (ports : ∀ i, portUsed i = true ↔ i ∈ Set.range portID)

include data in
/-- Every genuine physical row's owner bits are the actual final-site pointer. -/
theorem incidence_owner (v : N.Site) (r : Placement.Row N v) :
    owner F x (Subdivision.Gates.nameOld rows portID v r) = (F.sites (rows.site v)).val := by
  rcases r with e | p
  · change value (x ∘ F.ptr (Layer.edgeEnd (rows.edge e.val) (decide (N.src e.val=v)))) = _
    by_cases h : N.src e.val = v
    · rw [decide_eq_true h]
      exact (data.src e.val).trans (congrArg (fun u => (F.sites (rows.site u)).val) h)
    · rw [decide_eq_false h]
      exact (data.dst e.val).trans (congrArg (fun u => (F.sites (rows.site u)).val) (e.property.resolve_left h))
  · exact (data.attach p.val).trans (congrArg (fun u => (F.sites (rows.site u)).val) p.property)

include data used ports in
/-- True presence is exactly membership in the stable names of all real site incidences. -/
theorem enabled_iff (t : Subdivision.Gates.Old m np) :
    enabled F occupied portUsed x t = true ↔ ∃ v, ∃ r : Placement.Row N v, Subdivision.Gates.nameOld rows portID v r = t := by
  rcases t with ⟨i,side⟩ | i
  · simp only [enabled,Bool.and_eq_true,Bool.or_eq_true,decide_eq_true_eq,used]
    constructor
    · rintro ⟨⟨e,rfl⟩,hs⟩
      cases side
      · have diff := hs.resolve_left (by decide)
        have ne : N.src e ≠ N.dst e := fun eqn =>
          diff ((data.src e).trans ((congrArg (fun v => (F.sites (rows.site v)).val) eqn).trans (data.dst e).symm))
        refine ⟨N.dst e,.inl ⟨e,.inr rfl⟩,?_⟩
        change Sum.inl (rows.edge e,decide (N.src e=N.dst e)) = _
        rw [decide_eq_false ne]
      · refine ⟨N.src e,.inl ⟨e,.inl rfl⟩,?_⟩
        change Sum.inl (rows.edge e,decide (N.src e=N.src e)) = _
        simp
    · rintro ⟨v,e | p,h⟩
      · change Sum.inl (rows.edge e.val,decide (N.src e.val=v)) = Sum.inl (i,side) at h
        obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Sum.inl.inj h)
        refine ⟨⟨e.val,rfl⟩,?_⟩
        by_cases src : N.src e.val=v
        · exact .inl (decide_eq_true src)
        · refine .inr (fun eqn => src ?_)
          have same := (data.src e.val).symm.trans (eqn.trans (data.dst e.val))
          exact (rows.site.injective (F.sites.injective (Fin.ext same))).trans (e.property.resolve_left src)
      · cases h
  · change portUsed i = true ↔ _
    rw [ports]
    constructor
    · rintro ⟨u,rfl⟩
      exact ⟨N.attach u,.inr ⟨u,rfl⟩,rfl⟩
    · rintro ⟨v,e | p,h⟩
      · cases h
      · exact ⟨p.val,Sum.inr.inj h⟩

include data used ports in
/-- The stable physical owner test selects exactly the names incident to that site. -/
theorem atKey_iff (v : N.Site) (t : Subdivision.Gates.Old m np) :
    atKey F occupied portUsed x (F.sites (rows.site v)).val t = true ↔
      ∃ a, Subdivision.Gates.nameOld rows portID v a = t := by
  rw [atKey,Bool.and_eq_true,decide_eq_true_eq,enabled_iff F occupied portUsed rows portID data used ports]
  constructor
  · rintro ⟨⟨u,r,rfl⟩,key⟩
    obtain rfl := rows.site.injective (F.sites.injective (Fin.ext ((incidence_owner F rows portID data u r).symm.trans key)))
    exact ⟨r,rfl⟩
  · rintro ⟨r,rfl⟩
    exact ⟨⟨v,r,rfl⟩,incidence_owner F rows portID data v r⟩

end Packing.Inherited.FinalTies

end BorderVNP
end Computability
end OAI
