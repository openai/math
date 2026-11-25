import OAI.Computability.BorderVNP.PackedSubdivisionGateActive

/-! # Physical row order of original endpoint copies and inserted equality relays -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.Subdivision.Gates

open Crossing Shortening Shortening.PublicCapacity Placement
open scoped Classical

/-- First all cable-side candidates in old ID order, then ports, then the interior relay rectangle. -/
def ordinal {m np extra : ℕ} : Row m np extra ≃ Fin ((m*2+np)+m*extra) :=
  let side := ((Equiv.prodCongr (Equiv.refl (Fin m)) finTwoEquiv.symm).trans finProdFinEquiv)
  (((side.sumCongr (Equiv.refl (Fin np))).trans finSumFinEquiv).sumCongr finProdFinEquiv).trans finSumFinEquiv

/-- Source list in static physical rectangle order. -/
def selected {m np extra : ℕ} (keep : Row m np extra → Bool) : List (Row m np extra) :=
  ((List.finRange ((m*2+np)+m*extra)).filter fun i => keep (ordinal.symm i)).map ordinal.symm

variable {D np extra : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
    {s : Shape} (old : Rows s N) (portID : P ↪ Fin np)

/-- The publicly ordered nonempty old incidences, prior to encoding their strided copies. -/
noncomputable def oldRows (v : N.Site) : List (Placement.Row N v) :=
  (ordered N old.edge portID v).filter fun r => decide (0 < width N v r)

omit [Fintype P] in
private theorem increasing (v : N.Site) (a b : Placement.Row N v)
    (h : rowID N old.edge portID v a < rowID N old.edge portID v b) :
    ordinal (extra:=extra) (.inl (nameOld old portID v a)) < ordinal (.inl (nameOld old portID v b)) := by
  rcases a with e|p <;> rcases b with f|q
  · change (old.edge e.val).val < (old.edge f.val).val at h
    change (finTwoEquiv.symm (decide (N.src e.val=v))).val+2*(old.edge e.val).val <
      (finTwoEquiv.symm (decide (N.src f.val=v))).val+2*(old.edge f.val).val
    have := (finTwoEquiv.symm (decide (N.src e.val=v))).isLt
    omega
  · change (finTwoEquiv.symm (decide (N.src e.val=v))).val+2*(old.edge e.val).val < s.edges*2+(portID q.val).val
    have := (old.edge e.val).isLt
    have := (finTwoEquiv.symm (decide (N.src e.val=v))).isLt
    omega
  · change s.edges+(portID p.val).val < (old.edge f.val).val at h
    have := (old.edge f.val).isLt
    omega
  · change s.edges+(portID p.val).val < s.edges+(portID q.val).val at h
    change s.edges*2+(portID p.val).val < s.edges*2+(portID q.val).val
    omega

private theorem order_facts (v : N.Site) :
    (ordered N old.edge portID v).Nodup ∧
      (ordered N old.edge portID v).Pairwise (fun a b => rowID N old.edge portID v a < rowID N old.edge portID v b) ∧
      ∀ a : Placement.Row N v, a ∈ ordered N old.edge portID v := by
  let _ := LinearOrder.lift' (rowID N old.edge portID v) (rowID N old.edge portID v).injective
  exact ⟨Finset.sort_nodup ..,(Finset.sortedLT_sort (Finset.univ : Finset (Placement.Row N v))).pairwise,fun a => (Finset.mem_sort _).mpr (Finset.mem_univ a)⟩

/-- The finite source filter on a retained site gives the old endpoints in precisely
the stable sparse ID order used by its intrinsic copy program. -/
theorem selected_old (v : N.Site) (keep : Row s.edges np extra → Bool)
    (correct : ∀ t, keep t = true ↔ ∃ r : Placement.Row N v, 0 < width N v r ∧ .inl (nameOld old portID v r) = t) :
    selected keep = (oldRows old portID v).map (fun r => .inl (nameOld old portID v r)) := by
  let xs := (List.finRange ((s.edges*2+np)+s.edges*extra)).filter fun i => keep (ordinal.symm i)
  let ns := fun r : Placement.Row N v => (Sum.inl (nameOld old portID v r) : Row s.edges np extra)
  let f := ordinal ∘ ns
  obtain ⟨dup,order,all⟩ := order_facts old portID v
  have inject : Function.Injective f := fun _ _ h =>
    (nameOld old portID v).injective (Sum.inl.inj (ordinal.injective h))
  have mem (i) : i ∈ xs ↔ i ∈ (oldRows old portID v).map f := by
    simp only [xs,List.mem_filter,List.mem_finRange,true_and,correct,List.mem_map,oldRows,decide_eq_true_eq,all,true_and]
    constructor
    · rintro ⟨r,live,hr⟩
      exact ⟨r,live,(congrArg ordinal hr).trans (ordinal.apply_symm_apply i)⟩
    · rintro ⟨r,live,hr⟩
      exact ⟨r,live,((ordinal.symm_apply_apply (ns r)).symm.trans (congrArg ordinal.symm hr))⟩
  have perm := (List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _) ((dup.filter _).map inject)).mpr mem
  have first : (List.finRange ((s.edges*2+np)+s.edges*extra)).Pairwise (· ≤ ·) :=
    List.ofFn_id _ ▸ (monotone_id : Monotone (id : Fin ((s.edges*2+np)+s.edges*extra) → _)).sortedLE_ofFn.pairwise
  have last : ((oldRows old portID v).map f).Pairwise (· ≤ ·) :=
    List.Pairwise.map f (fun a b h => (increasing old portID v a b h).le) (order.filter _)
  have he : xs = (oldRows old portID v).map f := perm.eq_of_pairwise' (first.filter _) last
  change xs.map ordinal.symm = _
  rw [he,List.map_map]
  simp only [f,ns,Function.comp_def,Equiv.symm_apply_apply]

/-- A relay's unique marked candidate occupies one row independently of its two hop widths. -/
theorem selected_relay {m : ℕ} (keep : Row m np extra → Bool) (r : Row m np extra)
    (correct : ∀ t, keep t = true ↔ t = r) : selected keep = [r] := by
  let xs := (List.finRange ((m*2+np)+m*extra)).filter fun i => keep (ordinal.symm i)
  have mem (i) : i ∈ xs ↔ i ∈ [ordinal r] := by
    simp only [xs,List.mem_filter,List.mem_finRange,true_and,correct,List.mem_singleton]
    exact ordinal.symm_apply_eq
  have eqn := List.perm_singleton.mp
    ((List.perm_ext_iff_of_nodup ((List.nodup_finRange _).filter _) (List.nodup_singleton _)).mpr mem)
  change xs.map ordinal.symm = _
  change xs = [ordinal r] at eqn
  rw [eqn]
  simp

end Packing.Inherited.Subdivision.Gates

end BorderVNP
end Computability
end OAI
