import OAI.Hierarchy.DescentSparseMatchedBins

namespace OAI
/-! # Exact correspondence of amounts and acceptance bits in sparse and full matching -/

noncomputable section
namespace Hierarchy.DescentPacking.SparseBinRAM.Aperture
open Sparse
open scoped Classical BigOperators
variable {I C : Type*} [Fintype C] [DecidableEq C] {S : Finset C} {M : ℕ}

theorem roster_nonempty (c : C) (S : Finset C) : Nonempty (Fin (roster S).length) := by
  have inside := mem_binOrder c
  cases seq : binOrder C with
  | nil => simp [seq] at inside
  | cons h t =>
    have hit : h∈keep S := by simp [keep,seq]
    have mem : h∈roster S := List.mem_filter.mpr ⟨by simp [seq],decide_eq_true hit⟩
    obtain ⟨i,_⟩ := List.mem_iff_get.mp mem
    exact ⟨i⟩

variable (A : Aperture S M) [Nonempty (Fin (roster S).length)]
variable (f : I→ℕ) (xs : List I) (cap : C→ℕ) (support : ∀v,0<cap v→v∈keep S)
local notation "short" => Packing.decisions (pack f xs (mass A cap))
local notation "full" => Packing.decisions (pack f xs cap)

omit [Nonempty (Fin (roster S).length)] in
theorem rows_length : (short).length=(full).length := by
  have l := congrArg List.length (pack f xs (A.mass cap)).order
  have r := congrArg List.length (pack f xs cap).order
  simpa only [List.length_map] using l.trans r.symm

private theorem mapped_get {α β : Type*} (g : α→β) {ys : List β} {zs : List α}
    (h : ys=zs.map g) (u : Fin ys.length) (v : Fin zs.length) (same : u.val=v.val) :
    ys.get u=g (zs.get v) := by
  subst ys
  rcases u with ⟨i,hi⟩
  rcases v with ⟨j,hj⟩
  change i=j at same
  subst j
  simp [List.get_eq_getElem]

include support in
/-- Both rows result from one ordered decision on the genuine reachable roster. -/
theorem source_row (i : Fin (short).length) (j : Fin (full).length) (same : i.val=j.val) :
    ∃v : I,∃z : Option (Fin (roster S).length),
      (short).get i=(v,z.map (padded A.capacity).slot) ∧ (full).get j=(v,z.map (dense S).name) := by
  let D := dense S
  let P := padded A.capacity
  let ds := (pack f xs (cap ∘ D.name)).decisions
  have a := P.decisions f xs _ _ (A.mass_correct cap)
  have b := D.decisions f xs cap support
  have size : (short).length=ds.length := by simpa [ds,D] using congrArg List.length a
  let t : Fin ds.length := ⟨i.val,i.isLt.trans_eq size⟩
  exact ⟨(ds.get t).1,(ds.get t).2,
    mapped_get P.put a i t rfl,
    mapped_get D.decode b.symm j t same.symm⟩

include support in
theorem aligned_totals (j : ℕ) :
    (∑i : Fin (short).length,if i.val<j then f ((short).get i).1 else 0)=
      (∑i : Fin (full).length,if i.val<j then f ((full).get i).1 else 0) ∧
    (∑i : Fin (short).length,if i.val<j ∧ ((short).get i).2.isSome then f ((short).get i).1 else 0)=
      ∑i : Fin (full).length,if i.val<j ∧ ((full).get i).2.isSome then f ((full).get i).1 else 0 := by
  let e := finCongr (A.rows_length f xs cap)
  constructor
  · apply Fintype.sum_equiv e
    intro i
    obtain ⟨x,z,l,r⟩ := A.source_row f xs cap support i (e i) rfl
    simp only [l,r]
    rfl
  · apply Fintype.sum_equiv e
    intro i
    obtain ⟨x,z,l,r⟩ := A.source_row f xs cap support i (e i) rfl
    cases z <;> simp only [l,r,Option.map_none,Option.map_some,Option.isSome_none,Option.isSome_some] <;> rfl

omit [Nonempty (Fin (roster S).length)] in
theorem numeric_slot (a : Fin (roster S).length) :
    (Fintype.equivFin (Fin M) ((padded A.capacity).slot a)).val=(coordinate S a).val := by
  change (position M ((padded A.capacity).slot a)).val=_
  simp [padded,padSlot,coordinate,position]


end Hierarchy.DescentPacking.SparseBinRAM.Aperture

end
end OAI
