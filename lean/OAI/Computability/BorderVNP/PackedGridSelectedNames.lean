import OAI.Computability.BorderVNP.PackedBottomNativeNames

/-! # Selected wires and named choices on the physical grid

Each unary descriptor contributes its source name and its actual fine-wire
address at the same ordinal. Reading the stored fine assignment at this
address recovers the source's value in the chosen hidden grid assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports

open Crossing CellSparse

private def selectedEntries (fs : List Factor) : List (ℕ × Port) :=
  fs.filterMap fun f => match f with | .unary k tag => some (k,tag) | _ => none

private theorem selectedEntries_wires (fs : List Factor) : (selectedEntries fs).map Prod.fst = selectedWires fs := by
  induction fs with
  | nil => rfl
  | cons f fs ih => cases f <;> simp [selectedEntries,selectedWires] at * <;> assumption

private theorem selectedEntries_tags (next : ℕ) (fs : List Factor) :
    (selectedEntries fs).map Prod.snd = (sidecar next fs).map Prod.fst := by
  induction fs generalizing next with
  | nil => rfl
  | cons f fs ih => cases f <;> simp [selectedEntries,sidecar] at * <;> apply ih

/-- The selected wire at a native ordinal belongs to the very same original
unary factor as the source tag at that ordinal. -/
theorem selected_entry (next : ℕ) (fs : List Factor) (r : Fin (sidecar next fs).length) :
    Factor.unary ((selectedWires fs)[r.val]'(by simpa using r.isLt)) ((sidecar next fs).get r).1 ∈ fs := by
  have ht := selectedEntries_tags next fs
  have hw := selectedEntries_wires fs
  have len := congrArg List.length ht
  simp only [List.length_map] at len
  let i : Fin (selectedEntries fs).length := ⟨r.val,by rw [len]; exact r.isLt⟩
  have hval (k : ℕ) {T : Type} (a b : List T) (he : a = b) (h : k < a.length) :
      a[k] = b[k]'(he ▸ h) := by subst b; rfl
  have hk := hval r.val _ _ hw (by simpa only [List.length_map] using i.isLt)
  have hn := hval r.val _ _ ht (by simpa only [List.length_map] using i.isLt)
  simp only [List.getElem_map] at hk hn
  obtain ⟨f,hf,hfe⟩ := List.mem_filterMap.mp (List.get_mem (selectedEntries fs) i)
  cases f with
  | truth | sign | gadget => cases hfe
  | unary w tag =>
    have he : (w,tag) = (selectedEntries fs).get i := Option.some.inj hfe
    have hew := (congrArg Prod.fst he).trans hk
    have het := (congrArg Prod.snd he).trans hn
    simpa only [← hew,List.get_eq_getElem,← het] using hf

end Packing.BottomReports

namespace Packing.GridBoxes

open Crossing CellSparse BottomReports Diagonal.CellEntries
open scoped Classical

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable (rules : ∀ v, Rule N v)
variable {C Q : Type} [Fintype C] [DecidableEq C] (cell : N.Site → C)
variable (position : C → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
variable (hidden : ∀ c, N.InsideAssignment cell c) {src dst : Q → C} {H : ℕ}
variable (pack : (N.cellNetwork cell position).ChannelPacking src dst H)
variable {s m n : ℕ} (siteID : N.Site ↪ Fin s) (edges : N.Edge ↪ Fin m) (ports : P ↪ Fin n)

private theorem read_selected (c : C) (u : {v : N.Site // cell v = c}) (l : CellBox.Lane N u.val) (tag : Port)
    (isUnary : rules u.val = .unary l tag) (a x) (bank : ℕ → Bool) (off copy : ℕ)
    (aligned : ∀ k, bank (off+k.val) = physicalBits cell position hidden pack edges ports c a x k) :
    bank (off+(lane N cell c edges ports u l).val) =
      cellRead cell position hidden pack (sourceBit rules) c u a x := by
  let probe (w : N.Site) : Rule N w :=
    if h : u.val = w then h ▸ (Rule.truth (N := N) (v := u.val) (fun read => read l)) else .truth (fun _ => false)
  have hu : probe u.val = .truth (fun read => read l) := by simp [probe]
  calc
    _ = accepts N cell c edges ports u bank off copy (probe u.val) := by rw [hu]; rfl
    _ = cellRead cell position hidden pack (guard probe (fun p => bank (p.atBit copy 0))) c u a x :=
      accepts_cellRead cell position hidden pack edges ports probe c u a x bank off copy aligned
    _ = _ := by
      unfold cellRead fineFactor guard sourceBit
      rw [hu,isUnary]
      rfl

variable (c : C)
local notation "original" => factors N cell c siteID edges ports (fun v => rules (Subtype.val v))
variable (unique : ∀ u v p, ruleTag (rules u) = some p → ruleTag (rules v) = some p → u = v)
include unique

/-- At each stored row, a typed bundle's exact use bit is the named source bit
of the chosen hidden and supplied grid assignment. -/
theorem physicalBundle_trueReport (h : BundleHeader) (body : List Factor) (bank : ℕ → Bool)
    (i : Fin h.copies) (r : Fin (sidecar h.orig original).length) (a x)
    (aligned : ∀ k, bank (h.boxBase+i.val*h.stride+k.val) = physicalBits cell position hidden pack edges ports c a x k) :
    (physicalBundle h body original bank).uses
      (finProdFinEquiv (⟨r.val,by simpa [physicalBundle] using r.isLt⟩,i)) =
      trueReports rules cell position hidden pack c a x ((sidecar h.orig original).get r).1 := by
  let tag := ((sidecar h.orig original).get r).1
  let w := (selectedWires original)[r.val]'(by simpa using r.isLt)
  obtain ⟨u,_,hu⟩ := List.mem_map.mp (selected_entry h.orig original r)
  change ruleFactor N cell c edges ports u (Fintype.equivFin _) (rules u.val) = .unary w tag at hu
  cases hr : rules u.val with
  | truth f => simp only [hr,ruleFactor,reduceCtorEq] at hu
  | unary l t =>
    simp only [hr,ruleFactor,Factor.unary.injEq] at hu
    have htag : ruleTag (rules u.val) = some tag := by rw [hr]; exact congrArg some hu.2
    let pos : Fin (positions h.orig original).length := ⟨r.val,by simpa using r.isLt⟩
    apply (physicalBundle_use h body original bank pos i).trans
    rw [trueReports_at rules cell position hidden pack unique c u a x tag htag]
    change bank (h.boxBase+i.val*h.stride+w) = _
    rw [← hu.1]
    exact read_selected rules cell position hidden pack edges ports c u l t hr a x bank _ i.val aligned

/-- The native name resolver and the grid report function agree on all tags.
An absent name gives false in both representations. -/
theorem bundleUse_trueReports (h : BundleHeader) (body : List Factor) (bank : ℕ → Bool) (i : Fin h.copies)
    (distinct : ((sidecar h.orig original).map Prod.fst).Nodup) (a x)
    (aligned : ∀ k, bank (h.boxBase+i.val*h.stride+k.val) = physicalBits cell position hidden pack edges ports c a x k) :
    bundleUse h body original bank i = trueReports rules cell position hidden pack c a x := by
  funext tag
  by_cases hm : tag ∈ (sidecar h.orig original).map Prod.fst
  · obtain ⟨p,hp,rfl⟩ := List.mem_map.mp hm
    obtain ⟨r,rfl⟩ := List.mem_iff_get.mp hp
    exact (bundleUse_row h body original bank i distinct r).trans
      (physicalBundle_trueReport rules cell position hidden pack siteID edges ports c unique h body bank i r a x aligned)
  · have absent : ¬ ∃ u : {v : N.Site // cell v = c},ruleTag (rules u.val) = some tag := by
      rintro ⟨u,hu⟩
      apply hm
      rw [sidecar_tags]
      exact List.mem_filterMap.mpr ⟨ruleFactor N cell c edges ports u (Fintype.equivFin _) (rules u.val),
        List.mem_map.mpr ⟨u,mem_siteList ..,rfl⟩,(factorTag_rule ..).trans hu⟩
    rw [bundleUse,resolve,dite_eq_right hm,trueReports,dite_eq_right absent]

end Packing.GridBoxes

end BorderVNP
end Computability
end OAI
