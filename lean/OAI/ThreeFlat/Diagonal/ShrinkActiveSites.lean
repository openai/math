import OAI.ThreeFlat.Diagonal.CompressorLocalIncidence
import OAI.ThreeFlat.Diagonal.ShrinkOwnerKernel
import OAI.ThreeFlat.Diagonal.HistoryGroupedFactor

namespace OAI
/-! # Bounded local table of exactly the motifs occupied at a shrinking site -/

namespace ThreeFlat.Diagonal.CompressorPacking.Local

open Computability.VPVNP.Compression
open scoped Classical BigOperators

variable {V H Tag L : Type} {d c : ℕ} [AddCommGroup H] [AddCommGroup Tag] [AddCommGroup L]
  [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] [DecidableEq V] [DecidableEq Tag] [DecidableEq L]
  (P : PackingData V H Tag L d c) (layout : Bool) (v : Site V Tag L)

abbrev Slots (d c : ℕ) := Bool × Index d c

/-- Enumerate both endpoint choices at this actual lane, with a local test on
the six bounded parties of the resulting candidate. -/
def atSite (a : Slots d c) : Option P.Motif :=
  (lookup P a.1 v a.2).filter (fun m => decide (∃ j : Fin 6, partySite P layout m j = v))

omit [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] in
theorem atSite_some (a : Slots d c) (m : P.Motif) : atSite P layout v a = some m ↔
    lookup P a.1 v a.2 = some m ∧ ∃ j, partySite P layout m j = v := by
  simp [atSite]

omit [Fintype V] [Fintype H] [Fintype Tag] [Fintype L] in
/-- Every possible site role is A, B or D. The two possible placements in
the table include both A and B and also the layout chosen for D. -/
theorem atSite_covers (m : P.Motif) (yes : ∃ j, partySite P layout m j = v) :
    ∃ a, atSite P layout v a = some m := by
  obtain ⟨j,hj⟩ := yes
  have ha : ∃ a, lookup P false (P.roleA m) a = some m := by
    simpa only [P.placement_C_source] using covers_C P false m
  have hb : ∃ a, lookup P true (P.roleB m) a = some m := by
    simpa only [P.placement_C_target] using covers_C P true m
  have hd := covers_D P layout m
  have h : ∃ a : Slots d c, lookup P a.1 (partySite P layout m j) a.2 = some m := by
    unfold partySite
    generalize ShrinkMotif.role layout j = role
    fin_cases role
    · obtain ⟨a,h⟩ := ha; exact ⟨(false,a),h⟩
    · obtain ⟨a,h⟩ := hb; exact ⟨(true,a),h⟩
    · obtain ⟨a,h⟩ := hd; exact ⟨(layout,a),h⟩
  rw [hj] at h
  obtain ⟨a,h⟩ := h
  exact ⟨a,(atSite_some P layout v a m).2 ⟨h,j,hj⟩⟩

section
variable {B : ℕ} (ord : Fin B ≃ Slots d c)

/-- A candidate contributes its kernel only if this is its earliest local
slot. A duplicate check reads only a bounded prefix of the same table. -/
def First (i : Fin B) := ∃ m : P.Motif, atSite P layout v (ord i) = some m ∧
    ∀ j : Fin B, j < i → atSite P layout v (ord j) ≠ some m

private noncomputable def firstMotif (i : {i // First P layout v ord i}) : MotifKernel.Active (partySite P layout) v :=
  ⟨i.property.choose,((atSite_some P layout v (ord i.val) _).1 i.property.choose_spec.1).2⟩

/-- Canonical output rows are in bijection with the occupied motif set. -/
noncomputable def activeEquiv : {i // First P layout v ord i} ≃ MotifKernel.Active (partySite P layout) v :=
  Equiv.ofBijective (firstMotif P layout v ord) <| by
    constructor
    · intro a b eq
      apply Subtype.ext
      have same : a.property.choose = b.property.choose := congrArg Subtype.val eq
      rcases lt_trichotomy a.val b.val with h|h|h
      · exact False.elim (b.property.choose_spec.2 a.val h (a.property.choose_spec.1.trans (congrArg some same)))
      · exact h
      · exact False.elim (a.property.choose_spec.2 b.val h (b.property.choose_spec.1.trans (congrArg some same.symm)))
    · rintro ⟨m,hm⟩
      obtain ⟨a,ha⟩ := atSite_covers P layout v m hm
      let xs := Finset.univ.filter (fun i : Fin B => atSite P layout v (ord i) = some m)
      have live : xs.Nonempty := ⟨ord.symm a,by simp [xs,ha]⟩
      let i := xs.min' live
      have hi : atSite P layout v (ord i) = some m := (Finset.mem_filter.mp (xs.min'_mem live)).2
      have first : First P layout v ord i := ⟨m,hi,fun j hj h =>
        (not_le_of_gt hj) (xs.min'_le j (Finset.mem_filter.mpr ⟨Finset.mem_univ _,h⟩))⟩
      exact ⟨⟨i,first⟩,Subtype.ext (Option.some.inj (first.choose_spec.1.symm.trans hi))⟩

end

theorem slot_count : Fintype.card (Slots d c) = 8*d^2*2^c := by
  rw [Fintype.card_prod,Fintype.card_bool,index_count]
  ring

end ThreeFlat.Diagonal.CompressorPacking.Local

end OAI
