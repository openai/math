import OAI.Computability.BorderVNP.FiniteSewnFieldRuns

/-! # Maximal exterior staging intervals fit any genuine interval cover

Each physical row translates one old interval with a fixed displacement
or pins the entire interval to zero. It can therefore contain the final
lane of at most one maximal run of the actual partial source map.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.SewnField

open scoped Classical
open private start slope runStart interval from OAI.Computability.BorderVNP.FiniteSewnFieldRuns

private theorem cover_label {old next : ℕ} {read : Fin old → Option (Fin next)} {runs : List Interval}
    (cover : Covers runs read) (p : Interval) (hp : p ∈ runs) (k : Fin old)
    (h₁ : p.oldStart ≤ k.val) (h₂ : k.val < p.oldStart+p.width) :
    slope read k.val = p.source.map (fun j => (j : ℤ)-p.oldStart) := by
  have h := cover.agrees p hp (k.val-p.oldStart) (by omega) k (Nat.add_sub_of_le h₁).symm
  change (if h : k.val < old then (read ⟨k.val,h⟩).map (fun j => (j.val : ℤ)-k.val) else none) = _
  rw [dite_eq_left k.isLt]
  cases a : read k <;> cases b : p.source <;> simp_all
  omega

private theorem start_eq_of_constant {α : Type*} [DecidableEq α] (label : ℕ → α) (i j : ℕ) (hij : i ≤ j)
    (same : ∀ k, i ≤ k → k ≤ j → label k = label i) : start label j = start label i := by
  induction j, hij using Nat.le_induction with
  | base => rfl
  | succ j hij ih =>
    have h : label (j+1) = label j := (same _ (by omega) le_rfl).trans (same _ hij (by omega)).symm
    rw [start,ite_eq_left h]
    exact ih fun k hl hr => same k hl (by omega)

/-- The canonical zero/equality rows never exceed the size of any physical
interval description covering the same partial source map. -/
theorem intervals_length_le {old next : ℕ} (read : Fin old → Option (Fin next)) (runs : List Interval)
    (cover : Covers runs read) : (intervals read).length ≤ runs.length := by
  let ends := Finset.univ.filter (fun k : Fin old => ∀ j : Fin old, runStart read j = runStart read k → j ≤ k)
  have existsRow (k : Fin old) : ∃ a : Fin runs.length,
      (runs.get a).oldStart ≤ k.val ∧ k.val < (runs.get a).oldStart+(runs.get a).width := by
    obtain ⟨p,hp,i,hi,hk⟩ := cover.covers k
    obtain ⟨a,ha⟩ := List.mem_iff_get.mp hp
    exact ⟨a,ha ▸ by omega⟩
  let assign (k : ↥ends) := (existsRow k.val).choose
  have bound (k : ↥ends) := (existsRow k.val).choose_spec
  have inj : Function.Injective assign := by
    intro a b h
    have ha := bound a
    have hb := bound b
    change (runs.get (assign a)).oldStart ≤ a.val.val ∧ a.val.val < (runs.get (assign a)).oldStart+(runs.get (assign a)).width at ha
    change (runs.get (assign b)).oldStart ≤ b.val.val ∧ b.val.val < (runs.get (assign b)).oldStart+(runs.get (assign b)).width at hb
    rw [h] at ha
    let row := runs.get (assign b)
    have mem : row ∈ runs := List.get_mem ..
    have same {i j : Fin old} (ij : i ≤ j) (ilo : row.oldStart ≤ i.val) (jhi : j.val < row.oldStart+row.width) :
        runStart read j = runStart read i := by
      apply Fin.ext
      apply start_eq_of_constant _ _ _ ij
      intro k hl hr
      let t : Fin old := ⟨k,hr.trans_lt j.isLt⟩
      exact (cover_label cover row mem t (by dsimp [t]; omega) (by dsimp [t]; omega)).trans
        (cover_label cover row mem i ilo (by omega)).symm
    have equal : runStart read a.val = runStart read b.val := by
      rcases le_total a.val b.val with h₁ | h₂
      · exact (same h₁ ha.1 hb.2).symm
      · exact same h₂ hb.1 ha.2
    have aMax := (Finset.mem_filter.mp a.property).2
    have bMax := (Finset.mem_filter.mp b.property).2
    exact Subtype.ext (le_antisymm (bMax a.val equal) (aMax b.val equal.symm))
  change (ends.sort.map (interval read)).length ≤ runs.length
  rw [List.length_map,Finset.length_sort,← Fintype.card_coe]
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective assign inj

end Packing.SewnField

end BorderVNP
end Computability
end OAI
