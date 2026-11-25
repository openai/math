import OAI.Computability.VPVNP.RAMFinite
import OAI.ThreeFlat.Diagonal.TraceAdjacent
import OAI.ThreeFlat.Diagonal.TraceBankExecution
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.List.OfFn

namespace OAI
/-! # Weighted counting by locally certified register and sorted-memory rows -/

namespace ThreeFlat.Diagonal.TraceRows

open Computability.VPVNP.BurstRAM
open Computability.VPVNP.RAMMemory
open TraceBanks

deriving instance Fintype for Row
deriving instance Fintype for TraceBanks.Snapshot

variable {F C : Type*} {w p r k : ℕ}

private theorem ofFn_of_length {α : Type*} (xs : List α) {n : ℕ} (h : xs.length = n) :
    ∃ rows : Fin n → α, List.ofFn rows = xs := by
  subst n
  exact ⟨xs.get, List.ofFn_get xs⟩

def verified (P : Program w C) (c : C) (S d : ℕ) (header : ℕ → Word w) (xs : List (Row w C)) : Prop :=
  before (xs.headD .pad) = some c ∧ pairs P xs ∧
    PaddedCheck none (TraceRecordSort.sorted S d header (report xs).events)

private theorem verified_iff (P : Program w C) (c : C) (S d : ℕ) (header : ℕ → Word w)
    (xs : List (Row w C)) (fits : S + xs.length ≤ 2 ^ d) :
    verified P c S d header xs ↔ Local P c xs ∧ Correct (initialMemory S header) (report xs).events := by
  rw [verified, ← and_assoc, ← local_iff_pairs]
  apply and_congr_right
  intro hl
  apply TraceRecordSort.sorted_iff_correct
  have hh := (local_spec hl).1.length_lt
  omega

noncomputable def rowWeight [Semiring F] (code : RAM.FieldCode F w)
    (P : Program w C) (c : C) (S d : ℕ) (header : ℕ → Word w) (xs : List (Row w C)) : F := by
  classical
  exact if verified P c S d header xs then code.terminal (report xs).result else 0

/-- The physical CPU checks and the adjacent sorted-memory checks reproduce
the weighted sum of accepting machine branches, including their actual
terminal scalars. -/
theorem mass_eq_checked_rows [Semiring F] [Fintype C] (code : RAM.FieldCode F w)
    (P : Program w C) (c : C) (S d f : ℕ) (header : ℕ → Word w) (fits : S + f ≤ 2 ^ d) :
    RAM.mass code P f c (initialMemory S header) =
      ∑ rows : Fin f → Row w C, rowWeight code P c S d header (List.ofFn rows) := by
  classical
  let m := initialMemory S header
  let valid (xs : Fin f → Row w C) := verified P c S d header (List.ofFn xs)
  have vh (xs : Fin f → Row w C) := verified_iff P c S d header (List.ofFn xs) (by simpa using fits)
  change RAM.mass code P f c m = _
  rw [RAM.mass_eq_sum_reports, ← List.sum_toFinset _ (RAM.reports_nodup P f c m)]
  trans ∑ rows ∈ Finset.univ.filter valid, code.terminal (report (List.ofFn rows)).result
  · symm
    apply Finset.sum_bij (fun rows _ => report (List.ofFn rows))
    · intro xs hx
      obtain ⟨hl,hc⟩ := (vh xs).mp (Finset.mem_filter.mp hx).2
      apply List.mem_toFinset.mpr
      apply (RAM.mem_reports_iff ..).mpr
      exact ⟨by simpa using (local_spec hl).1, hc⟩
    · intro xs hx ys hy he
      have gx := (local_spec ((vh xs).mp (Finset.mem_filter.mp hx).2).1).2
      have gy := (local_spec ((vh ys).mp (Finset.mem_filter.mp hy).2).1).2
      simp only [List.length_ofFn] at gx gy
      rw [he] at gx
      exact List.ofFn_injective (gx.symm.trans gy)
    · intro rep hrep
      obtain ⟨hg,hc⟩ := (RAM.mem_reports_iff ..).mp (List.mem_toFinset.mp hrep)
      obtain ⟨hh,hl,hr⟩ := render_spec hg
      obtain ⟨xs,hxs⟩ := ofFn_of_length _ hh
      refine ⟨xs, Finset.mem_filter.mpr ⟨Finset.mem_univ _, (vh xs).mpr ?_⟩, ?_⟩
      · rw [hxs]
        exact ⟨hl, by simpa [hr] using hc⟩
      · rw [hxs, hr]
    · intros
      rfl
  · rw [Finset.sum_filter]
    apply Finset.sum_congr rfl
    intro xs _
    simp only [valid, rowWeight]

/-- Put the initialized header in the external half of the tagged memory. -/
theorem inputBank_initialMemory (S : ℕ) (header : ℕ → Word w) (hs : S ≤ 2 ^ w) :
    inputBank (initialMemory S header) = initialMemory S (fun i => wide (header i)) := by
  funext i
  by_cases hi : i < S
  · simp [initialMemory, inputBank, hi, lt_of_lt_of_le hi hs]
  · by_cases hj : i < 2 ^ w <;> simp [initialMemory, inputBank, hi, hj, wide]

/-- Native RAM value with the weighted finite row sum used by the compiled
trace. Every private-memory access has its own tagged sorting slot. -/
theorem value_eq_checked_rows [Semiring F] (code : RAM.FieldCode F w)
    (M : PrivateRAM.Machine w p r k) (s : Word w) (S d f : ℕ) (header : ℕ → Word w)
    (hs : S ≤ 2 ^ w) (fits : S + f ≤ 2 ^ d) :
    RAM.value code M f s (initialMemory S header) =
      ∑ rows : Fin f → Row (w+1) (Snapshot w p r), rowWeight (wideCode code) (exposed M)
        ((exposed M).start (wide s)) S d (fun i => wide (header i)) (List.ofFn rows) := by
  rw [value_eq_exposed, inputBank_initialMemory S header hs]
  exact mass_eq_checked_rows _ _ _ _ _ _ _ fits

end ThreeFlat.Diagonal.TraceRows

end OAI
