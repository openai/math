import OAI.Computability.BorderVNP.CellProfileAux
import OAI.Computability.BorderVNP.CellSparseFactorCode
import Mathlib.Data.List.TakeDrop

/-!
# Exact private counts of selected gadget positions

The cell counts every selected gadget ID over all physical factor occurrences.
The tally uses one flag for every prefix and candidate count and checks the
reported binary count against the active final flag. All slots in the guessed
square are forced by the original factor assignments.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse.Gadget

/-- The indicator of selecting this ID at an actual occurrence. -/
def matchAt (D : Directory) (id : ℕ) (bank : ℕ → Bool) (i : ℕ) : Bool :=
  (D.occurrences[i]?).any (selected id bank)

/-- A prefix of the tally is exactly the number of selected occurrences in the list prefix. -/
theorem count_prefix (D : Directory) (id : ℕ) (bank : ℕ → Bool) {n : ℕ} (hn : n ≤ D.occurrences.length) :
    Prefix.count (matchAt D id bank) n =
      ((D.occurrences.take n).map (selected id bank)).count true := by
  induction n with
  | zero => rfl
  | succ n ih =>
    have hn' : n < D.occurrences.length := hn
    rw [Prefix.count, ih hn'.le, ← List.take_concat_get' D.occurrences n hn']
    simp only [List.map_append, List.map_singleton, List.count_append, matchAt, List.getElem?_eq_getElem hn',
      Option.any_some]
    cases selected id bank D.occurrences[n] <;> simp

/-- The final counter is the count in the original ordered occurrence scan. -/
theorem count_matches (D : Directory) (id : ℕ) (bank : ℕ → Bool) :
    Prefix.count (matchAt D id bank) D.occurrences.length =
      (D.occurrences.map (selected id bank)).count true := by
  simpa using count_prefix D id bank le_rfl

/-- Initialization, prefix transitions, and the reported multiplicity at the sole active final
flag. The data bank begins at `off` behind the allocated flags. -/
def Accept (cap off : ℕ) (bits : List ℕ) (id : ℕ) (D : Directory) (b : ℕ → Bool) : Prop :=
  Prefix.Valid cap cap (matchAt D id (Profile.data off b)) (fun i k => b (Prefix.address 0 cap i k)) ∧
    ∀ k ≤ cap, b (Prefix.address 0 cap cap k) = true → word (Profile.data off b) bits = k

/-- The tally checker fixes every flag and compares the supplied count to its true value. -/
theorem accept_iff (cap off : ℕ) (bits : List ℕ) (id : ℕ) (D : Directory) (b : ℕ → Bool) :
    Accept cap off bits id D b ↔
      word (Profile.data off b) bits = Prefix.count (matchAt D id (Profile.data off b)) cap ∧
      ∀ i ≤ cap, ∀ k ≤ cap, b (Prefix.address 0 cap i k) =
        decide (Prefix.count (matchAt D id (Profile.data off b)) i = k) := by
  let m := matchAt D id (Profile.data off b)
  rw [Accept, Prefix.valid_iff]
  constructor
  · rintro ⟨h, final⟩
    have hc := Prefix.count_le m cap
    exact ⟨final (Prefix.count m cap) hc (by rw [h cap le_rfl _ hc]; simp [m]), h⟩
  · rintro ⟨h, flags⟩
    refine ⟨flags, fun k hk hf => ?_⟩
    rw [flags cap le_rfl k hk, decide_eq_true_eq] at hf
    exact h.trans hf

/-- Physical row-major index of each flag in the square. -/
theorem flagAddress (cap : ℕ) (i k : Fin (cap+1)) :
    Prefix.address 0 cap i k = (finProdFinEquiv (i,k)).val := by
  change 0 + i.val * (cap+1) + k.val = k.val + (cap+1) * i.val
  ring

/-- The unique exhaustive physical bit vector of gadget-prefix flags. -/
def canonicalAux (D : Directory) (id : ℕ) (bank : ℕ → Bool)
    (q : Fin ((D.occurrences.length+1)*(D.occurrences.length+1))) : Bool :=
  let cap := D.occurrences.length
  let z := (finProdFinEquiv (m := cap+1) (n := cap+1)).symm q
  decide (Prefix.count (matchAt D id bank) z.1.val = z.2.val)

private theorem canonicalAux_at (D : Directory) (id : ℕ) (bank : ℕ → Bool)
    (i k : Fin (D.occurrences.length + 1)) :
    canonicalAux D id bank (finProdFinEquiv (i,k)) = decide (Prefix.count (matchAt D id bank) i = k) := by
  exact congrArg (fun z : Fin (D.occurrences.length+1) × Fin (D.occurrences.length+1) =>
    decide (Prefix.count (matchAt D id bank) z.1.val = z.2.val)) (finProdFinEquiv.symm_apply_apply (i,k))

/-- Reading the prepended square agrees with the original wire assignment after it.
The report passes precisely when it is the selected count, with exactly one full
auxiliary vector. -/
theorem accept_stack_iff (D : Directory) (id : ℕ) (bits : List ℕ) (v : List Bool)
    (x : Fin ((D.occurrences.length+1)*(D.occurrences.length+1)) → Bool) :
    let cap := D.occurrences.length
    Accept cap ((cap+1)*(cap+1)) bits id D (lookup (List.ofFn x ++ v)) ↔
      word (lookup v) bits = (D.occurrences.map (selected id (lookup v))).count true ∧
        x = canonicalAux D id (lookup v) := by
  let cap := D.occurrences.length
  let b := lookup (List.ofFn x ++ v)
  have hd : Profile.data ((cap+1)*(cap+1)) b = lookup v := funext (lookup_after_prefix x v)
  have hg (i k : Fin (cap+1)) : b (Prefix.address 0 cap i k) = x (finProdFinEquiv (i,k)) := by
    rw [flagAddress]
    exact lookup_prefix x v _
  change Accept cap ((cap+1)*(cap+1)) bits id D b ↔ _
  rw [accept_iff, hd, count_matches]
  apply and_congr_right
  intro _
  constructor
  · intro h
    funext q
    obtain ⟨⟨i,k⟩, rfl⟩ := (finProdFinEquiv (m := cap+1) (n := cap+1)).surjective q
    rw [canonicalAux_at, ← hg]
    exact h i (Nat.le_of_lt_succ i.isLt) k (Nat.le_of_lt_succ k.isLt)
  · rintro rfl i hi k hk
    let i' : Fin (cap+1) := ⟨i, Nat.lt_succ_of_le hi⟩
    let k' : Fin (cap+1) := ⟨k, Nat.lt_succ_of_le hk⟩
    exact (hg i' k').trans (canonicalAux_at ..)

end CellSparse.Gadget

end BorderVNP
end Computability
end OAI
