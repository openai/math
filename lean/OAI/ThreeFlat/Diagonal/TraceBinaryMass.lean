import OAI.ThreeFlat.Diagonal.TraceBinaryWitness
import OAI.ThreeFlat.Diagonal.TraceMass
import OAI.ThreeFlat.Diagonal.TraceCpuBits

namespace OAI
/-! # The native path sum on fixed binary CPU and sort arrays -/

namespace ThreeFlat.Diagonal.TraceRows

open Computability.VPVNP BurstRAM RAMMemory RAMSort RAMSerialization TraceBanks
variable {F : Type*} {w p r k d : ℕ}

/-- Sum over a canonical encoding with zero on noncanonical strings. -/
private theorem sum_encoded {A B : Type*} [Fintype A] [Fintype B] [AddCommMonoid F]
    (enc : A → B) (dec : B → A) (left : Function.LeftInverse dec enc) (g : A → F) :
    letI := Classical.decEq B
    (∑ a, g a) = ∑ b, if enc (dec b) = b then g (dec b) else 0 := by
  classical
  trans ∑ b ∈ Finset.univ.filter (fun b => enc (dec b) = b), g (dec b)
  · apply Finset.sum_bij (fun a _ => enc a)
    · intro a _
      simp [left a]
    · intro a _ b _ he
      exact left.injective he
    · intro b hb
      exact ⟨dec b, Finset.mem_univ _, (Finset.mem_filter.mp hb).2⟩
    · intro a _
      rw [left a]
  · rw [Finset.sum_filter]

/-- An uncoded row sequence already fixes all nonzero weights by its single halt. -/
def terminalProduct [Monoid F] {C : Type*} (code : RAM.FieldCode F w) (rows : List (Row w C)) : F :=
  (rows.map (fun x => match x with
    | .halt _ out => code.terminal out
    | _ => 1)).prod

private theorem terminal_pad [Monoid F] {C : Type*} (code : RAM.FieldCode F w) (f : ℕ) :
    terminalProduct code (List.replicate f (.pad : Row w C)) = 1 := by
  induction f with
  | zero => rfl
  | succ f ih => simp [terminalProduct, List.replicate_succ]

theorem terminalProduct_eq [Monoid F] {C : Type*} (code : RAM.FieldCode F w)
    {P : Program w C} {c rs} (hl : Local P c rs) :
    terminalProduct code rs = code.terminal (report rs).result := by
  induction hl with
  | @halt c f out hs =>
    change code.terminal out * terminalProduct code (List.replicate f (.pad : Row w C)) = _
    rw [terminal_pad, mul_one]
    rfl
  | move hs ht ih => simpa [terminalProduct, report, Report.prepend] using ih

/-- The local Boolean acceptance predicate on all guessed wires, with one
terminal field factor at a halting row and unit factors elsewhere. -/
noncomputable def binaryWeight [Semiring F] (code : RAM.FieldCode F w) (M : PrivateRAM.Machine w p r k)
    (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (s : Word w) (S d f : ℕ) (header : ℕ → Word w)
    (bits : CpuBits w r f) (z : SortBits d (w+1)) : F := by
  classical
  let xs := readCpu hw hp bits
  let rows := List.ofFn xs
  let P := exposed M
  let initial := P.start (wide s)
  exact if writeCpu hw hp xs = bits ∧ before (rows.headD .pad) = some initial ∧ pairs P rows ∧
      memoryPass (by omega) S d (fun i => wide (header i)) (report rows).events z
    then terminalProduct (wideCode code) rows else 0

/-- Summing the uniquely determined sorting messages inserts exactly the
read-correctness test, over any coefficient semiring. -/
private theorem sum_memoryPass [Semiring F] (hw : 2 ≤ w) (S d : ℕ) (header : ℕ → Word w)
    (es : List (Event w)) (fit : S + es.length ≤ 2^(1+d)) (hs : S ≤ 2^w) (ht : es.length ≤ 2^w)
    (weight : F) {memDecision : ∀ z, Decidable (memoryPass hw S d header es z)}
    {correctDecision : Decidable (Correct (initialMemory S header) es)} :
    (∑ z : SortBits d w, @ite F (memoryPass hw S d header es z) (memDecision z) weight 0) =
      @ite F (Correct (initialMemory S header) es) correctDecision weight 0 := by
  classical
  by_cases hc : Correct (initialMemory S header) es
  · rw [ite_eq_left hc]
    obtain ⟨m, hm, hu⟩ := (existsUnique_memoryBits_iff hw S d header es fit hs ht).mpr hc
    rw [Finset.sum_eq_single m]
    · simp [hm]
    · intro z _ hne
      exact ite_eq_right (fun h => hne (hu z h))
    · simp
  · rw [ite_eq_right hc]
    apply Finset.sum_eq_zero
    intro z _
    apply ite_eq_right
    intro h
    exact hc (((TraceRecordSort.twoTrack_at_iff _ _ _ _ fit _).mp h.2).2)

set_option maxHeartbeats 1200000 in
/-- The weighted RAM value as a sum over just the binary CPU and binary
sorting wires of the paired-row trace. All validators in each summand are
adjacent CPU checks, local sort-send checks, and the sorted predecessor
tests. -/
theorem value_eq_sum_binary [Semiring F] (code : RAM.FieldCode F w) (M : PrivateRAM.Machine w p r k)
    (hw : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (s : Word w) (S d f : ℕ) (header : ℕ → Word w)
    (hs : S ≤ 2^w) (hf : f ≤ 2^(w+1)) (fit : S+f ≤ 2^(1+d)) :
    RAM.value code M f s (initialMemory S header) =
      ∑ bits : CpuBits w r f, ∑ z : SortBits d (w+1), binaryWeight code M hw hp s S d f header bits z := by
  classical
  let : DecidableEq (CpuBits w r f) := Classical.decEq _
  rw [value_eq_checked_rows code M s S (1+d) f header hs fit]
  let P := exposed M
  let c := P.start (wide s)
  let hd := fun i => wide (header i)
  let g := fun xs : Fin f → Row (w+1) (Snapshot w p r) =>
    rowWeight (wideCode code) P c S (1+d) hd (List.ofFn xs)
  change (∑ xs, g xs) = _
  rw [sum_encoded (writeCpu hw hp) (readCpu hw hp) (read_write_cpu hw hp) g]
  apply Finset.sum_congr rfl
  intro bits _
  let xs := readCpu hw hp bits
  let rs := List.ofFn xs
  have hr : rs.length = f := List.length_ofFn
  have hb (z : SortBits d (w+1)) : binaryWeight code M hw hp s S d f header bits z =
      if writeCpu hw hp xs = bits ∧ Local P c rs ∧
        memoryPass (by omega) S d hd (report rs).events z then terminalProduct (wideCode code) rs else 0 := by
    simp only [binaryWeight, xs, rs, P, c, hd, local_iff_pairs, and_assoc]
    exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)
  have hg : g xs = if Local P c rs ∧
      PaddedCheck none (TraceRecordSort.sorted S (1+d) hd (report rs).events) then
        (wideCode code).terminal (report rs).result else 0 := by
    simp only [g, rowWeight, verified, local_iff_pairs, and_assoc, xs, rs]
    exact ite_congr rfl (fun _ => rfl) (fun _ => rfl)
  change (if writeCpu hw hp xs = bits then g xs else 0) = _
  simp_rw [hb]
  by_cases hcode : writeCpu hw hp xs = bits
  · by_cases hl : Local P c rs
    · have he : (report rs).events.length < f := hr ▸ (local_spec hl).1.length_lt
      have hh : S ≤ 2^(w+1) := by rw [Nat.pow_succ]; omega
      have hc := TraceRecordSort.sorted_iff_correct S (1+d) hd (report rs).events (by omega)
      simp only [hcode, ite_true, hg, hl, true_and, hc]
      rw [terminalProduct_eq _ hl]
      exact (sum_memoryPass (show 2 ≤ w+1 by omega) S d hd (report rs).events
        (by omega) hh (by omega) ((wideCode code).terminal (report rs).result)).symm
    · simp [hcode, hg, hl]
  · simp [hcode]

end ThreeFlat.Diagonal.TraceRows

end OAI
