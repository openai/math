import OAI.Computability.BorderVNP.FiniteDiagonalCellTraceUnsigned
import OAI.Computability.BorderVNP.FiniteDiagonalCellTraceUnique
import OAI.Computability.BorderVNP.FiniteEvaluatorPrepareReports
import OAI.Computability.BorderVNP.PackedInheritedStaging
import OAI.Computability.BorderVNP.PackedInheritedFieldWeight

/-! # Actual typed scalar reports on local packed site banks

Append the bit-major scalar report after the site's guessed and supplied
words. Locality preserves its complete guard/observation result, including
the physical padded slabs and grouped ties in a born bottom box. Summing the
real typed checker tails against the native scalar product recovers the
original packed field value.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteDiagonal.CellTrace.PackedSite

open Crossing CellSparse FieldDirectory Packing.Inherited VPVNP RAMSerialization
open scoped Classical BigOperators
open private bits_left bits_right from OAI.Computability.BorderVNP.PackedInheritedStaging
open private lookupPrefix lookupSuffix reportBits_eq from OAI.Computability.BorderVNP.FiniteDiagonalCellTraceCopied
open private bitDigits from OAI.Computability.BorderVNP.FiniteDiagonalCellTrace
open private prod_counted from OAI.Computability.BorderVNP.FiniteCellEntries

variable (s : Site) {F : Type*} [Fintype F]

/-- Exact bit-major report metadata on top of the original physical inherited site. -/
def directory (scalars digits : ℕ) : Directory :=
  {s.directory with reportedCounts := FiniteEvaluator.Reports.fields s.size scalars digits}

/-- Supplied old lanes followed by the actual scalar report bits. -/
def external {digits : ℕ} (x : Fin s.incoming → Bool) (c : Fin (Fintype.card F) → Fin digits → Bool) :=
  List.ofFn x ++ Copied.reportBits c

/-- The original packed site sees the same actual bank on all of its allocated addresses. -/
theorem observation {digits : ℕ} (locality : s.Local) (g : Fin s.work → Bool) (x : Fin s.incoming → Bool)
    (c : Fin (Fintype.card F) → Fin digits → Bool) :
    s.observe (lookup (List.ofFn g ++ external s x c)) = s.observe (bits g x) := by
  apply locality
  intro i hi
  by_cases left : i < s.work
  · exact (lookupPrefix g _ ⟨i,left⟩).trans (bits_left g x ⟨i,left⟩).symm
  · obtain ⟨j,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt left)
    have hj : j < s.incoming := by change s.work+j < s.work+s.incoming at hi; omega
    rw [lookupSuffix]
    exact (lookupPrefix x _ ⟨j,hj⟩).trans (bits_right g x ⟨j,hj⟩).symm

/-- Each genuine report row reads its advertised scalar digit after the original entire bank. -/
theorem report_read {digits : ℕ} (g : Fin s.work → Bool) (x : Fin s.incoming → Bool)
    (c : Fin (Fintype.card F) → Fin digits → Bool) (v : Fin (Fintype.card F)) (i : Fin digits) :
    lookup (List.ofFn g ++ external s x c) (s.size+(finProdFinEquiv (i,v)).val) = c v i := by
  rw [Site.size,Nat.add_assoc,lookupSuffix,external,lookupSuffix,reportBits_eq]
  simp only [lookup,List.head?_drop,List.getElem?_ofFn,dite_eq_left (finProdFinEquiv (i,v)).isLt,
    Fin.eta,Option.getD_some]
  exact congrArg (fun p : Fin digits × Fin (Fintype.card F) => c p.2 p.1) (finProdFinEquiv.symm_apply_apply (i,v))

private theorem word_digits (b : ℕ → Bool) (xs : List ℕ) : word b xs = FieldPowers.digits (xs.map b) := by
  induction xs with
  | nil => rfl
  | cons i is ih => cases e : b i <;> simp [word,FieldPowers.digits,e,ih]

/-- The fixed field alphabet contains every selected ID, and each little-endian
report word gives its true number of occurrences in this local observation. -/
def ValidReport {digits : ℕ} (obs : List (Bool × Option ℕ)) (c : Fin (Fintype.card F) → Fin digits → Bool) : Prop :=
  (∀ j ∈ obs.filterMap Prod.snd, j < Fintype.card F) ∧
    ∀ j : Fin (Fintype.card F), (obs.filterMap Prod.snd).count j.val = FieldPowers.digits (List.ofFn (c j))

private theorem counts {digits : ℕ} (obs : List (Bool × Option ℕ)) (g : Fin s.work → Bool)
    (x : Fin s.incoming → Bool) (c : Fin (Fintype.card F) → Fin digits → Bool) :
    countsValid (lookup (List.ofFn g ++ external s x c)) (directory s (Fintype.card F) digits).reportedCounts obs ↔
      ValidReport obs c := by
  let rows := FiniteEvaluator.Reports.fields s.size (Fintype.card F) digits
  have hlen : rows.length=Fintype.card F := by simp [rows,FiniteEvaluator.Reports.fields]
  have hd (j : Fin rows.length) :
      word (lookup (List.ofFn g ++ external s x c)) rows[j] = FieldPowers.digits (List.ofFn (c (Fin.cast hlen j))) := by
    have row : rows[j] = List.ofFn fun i : Fin digits => s.size+(finProdFinEquiv (i,Fin.cast hlen j)).val := by
      change (List.ofFn fun v : Fin (Fintype.card F) => List.ofFn fun i : Fin digits =>
        s.size+(finProdFinEquiv (i,v)).val)[j.val] = _
      rw [List.getElem_ofFn]
      rfl
    rw [row,word_digits,List.map_ofFn]
    congr 2
    funext i
    exact report_read s g x c (Fin.cast hlen j) i
  change countsValid _ rows obs ↔ _
  unfold countsValid ValidReport
  constructor
  · rintro ⟨range,mul⟩
    refine ⟨by simpa only [hlen] using range,fun j => ?_⟩
    exact (mul (Fin.cast hlen.symm j)).trans (hd (Fin.cast hlen.symm j))
  · rintro ⟨range,mul⟩
    refine ⟨by simpa only [hlen] using range,fun j => ?_⟩
    exact (mul (Fin.cast hlen j)).trans (hd j).symm

private theorem raw (scalars digits : ℕ) (b : ℕ → Bool) :
    (directory s scalars digits).weight b = (s.observe b).elim 0 (fun obs =>
      if countsValid b (directory s scalars digits).reportedCounts obs then
        if (obs.map Prod.fst).foldl Bool.xor false then -1 else 1 else 0) := by
  have eq : (directory s scalars digits).observations b=s.directory.observations b := rfl
  unfold Directory.weight Site.observe
  rw [eq]
  by_cases pass : ∀ r ∈ s.rows, r.Valid s.boxes b
  · have hp : ∀ r ∈ (directory s scalars digits).records, r.Valid (directory s scalars digits).boxes b := pass
    cases o : s.directory.observations b <;> simp only [ite_eq_left pass,and_iff_right hp,Option.elim_none,Option.elim_some]
  · have hp : ¬(∀ r ∈ (directory s scalars digits).records, r.Valid (directory s scalars digits).boxes b) := pass
    cases o : s.directory.observations b <;> simp [pass,hp]

/-- The physical sparse directory returns its original site's sign precisely
on the correct scalar count report. A rejected packed site returns zero. -/
theorem entry {digits : ℕ} (locality : s.Local) (g : Fin s.work → Bool) (x : Fin s.incoming → Bool)
    (c : Fin (Fintype.card F) → Fin digits → Bool) :
    (directory s (Fintype.card F) digits).weight (lookup (List.ofFn g ++ external s x c)) =
      (s.observe (bits g x)).elim 0 (fun obs => if ValidReport obs c then
        if (obs.map Prod.fst).foldl Bool.xor false then -1 else 1 else 0) := by
  rw [raw,observation s locality]
  cases h : s.observe (bits g x) <;> simp only [Option.elim_none,Option.elim_some,counts]

/-- There is one binary field report even when some original factors have
no scalar ID, or an ID representing the zero element. -/
theorem uniqueReport {digits : ℕ} (obs : List (Bool × Option ℕ))
    (range : ∀ j ∈ obs.filterMap Prod.snd, j < Fintype.card F)
    (fit : (obs.filterMap Prod.snd).length < 2^digits) :
    ∃! c : Fin (Fintype.card F) → Fin digits → Bool, ValidReport obs c := by
  let n (j : Fin (Fintype.card F)) : Fin (2^digits) :=
    ⟨(obs.filterMap Prod.snd).count j.val,(List.count_le_length ..).trans_lt fit⟩
  refine ⟨fun j => wordBits digits (n j),⟨range,fun j => by simp [bitDigits,n]⟩,?_⟩
  intro c hc
  funext j
  apply (wordBits digits).symm.injective
  apply Fin.ext
  simpa only [bitDigits,n,Equiv.symm_apply_apply] using (hc.2 j).symm

/-- On a fixed packed bank, summing the true residual checker paths and the
bit-major scalar scanner over report choices recovers the packed field output. -/
theorem residual_field {digits : ℕ} [Field F] (locality : s.Local) (g : Fin s.work → Bool) (x : Fin s.incoming → Bool)
    (range : ∀ obs, s.observe (bits g x)=some obs → ∀ j ∈ obs.filterMap Prod.snd, j < Fintype.card F)
    (fit : ∀ obs, s.observe (bits g x)=some obs → (obs.filterMap Prod.snd).length < 2^digits) :
    (∑ c : Fin (Fintype.card F) → Fin digits → Bool,
      ((∑ p ∈ Compact.assignmentTails (directory s (Fintype.card F) digits) [] (List.ofFn g) (external s x c),
        TeamTape.haltWeight true p.2 : ℤ) : F) *
        ∏ v, (Fintype.equivFin F).symm v ^ FieldPowers.digits (List.ofFn (c v))) =
      (s.observe (bits g x)).elim 0 (fieldWeight (FieldPowers.entry (Fintype.equivFin F).symm)) := by
  simp only [Compact.assignmentTails_sum,entry s locality]
  cases ho : s.observe (bits g x) with
  | none => simp
  | some obs =>
    simp only [Option.elim_some]
    obtain ⟨c,hc,uc⟩ := uniqueReport (F := F) obs (range obs ho) (fit obs ho)
    rw [Finset.sum_eq_single c]
    · rw [ite_eq_left hc,fieldWeight,prod_counted (Fintype.equivFin F).symm _ (range obs ho)]
      simp only [← hc.2]
      split <;> simp
    · intro b _ hb
      simp [ite_eq_right (fun h => hb (uc b h))]
    · simp

/-- The sum over all original private assignments equals the true inherited
site table on this supplied word. -/
theorem site_field {digits : ℕ} [Field F] (locality : s.Local) (x : Fin s.incoming → Bool)
    (range : ∀ (g : Fin s.work → Bool) obs, s.observe (bits g x)=some obs → ∀ j ∈ obs.filterMap Prod.snd, j < Fintype.card F)
    (fit : ∀ (g : Fin s.work → Bool) obs, s.observe (bits g x)=some obs → (obs.filterMap Prod.snd).length < 2^digits) :
    (∑ g : Fin s.work → Bool, ∑ c : Fin (Fintype.card F) → Fin digits → Bool,
      ((∑ p ∈ Compact.assignmentTails (directory s (Fintype.card F) digits) [] (List.ofFn g) (external s x c),
        TeamTape.haltWeight true p.2 : ℤ) : F) *
        ∏ v, (Fintype.equivFin F).symm v ^ FieldPowers.digits (List.ofFn (c v))) =
      s.value (fieldWeight (FieldPowers.entry (Fintype.equivFin F).symm)) x :=
  Finset.sum_congr rfl fun g _ => residual_field s locality g x (range g) (fit g)

end FiniteDiagonal.CellTrace.PackedSite

end BorderVNP
end Computability
end OAI
