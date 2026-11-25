import OAI.Computability.BorderVNP.CoverDeckPackSequence

/-! # Numerical invariants of a running physical pack bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open VPVNP.VerifierNetwork (Frame)
open PackedDeckCandidate

/-- Actual input count for a candidate of one pack. -/
def tableCount {B : Type*} {q l m w K : ℕ} (z : PackTables B q l m w K → Bool)
    (i : Fin K) (j : Fin m) (b : B) (g : Fin q → Deck l) : ℕ :=
  ParseBatchSort.value fun s => z (i,j,b,g,s)

/-- Count at a physical tile after the indicated number of circuit steps. -/
noncomputable def bankAt {B : Type*} [Fintype B] {q l m w K : ℕ}
    (step : Frame (Input B (Fin q → Deck l) m w) (BankStatePins B q l m w))
    (z : PackTables B q l m w K → Bool) (r : ℕ) (b : B) (g : Fin q → Deck l) : ℕ :=
  ParseBatchSort.value fun s => priorAt step z r (.inl (b,g,s))

/-- Cleared numerator of the running mean bank read from its actual circuit wires. -/
noncomputable def storedAt {B : Type*} [Fintype B] {q l m w K : ℕ}
    (step : Frame (Input B (Fin q → Deck l) m w) (BankStatePins B q l m w))
    (z : PackTables B q l m w K → Bool) (r : ℕ) (b : B) : ℕ :=
  ParseBatchSort.value fun s => priorAt step z r (.inr (b,s))

/-- Sum of unconditional means of all packs already processed. -/
noncomputable def baseAt {B : Type*} {q l m w K : ℕ} (prob : Fin m → ℚ)
    (z : PackTables B q l m w K → Bool) : ℕ → B → ℚ
  | 0, _ => 0
  | r+1, b => baseAt prob z r b + if hr : r < K then
      PackedDeckMean.mean prob (tableCount z ⟨r,hr⟩) b 1 else 0

theorem baseAt_succ {B : Type*} {q l m w K : ℕ} (prob : Fin m → ℚ)
    (z : PackTables B q l m w K → Bool) (i : Fin K) (b : B) :
    baseAt prob z (i.val+1) b = baseAt prob z i.val b + PackedDeckMean.mean prob (tableCount z i) b 1 := by
  simp [baseAt,i.isLt]

/-- A convex average of counts bounded by H is bounded by H, even after
the independent uniform deck posttranslation. -/
theorem packMean_le {B J G : Type*} [Fintype J] [Fintype G] [Group G] (prob : J → ℚ)
    (hn : ∀ j, 0 ≤ prob j) (hs : ∑ j, prob j = 1) (C : J → B → G → ℕ) (H : ℕ)
    (hc : ∀ j b g, C j b g ≤ H) (b : B) (x : G) : PackedDeckMean.mean prob C b x ≤ H := by
  rw [PackedDeckMean.mean_eq]
  calc
    _ ≤ ∑ j, prob j * H := Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left
      ((div_le_iff₀ (show (0:ℚ) < Fintype.card G by exact_mod_cast Fintype.card_pos)).mpr (by
        have h := Finset.sum_le_sum (s := Finset.univ) (fun g _ => hc j b g)
        have h' : ∑ g, C j b g ≤ H * Fintype.card G := by simpa [mul_comm] using h
        exact_mod_cast h')) (hn j)
    _ = H := by rw [← Finset.sum_mul,hs,one_mul]

/-- The cumulative rational mean is bounded by the number of processed
packs times the per-cell input bound. -/
theorem baseAt_le {B : Type*} {q l m w K : ℕ} (prob : Fin m → ℚ) (hn : ∀ j, 0 ≤ prob j)
    (hs : ∑ j, prob j = 1) (z : PackTables B q l m w K → Bool) (H : ℕ)
    (hc : ∀ i j b g, tableCount z i j b g ≤ H) (r : ℕ) (b : B) :
    baseAt prob z r b ≤ (r:ℚ)*H := by
  induction r with
  | zero => simp [baseAt]
  | succ r ih =>
    have h : (if hr : r < K then PackedDeckMean.mean prob (tableCount z ⟨r,hr⟩) b 1 else 0) ≤ H := by
      split
      · exact packMean_le prob hn hs _ H (hc _) b 1
      · positivity
    simpa [baseAt,add_mul] using add_le_add ih h

private theorem value_false (w : ℕ) : ParseBatchSort.value (fun _ : Fin w => false) = 0 := by
  induction w with
  | zero => rfl
  | succ w ih => simpa [ParseBatchSort.value] using ih

@[simp] theorem bankAt_zero {B : Type*} [Fintype B] {q l m w K : ℕ}
    (step : Frame (Input B (Fin q → Deck l) m w) (BankStatePins B q l m w))
    (z : PackTables B q l m w K → Bool) (b : B) (g : Fin q → Deck l) :
    bankAt step z 0 b g = 0 := value_false w

@[simp] theorem storedAt_zero {B : Type*} [Fintype B] {q l m w K : ℕ}
    (step : Frame (Input B (Fin q → Deck l) m w) (BankStatePins B q l m w))
    (z : PackTables B q l m w K → Bool) (b : B) : storedAt step z 0 b = 0 := value_false w

/-- Reading the count and mean banks of the next circuit stage is exactly
reading the new count and numerator ports of this stage. -/
theorem nextBank_eq {B : Type*} [Fintype B] {q l m w K : ℕ}
    (step : Frame (Input B (Fin q → Deck l) m w) (BankStatePins B q l m w))
    (z : PackTables B q l m w K → Bool) (i : Fin K) :
    (∀ b g, bankAt step z (i.val+1) b g = ParseBatchSort.value (fun s => stateAt step z i (.inr (b,g,s)))) ∧
    (∀ b, storedAt step z (i.val+1) b =
      meanNumerator (fun a => stateAt step z i (.inl (.inl (.inl (.inl a))))) b) := by
  constructor <;> intros <;> simp [bankAt,storedAt,priorAt_succ,meanNumerator,nextPriorPin]

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
