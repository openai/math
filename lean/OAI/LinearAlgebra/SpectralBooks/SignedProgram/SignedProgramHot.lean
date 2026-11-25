import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramCells
import OAI.Computability.QuantumFactoring.BooleanFold
import OAI.Computability.QuantumFactoring.BooleanVector

/-! # One-hot Boolean guesses for the decoder

A guess consists of the table's scalar equality flags, the body-length flag
and the cursor rows. All unused scalar values must be false.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace SignedProgram.Hot

open ExactQuantumFactoring BooleanNetwork
open scoped Classical
variable {n : ℕ}

abbrev GuessNames (n : ℕ) := (Cell n × Fin (n+3)) ⊕ (Fin (n+1) ⊕ (Fin (slotsCount n+1) × Fin (n+1)))
def decodeGuessWidth (n : ℕ) := Fintype.card (GuessNames n)

def index (c : GuessNames n) : Fin (decodeGuessWidth n) := Fintype.equivFin _ c

def guessBit (n : ℕ) (c : GuessNames n) : BooleanNetwork (n + decodeGuessWidth n) 1 :=
  bit (Fin.natAdd n (index c))

@[simp] theorem guessBit_eval (c : GuessNames n) (x : Basis n) (g : Basis (decodeGuessWidth n)) :
    (guessBit n c).eval (Fin.append x g) 0 = g (index c) := Fin.append_right _ _ _

@[simp] theorem guessBit_count (c : GuessNames n) : (guessBit n c).net.count = 0 := rfl

def fieldBit (n : ℕ) (c : Cell n) (v : ℕ) : BooleanNetwork (n+decodeGuessWidth n) 1 :=
  if hv : v < n+3 then guessBit n (.inl (c,⟨v,hv⟩)) else constant false

theorem fieldBit_count (n : ℕ) (c : Cell n) (v : ℕ) : (fieldBit n c v).net.count ≤ 1 := by
  by_cases h : v < n+3
  · rw [fieldBit,dite_eq_left h]
    simp
  · rw [fieldBit,dite_eq_right h]
    simp

private def valueOf (g : Basis (decodeGuessWidth n)) (c : Cell n) : ℕ :=
  if h : ∃ v : Fin (n+3), g (index (.inl (c,v))) = true then (Classical.choose h).val else 0

def tableOfBits {n : ℕ} (g : Basis (decodeGuessWidth n)) : Table n :=
  reconstruct n (valueOf g)

/-- Each coordinate is a legal scalar, and every bit of its one-hot row is
forced. The frame and cursor bits are checked separately. -/
def WellCoded {n : ℕ} (g : Basis (decodeGuessWidth n)) : Prop :=
  ∀ c : Cell n, ∃ a : Fin (n+3), a.val < c.arity ∧
    ∀ v : Fin (n+3), g (index (.inl (c,v))) = true ↔ v = a

private theorem valueOf_spec {g : Basis (decodeGuessWidth n)} (hg : WellCoded g) (c : Cell n) :
    valueOf g c < c.arity ∧ ∀ v : Fin (n+3), g (index (.inl (c,v))) = true ↔ v.val = valueOf g c := by
  obtain ⟨a,ha,he⟩ := hg c
  have hex : ∃ v : Fin (n+3), g (index (.inl (c,v))) = true := ⟨a,(he a).mpr rfl⟩
  have hval : valueOf g c = a.val := by
    rw [valueOf,dite_eq_left hex,(he _).mp (Classical.choose_spec hex)]
  simp only [hval]
  exact ⟨ha,fun v ↦ (he v).trans Fin.ext_iff⟩

theorem fieldBit_correct (c : Cell n) (v : ℕ) (x : Basis n) (g : Basis (decodeGuessWidth n))
    (h : WellCoded g) :
    (fieldBit n c v).eval (Fin.append x g) 0 = decide (c.value (tableOfBits g) = v) := by
  unfold tableOfBits
  rw [value_reconstruct _ (fun c ↦ (valueOf_spec h c).1)]
  apply Bool.eq_iff_iff.mpr
  by_cases hv : v < n+3
  · rw [fieldBit,dite_eq_left hv,guessBit_eval, decide_eq_true_eq]
    exact ((valueOf_spec h c).2 ⟨v,hv⟩).trans eq_comm
  · rw [fieldBit,dite_eq_right hv,eval_constant,decide_eq_true_eq]
    have hlt := ((valueOf_spec h c).1).trans_le c.arity_bound
    simp [show valueOf g c ≠ v by omega]

/-- Exactly one setting of the raw bits represents a given table, frame and cursor mask. -/
def encodeGuess (t : Table n) (f : Fin (n+1)) (m : Marks n) : Basis (decodeGuessWidth n) :=
  fun i ↦ match (Fintype.equivFin (GuessNames n)).symm i with
    | .inl (c,v) => decide (v.val = c.value t)
    | .inr (.inl v) => decide (v = f)
    | .inr (.inr (i,v)) => m i v

@[simp] theorem encodeGuess_table (t : Table n) (f : Fin (n+1)) (m : Marks n) (c : Cell n) (v : Fin (n+3)) :
    encodeGuess t f m (index (.inl (c,v))) = decide (v.val = c.value t) := by simp [encodeGuess,index]

@[simp] theorem encodeGuess_frame (t : Table n) (f v : Fin (n+1)) (m : Marks n) :
    encodeGuess t f m (index (.inr (.inl v))) = decide (v = f) := by simp [encodeGuess,index]

@[simp] theorem encodeGuess_mark (t : Table n) (f : Fin (n+1)) (m : Marks n) (i : Fin (slotsCount n + 1))
    (v : Fin (n+1)) : encodeGuess t f m (index (.inr (.inr (i,v)))) = m i v := by simp [encodeGuess,index]

theorem wellCoded_encodeGuess (t : Table n) (f : Fin (n+1)) (m : Marks n) : WellCoded (encodeGuess t f m) := by
  intro c
  refine ⟨⟨_, (c.value_lt t).trans_le c.arity_bound⟩, c.value_lt t, ?_⟩
  intro v
  simp [Fin.ext_iff]

@[simp] theorem tableOfBits_encodeGuess (t : Table n) (f : Fin (n+1)) (m : Marks n) :
    tableOfBits (encodeGuess t f m) = t := by
  rw [tableOfBits, ← reconstruct_value t]
  congr 1
  funext c
  let v : Fin (n+3) := ⟨c.value t, (c.value_lt t).trans_le c.arity_bound⟩
  have h := ((valueOf_spec (wellCoded_encodeGuess t f m) c).2 v).mp (by simp [v])
  simpa [v, reconstruct_value] using h.symm

def marksOfBits (g : Basis (decodeGuessWidth n)) : Marks n := fun i v ↦ g (index (.inr (.inr (i,v))))

end SignedProgram.Hot

end

end SpectralBooks
end LinearAlgebra
end OAI
