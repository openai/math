import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramOrder
import OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramUnaryCircuit

/-! # Checking and recovering the canonical one-hot decoder guess -/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

noncomputable section

namespace SignedProgram.Hot
open ExactQuantumFactoring BooleanNetwork
open Unary
open private hot hot_eval hot_count from
  OAI.LinearAlgebra.SpectralBooks.SignedProgram.SignedProgramUnaryCircuit
open scoped Classical
variable {n : ℕ}

def frameWire (n : ℕ) (j : Fin (n+1)) := guessBit n (.inr (.inl j))
def cursorWire (n : ℕ) (i : Fin (slotsCount n+1)) (j : Fin (n+1)) := guessBit n (.inr (.inr (i,j)))

def codeNet (n : ℕ) : BooleanNetwork (n+decodeGuessWidth n) 1 :=
  andOver fun c : Cell n ↦ orOver fun z : Fin (n+3) ↦
    if z.val < c.arity then hot (fun v : Fin (n+3) ↦ guessBit n (.inl (c,v))) z else constant false

theorem codeNet_correct (x : Basis n) (g : Basis (decodeGuessWidth n)) :
    (codeNet n).eval (Fin.append x g) 0 = true ↔ WellCoded g := by
  rw [codeNet,andOver_eval]
  unfold WellCoded
  apply forall_congr'
  intro c
  rw [orOver_eval]
  apply exists_congr
  intro v
  by_cases hv : v.val < c.arity
  · simp [hv,hot_eval]
  · simp [hv]

theorem codeNet_count (n : ℕ) : (codeNet n).net.count ≤
    (2+n*(8+5*n))*((n+3)*((n+3)*2+5)+2)+1 := by
  apply (andOver_count _ (C := (n+3)*((n+3)*2+5)+1) ?_).trans
    (Nat.add_le_add_right (Nat.mul_le_mul_right _ (cells_card_le n)) _)
  intro c
  apply (orOver_count _ (C := (n+3)*2+1) ?_).trans (by simp)
  intro j
  by_cases hj : j.val < c.arity
  · rw [ite_eq_left hj]
    exact hot_count _ _ (C := 0) (fun _ ↦ le_rfl)
  · rw [ite_eq_right hj]
    simp

def FrameValid (g : Basis (decodeGuessWidth n)) : Prop :=
  ∃ f : Fin (n+1), ∀ j, g (index (.inr (.inl j))) = true ↔ j = f

def frameOfBits (g : Basis (decodeGuessWidth n)) : Fin (n+1) :=
  if h : FrameValid g then Classical.choose h else 0

theorem frameOfBits_spec {g : Basis (decodeGuessWidth n)} (h : FrameValid g) :
    ∀ j, g (index (.inr (.inl j))) = true ↔ j = frameOfBits g := by
  rw [frameOfBits,dite_eq_left h]
  exact Classical.choose_spec h

def frameCodeNet (n : ℕ) : BooleanNetwork (n+decodeGuessWidth n) 1 :=
  orOver fun z : Fin (n+1) ↦ hot (frameWire n) z

theorem frameCodeNet_correct (x : Basis n) (g : Basis (decodeGuessWidth n)) :
    (frameCodeNet n).eval (Fin.append x g) 0 = true ↔ FrameValid g := by
  simp [frameCodeNet,FrameValid,orOver_eval,hot_eval,frameWire]

theorem frameCodeNet_count (n : ℕ) : (frameCodeNet n).net.count ≤ (n+1)*((n+1)*2+5)+1 := by
  exact (orOver_count _ (fun z ↦ hot_count (frameWire n) z (C := 0) (fun _ ↦ le_rfl))).trans
    (by simp)

def unpack (g : Basis (decodeGuessWidth n)) : DecodeWitness n :=
  (tableOfBits g, frameOfBits g, marksOfBits g)

theorem frameValid_encode (w : DecodeWitness n) : FrameValid (encodeGuess w.1 w.2.1 w.2.2) :=
  ⟨w.2.1, by simp⟩

theorem unpack_encode (w : DecodeWitness n) : unpack (encodeGuess w.1 w.2.1 w.2.2) = w := by
  rcases w with ⟨t,f,m⟩
  have hf := ((frameOfBits_spec (frameValid_encode (t,f,m))) f).mp (by simp)
  simp only [unpack,tableOfBits_encodeGuess,← hf,Prod.mk.injEq,true_and]
  exact funext₂ (encodeGuess_mark t f m)

theorem encode_unpack {g : Basis (decodeGuessWidth n)} (hc : WellCoded g) (hf : FrameValid g) :
    encodeGuess (tableOfBits g) (frameOfBits g) (marksOfBits g) = g := by
  funext i
  obtain ⟨(⟨c,v⟩ | (z | ⟨j,u⟩)),rfl⟩ := (Fintype.equivFin (GuessNames n)).surjective i
  · change encodeGuess _ _ _ (index (.inl (c,v))) = g (index (.inl (c,v)))
    have h := fieldBit_correct c v.val (fun _ ↦ false) g hc
    rw [fieldBit,dite_eq_left v.isLt,guessBit_eval] at h
    rw [encodeGuess_table]
    apply (Bool.eq_iff_iff.mpr ?_)
    rw [decide_eq_true_eq, Bool.eq_iff_iff.mp h, decide_eq_true_eq]
    exact eq_comm
  · change encodeGuess _ _ _ (index (.inr (.inl z))) = _
    rw [encodeGuess_frame, Bool.eq_iff_iff, decide_eq_true_eq]
    exact (frameOfBits_spec hf z).symm
  · exact encodeGuess_mark _ _ _ _ _

end SignedProgram.Hot

end

end SpectralBooks
end LinearAlgebra
end OAI
