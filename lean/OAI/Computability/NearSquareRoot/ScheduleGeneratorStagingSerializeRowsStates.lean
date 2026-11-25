import OAI.Computability.NearSquareRoot.CommonAlphabetPublicNumbering
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSequenceRows
import OAI.Computability.NearSquareRoot.ScheduleStagingSerialize
import OAI.Computability.NearSquareRoot.KernelComputableAddress

/-! # State addresses of the two-tape staged operand serializer -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.SerializeRows

open CommonAlphabet StagingSerialize

private def fixedPhase (k : ℕ) : Fin 9 → Phase k
  | 0 => .turn
  | 1 => .back
  | 2 => .scan
  | 3 => .payload false
  | 4 => .payload true
  | 5 => .returnIn
  | 6 => .returnOut
  | 7 => .ready
  | 8 => .rejected

private def split (k : ℕ) : Phase k ≃ (Fin 9 ⊕ Fin (2^k) ⊕ Fin (header k).length) where
  toFun
    | .turn => .inl 0
    | .back => .inl 1
    | .scan => .inl 2
    | .payload false => .inl 3
    | .payload true => .inl 4
    | .returnIn => .inl 5
    | .returnOut => .inl 6
    | .ready => .inl 7
    | .rejected => .inl 8
    | .check j => .inr (.inl j)
    | .header j => .inr (.inr j)
  invFun
    | .inl j => fixedPhase k j
    | .inr (.inl j) => .check j
    | .inr (.inr j) => .header j
  left_inv := by intro q; cases q <;> first | rfl | (rename_i b; cases b <;> rfl)
  right_inv := by
    rintro (j|j|j)
    · fin_cases j <;> rfl
    · rfl
    · rfl

def states (k : ℕ) : CommonAlphabet.Numbering (Phase k) :=
  Numbering.ofEquiv (split k) ((Numbering.fin 9).sum
    ((Numbering.fin (2^k)).sum (Numbering.fin (header k).length)))

abbrev rank {k : ℕ} (q : Phase k) : ℕ := ((states k).equiv q).val

@[simp] theorem rank_turn (k : ℕ) : rank (.turn : Phase k) = 0 := rfl
@[simp] theorem rank_back (k : ℕ) : rank (.back : Phase k) = 1 := rfl
@[simp] theorem rank_scan (k : ℕ) : rank (.scan : Phase k) = 2 := rfl
@[simp] theorem rank_payload_false (k : ℕ) : rank (.payload false : Phase k) = 3 := rfl
@[simp] theorem rank_payload_true (k : ℕ) : rank (.payload true : Phase k) = 4 := rfl
@[simp] theorem rank_returnIn (k : ℕ) : rank (.returnIn : Phase k) = 5 := rfl
@[simp] theorem rank_returnOut (k : ℕ) : rank (.returnOut : Phase k) = 6 := rfl
@[simp] theorem rank_ready (k : ℕ) : rank (.ready : Phase k) = 7 := rfl
@[simp] theorem rank_rejected (k : ℕ) : rank (.rejected : Phase k) = 8 := rfl
@[simp] theorem rank_check {k : ℕ} (j : Fin (2^k)) : rank (.check j) = 9+j.val := rfl
@[simp] theorem rank_header {k : ℕ} (j : Fin (header k).length) :
    rank (.header j) = 9+2^k+j.val := by change 9+(2^k+j.val) = _; omega

@[simp] theorem rank_checkAt (k j : ℕ) : rank (checkAt k j) = if j < 2^k then 9+j else 0 := by
  unfold checkAt atIndex
  split <;> simp_all

@[simp] theorem rank_headerAt (k j : ℕ) :
    rank (headerAt k j) = if j < 2*k+3 then 9+2^k+j else 2 := by
  unfold headerAt atIndex
  split <;> rename_i h <;> rw [header_length] at h <;> simp [h]

@[simp] theorem rank_start (k : ℕ) : rank (StagingSerialize.start k) = 9 := by
  simp [StagingSerialize.start]

theorem size : Computable fun k => (states k).size := by
  change Computable fun k : ℕ => 9+(2^k+(header k).length)
  simp only [header_length]
  exact Primrec.nat_add.to_comp.comp (Computable.const 9) (Primrec.nat_add.to_comp.comp
    (KernelComputableAddress.primrec_pow (Primrec.const 2) Primrec.id).to_comp
    (Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (Computable.const 2) Computable.id) (Computable.const 3)))

theorem start : Computable fun k => ((states k).equiv (StagingSerialize.start k)).val :=
  (Computable.const 9).of_eq fun k => (rank_start k).symm

end Generator.SerializeRows

end NearSquareRoot
end Computability
end OAI
