import OAI.Computability.VPVNP.RAMTapePublicExprLogScan
import OAI.Computability.VPVNP.RAMTapeRoutinePorts

/-! # Padded word code for the public grammar logarithms

A single fixed control computes either binary logarithm in the destination
register. After scanning the bits it converts at most `w` unary marks to a
padded binary word by verified word increments. The other registers, public
words, persistent word and private write log are preserved.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.PublicExprLog

open BurstRAM BurstRAM.PrivateRAM
open UnaryWord (Port store)

variable {r k w : ℕ}

private def ports (dst : Fin r) : Port → ISA.Port r k
  | .number => .reg dst
  | .pending => .work 0
  | .tmp => .work 1
  | .src => .work 2
  | .unit => .work 3

private theorem ports_injective (dst : Fin r) : Function.Injective (ports (k := k) dst) := by
  intro p q h
  cases p <;> cases q <;> simp [ports] at h ⊢

/-- In-place floor or ceiling binary logarithm; no auxiliary architectural
register is required. -/
def code (ceiling : Bool) (dst : Fin r) : FiniteRoutine (ISA.Port r k) :=
  (FiniteRoutine.ofStackCode (scan ceiling) (ports dst) .reverse (· == .done)).followedBy
    (FiniteRoutine.ofStackCode (UnaryWord.code 0) (ports dst) .count (· == .done))

/-- Quadratic step bound for computing a floor or ceiling binary logarithm in a padded word. -/
def bound (w : ℕ) := 12 * (w+1)^2

theorem runs (ceiling : Bool) (dst : Fin r) (pub : Fin k → Word w) (persist : Word w)
    (rs : Fin r → Word w) (log : WriteLog w) :
    ∃ t ≤ bound w, (code ceiling dst).Runs t (ISA.bank pub persist rs log)
      (ISA.bank pub persist (Function.update rs dst
        (Fin.ofNat (2^w) (if ceiling then Nat.clog 2 (rs dst).val else Nat.log 2 (rs dst).val))) log) := by
  let x := rs dst
  let j := if ceiling then Nat.clog 2 x.val else Nat.log 2 x.val
  let y := Fin.ofNat (2^w) j
  let base := ISA.bank pub persist rs log
  have hj : j ≤ w := by
    cases ceiling with
    | true => exact Nat.clog_le_of_le_pow x.isLt.le
    | false =>
      by_cases hz : x.val = 0
      · simp [j, hz]
      · exact (Nat.log_lt_of_lt_pow hz x.isLt).le
  have hfit : j < 2^w := hj.trans_lt (Nat.lt_two_pow_self (n := w))
  obtain ⟨t, ht, hscan⟩ := scan_runs ceiling (wordBits x)
  simp only [length_wordBits, TapeWord.value_wordBits] at ht hscan
  obtain ⟨res,hl,hv,hcount⟩ := UnaryWord.count_run 0 j [] (List.replicate w false) []
    (by simpa only [UnaryWord.zeros_value, Nat.zero_add, List.length_replicate] using hfit)
  simp only [List.length_replicate, UnaryWord.zeros_value, Nat.zero_add] at hl hv hcount
  have he : res = wordBits y := TapeWord.eq_of_length_value (hl.trans (length_wordBits y).symm)
    (by rw [hv, TapeWord.value_wordBits]; exact (Nat.mod_eq_of_lt hfit).symm)
  rw [he] at hcount
  have hp := ports_injective (k := k) dst
  have first := FiniteRoutine.runs_ofStackCode hp (normal := (· == Phase.done)) rfl rfl
    (fun q h => by simp only [beq_iff_eq] at h; subst q; rfl) base hscan
  have second := FiniteRoutine.runs_ofStackCode hp (normal := (· == UnaryWord.Phase.done)) rfl rfl
    (fun q h => by simp only [beq_iff_eq] at h; subst q; rfl) base hcount
  have hi : installStacks (ports dst) base (store [] [] (wordBits x) [] []) = base := by
    apply installStacks_eq hp
    intro p
    cases p <;> rfl
  have ho : installStacks (ports dst) base (store [] [] (wordBits y) [] []) =
      Function.update base (.reg dst) (wordBits y) := by
    apply installStacks_frame hp
    · intro p
      cases p <;> simp [ports, store, base, ISA.bank]
    · intro l h
      exact Function.update_of_ne (h .number).symm ..
  rw [hi] at first
  rw [ho, ISA.bank_updateReg] at second
  refine ⟨t+(j*(4*w+3)+1), ?_, first.followedBy second⟩
  have hjw := Nat.mul_le_mul_right (4*w+3) hj
  unfold bound
  nlinarith only [hjw, ht, Nat.zero_le (w*w), Nat.zero_le w]

end RAMTape.PublicExprLog

end VPVNP
end Computability
end OAI
