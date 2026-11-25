import OAI.Computability.NearSquareRoot.KernelPassEncoding
import OAI.Computability.NearSquareRoot.KernelPassCertificate
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Find

/-! # Uniform search for a normalized template

A candidate includes its own arity, number of rows and complete finite
instruction list. A bounded parser enumerates all candidates by one natural
number. The strict recursive-call inequality for a positive rational
exponent is tested by integer powering. Semantic correctness at all widths
is tested by rational transfer matrices.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelPass

/-- The sizes are part of the finite description, so they may grow as the
requested rational exponent decreases. -/
structure Candidate where
  arity : ℕ
  rows : ℕ
  program : Plan arity rows rows

namespace Candidate

private def fallback : Candidate := ⟨0,0,.mix (fun _ _ => (0,0))⟩

/-- Enumerate every finite program together with its row dimensions. -/
def atCode (n : ℕ) : Candidate := (do
  let (A,W,depth,code) ← Encodable.decode (α := ℕ × ℕ × ℕ × ℕ) n
  let p ← Plan.decode A depth W W code
  return Candidate.mk A W p).getD fallback

def code (t : Candidate) : ℕ :=
  Encodable.encode (t.arity,t.rows,t.program.depth,t.program.code)

theorem atCode_code (t : Candidate) : atCode t.code = t := by
  cases t
  simp [code, atCode, Plan.decode_code]

/-- The semantic and quantitative conditions required by the binary recursion. -/
def Good (num den : ℕ) (t : Candidate) : Prop :=
  5 ≤ t.arity ∧ 2 ≤ t.rows ∧ Correct t.program ∧
    (t.program.calls : ℝ) / t.rows < (t.arity : ℝ) ^ ((num : ℝ) / den)

/-- Every calculation in the verification predicate is on finite data. -/
def accepts (num den : ℕ) (t : Candidate) : Bool :=
  decide (5 ≤ t.arity ∧ 2 ≤ t.rows ∧ t.program.certified = true ∧
    t.program.calls ^ den < t.rows ^ den * t.arity ^ num)

theorem calls_lt_iff {num den A W s : ℕ} (hd : 0 < den) (hw : 0 < W) :
    s ^ den < W ^ den * A ^ num ↔
      (s : ℝ) / W < (A : ℝ)^((num : ℝ)/den) := by
  have hw' : (0:ℝ) < W := by exact_mod_cast hw
  have hd' : (den : ℝ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [← pow_lt_pow_iff_left₀ (n := den) (by positivity : 0 ≤ (s : ℝ)/W)
    (Real.rpow_nonneg (Nat.cast_nonneg _) _) hd.ne', div_pow,
    div_lt_iff₀ (pow_pos hw' _), ← Real.rpow_mul_natCast (Nat.cast_nonneg _),
    div_mul_cancel₀ _ hd', Real.rpow_natCast, mul_comm]
  exact_mod_cast Iff.rfl

theorem accepts_iff {num den : ℕ} (hd : 0 < den) (t : Candidate) :
    t.accepts num den = true ↔ Good num den t := by
  simp only [accepts, decide_eq_true_eq, Plan.certified_iff, Good]
  constructor
  · rintro ⟨ha,hw,hc,hs⟩
    exact ⟨ha,hw,hc,(calls_lt_iff hd (by omega)).mp hs⟩
  · rintro ⟨ha,hw,hc,hs⟩
    exact ⟨ha,hw,hc,(calls_lt_iff hd (by omega)).mpr hs⟩

private theorem terminates {num den : ℕ} (hd : 0 < den) (h : ∃ t, Good num den t) :
    ∃ n : ℕ, (atCode n).accepts num den = true := by
  obtain ⟨t, ht⟩ := h
  exact ⟨t.code, by rw [atCode_code, accepts_iff hd]; exact ht⟩

/-- The first certified template in the fixed enumeration. The existence
proof is erased when this search is evaluated. -/
def find (num den : ℕ) (hd : 0 < den) (h : ∃ t, Good num den t) : Candidate :=
  atCode (Nat.find (terminates hd h))

theorem find_good {num den : ℕ} (hd : 0 < den) (h : ∃ t, Good num den t) :
    Good num den (find num den hd h) :=
  (accepts_iff hd _).mp (Nat.find_spec (terminates hd h))

end Candidate
end KernelPass

end NearSquareRoot
end Computability
end OAI
