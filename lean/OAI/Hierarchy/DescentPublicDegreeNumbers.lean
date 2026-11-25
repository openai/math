import Mathlib.Data.Nat.Log
import Mathlib.Tactic

namespace OAI
/-! # Numerical round growth and decoding of the fixed host degree calendar -/
namespace Hierarchy
namespace DescentHostDegree
/-- The fixed parameter `a₀` controls the absolute packing error allowance. -/
def logDegree (Δ : ℕ) := Nat.clog 2 (2*Δ)
def gap (Δ : ℕ) := 32*logDegree Δ
def packExponent (a₀ Δ : ℕ) := a₀+34*logDegree Δ

/-- The factor five covers surviving motif incidences at a site. The exponent
also permits every attached pack to have full old load `2^a B`. -/
def gainExponent (a₀ Δ : ℕ) := 10+33*logDegree Δ+2*packExponent a₀ Δ

end DescentHostDegree

open DescentHostDegree
namespace DescentCompiler
def ordinaryDegree (d : ℕ) :=
  let window:=gap d+gainExponent 20 d
  ((d+1)*(window+1+2^window)*(2^packExponent 20 d+2))^10

def atRound : ℕ→ℕ
  | 0=>3
  | j+1=>ordinaryDegree (atRound j)

end DescentCompiler

namespace DescentSixParty.Chronology
/-- The ordinary RAM comparisons only need the logarithmic degree class.
Its public factor encodes the class even when the realized host has fewer
vertices or neighbors than its fixed rectangular scan. -/
def degreeClass (radix factor : ℕ) := ((factor/radix).log2-50)/101

namespace OrdinaryLink
open DescentCompiler
theorem degree_step (d : ℕ) : logDegree d<logDegree (ordinaryDegree d) := by
  let win:=gap d+gainExponent 20 d
  let v:=(d+1)*(win+1+2^win)*(2^packExponent 20 d+2)
  have exponent : logDegree d≤win:=by dsimp [win,gap];omega
  have scale : 2^logDegree d≤2^win:=Nat.pow_le_pow_right (by decide) exponent
  have thick : (win+1+2^win)≤(d+1)*(win+1+2^win):=Nat.le_mul_of_pos_left _ (Nat.succ_pos _)
  have thick' : (d+1)*(win+1+2^win)≤v:=Nat.le_mul_of_pos_right _ (by positivity)
  have power : v≤v^10:=Nat.le_self_pow (by decide : (10:ℕ)≠0) v
  have growth : 2^logDegree d<2*(v^10):=by have:=Nat.two_pow_pos (logDegree d);omega
  exact (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).2 growth

theorem classes_strict : StrictMono (fun j=>logDegree (atRound j)) :=
  strictMono_nat_of_lt_succ (fun j=>degree_step (atRound j))

/-- Numeric finite search in the public list of round degrees. -/
def roundFor (target : ℕ) : ℕ→Option ℕ
  | 0=>none
  | n+1=>if logDegree (atRound n)=target then some n else roundFor target n

theorem roundFor_exact {j rounds : ℕ} (hj : j<rounds) : roundFor (logDegree (atRound j)) rounds=some j := by
  induction rounds with
  | zero=>omega
  | succ n ih=>
    by_cases h:j=n
    · subst j;simp [roundFor]
    · have h':j<n:=by omega
      simp [roundFor,(classes_strict h').ne.symm,ih h']

def publicDegree (rounds radix factor : ℕ) := (roundFor (degreeClass radix factor) rounds).elim 0 atRound

end OrdinaryLink
end DescentSixParty.Chronology
end Hierarchy

end OAI
