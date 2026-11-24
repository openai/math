import OAI.Computability.VPVNP.RAMTapeRoutinePorts
import OAI.Computability.VPVNP.RAMTapeInputParametersLog
import OAI.Computability.VPVNP.RAMTapeInputParametersPower
import OAI.Computability.VPVNP.RAMTapeInputParametersBucket
import OAI.Computability.VPVNP.RAMTapeUnaryWord
import OAI.Computability.VPVNP.RAMParameters

/-!
# Computing the live bucket from the unary input length

The fixed rational exponent has numerator `p` and positive denominator `q`.
The potentially large integer `n^p` stays in a padded binary word. Only its
binary logarithm and the final bucket size are expanded as unary tallies.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.InputBucketFromSize

open BurstRAM

/-- Stack labels for converting unary size to a padded word, exponentiating, taking its
logarithm, and producing the unary bucket. -/
inductive Port
  | size | bucket | base | acc | log | tmp | pending | factor | product | shifted | sum
  deriving DecidableEq

instance : Fintype Port := derive_fintype% _

/-- Initialize the named size, base, power accumulator, logarithm, and bucket stacks with empty
arithmetic scratch. -/
def store (size base acc log bucket : List Bool) : Stacks Port
  | .size => size
  | .base => base
  | .acc => acc
  | .log => log
  | .bucket => bucket
  | _ => []

/-- Connect unary-to-word conversion to the size, pending marks, base, initial unit, and
temporary stack of bucket preparation. -/
def unaryPort : UnaryWord.Port → Port
  | .src => .size
  | .pending => .pending
  | .number => .base
  | .unit => .acc
  | .tmp => .tmp

/-- Connect repeated multiplication to the base, accumulator, factor, product, shifted factor,
sum, and temporary stack. -/
def powerPort : InputPower.Port → Port
  | .base => .base
  | .tmp => .tmp
  | .mul .multiplier => .acc
  | .mul .multiplicand => .factor
  | .mul .accumulator => .product
  | .mul .shifted => .shifted
  | .mul .sum => .sum

/-- Feed the power accumulator to the word ceiling-log scan and collect its marks on the
logarithm stack. -/
def logPort : WordCeilLog.Port → Port
  | .word => .acc
  | .tmp => .tmp
  | .out => .log

/-- Feed logarithm marks into the block-doubling routine and collect the resulting unary
bucket. -/
def bucketPort : InputBucket.Port → Port
  | .src => .log
  | .out => .bucket
  | .tmp => .tmp

private def unary (p : ℕ) := FiniteRoutine.ofStackCode (UnaryWord.code p) unaryPort
  (.alloc (Fin.last (p+1))) (· == .done)
private def power (p : ℕ) := FiniteRoutine.ofStackCode (InputPower.code p) powerPort
  (.round (Fin.last p) .test) (· == .done)
private def logarithm := FiniteRoutine.ofStackCode WordCeilLog.code logPort .reverse (· == .done)
private def bucket (q : ℕ) (hq : 0 < q) := FiniteRoutine.ofStackCode (InputBucket.code q hq)
  bucketPort .init (· == .done)

private def clearCode : StackCode Unit Bool
  | false => .pop () Option.isNone
  | true => .halt true

private def clearBase := FiniteRoutine.ofStackCode clearCode (fun _ => Port.base) false id

/-- One finite control per fixed rational parameter, independent of input length. -/
def routine (p q : ℕ) (hq : 0 < q) : FiniteRoutine Port :=
  ((((unary p).followedBy (power p)).followedBy clearBase).followedBy logarithm).followedBy (bucket q hq)

private theorem unary_run (p n : ℕ) :
    (unary p).Runs (UnaryWord.work p n) (store (List.replicate n true) [] [] [] [])
      (store [] (wordBits (UnaryWord.inputWord p n)) (wordBits (UnaryWord.unitWord p n)) [] []) := by
  apply FiniteRoutine.runs_ofStackCode_framed (by decide) rfl rfl (fun z h => by simp only [beq_iff_eq] at h; subst z; rfl)
    (UnaryWord.runs p n)
  · intro k; cases k <;> rfl
  · intro k; cases k <;> rfl
  · intro i hi
    cases i <;> first | rfl | exact (hi .src rfl).elim | exact (hi .number rfl).elim | exact (hi .unit rfl).elim

/-- The allocated width suffices even when the rational numerator is large. -/
theorem power_fits (p n : ℕ) : n^p < 2^(UnaryWord.width p n) := by
  have h : n ≤ 2^(n+1) := (Nat.lt_pow_self (by decide : 1 < 2)).le.trans
    (Nat.pow_le_pow_right (by decide) (Nat.le_succ n))
  calc
    n^p ≤ (2^(n+1))^p := Nat.pow_le_pow_left h p
    _ = 2^(p*(n+1)) := by rw [← pow_mul, Nat.mul_comm]
    _ < _ := Nat.pow_lt_pow_right (by decide) (by simp [UnaryWord.width, Nat.succ_mul])

private def powerWord (p n : ℕ) : Word (UnaryWord.width p n) := ⟨n^p, power_fits p n⟩

private theorem power_run (p n : ℕ) :
    let w := UnaryWord.width p n
    let x := wordBits (UnaryWord.inputWord p n)
    (power p).Runs (p*(8*w^2+18*w+10)+1) (store [] x (wordBits (UnaryWord.unitWord p n)) [] [])
      (store [] x (wordBits (powerWord p n)) [] []) := by
  have h := InputPower.power_run (Fin.last p) (UnaryWord.inputWord p n) (UnaryWord.unitWord p n)
  simp only [Fin.val_last, UnaryWord.inputWord_val, UnaryWord.unitWord_val, Nat.mul_one] at h
  have he : Fin.ofNat (2 ^ UnaryWord.width p n) (n^p) = powerWord p n :=
    Fin.ext (Nat.mod_eq_of_lt (power_fits p n))
  rw [he] at h
  apply FiniteRoutine.runs_ofStackCode_framed (by decide) rfl rfl (fun z hh => by simp only [beq_iff_eq] at hh; subst z; rfl) h
  · intro k; cases k with
    | base | tmp => rfl
    | mul r => cases r <;> rfl
  · intro k; cases k with
    | base | tmp => rfl
    | mul r => cases r <;> rfl
  · intro i hi; cases i <;> first | rfl | exact (hi (.mul .multiplier) rfl).elim

private theorem clear_run (x a : List Bool) :
    clearBase.Runs (x.length+1) (store [] x a [] []) (store [] [] a [] []) := by
  have loop (l : List Bool) : StackRuns clearCode (l.length+1) false (fun _ => l) true (fun _ => []) := by
    induction l with
    | nil => exact .cons (.pop rfl) (.nil ..)
    | cons b l ih =>
      refine .cons (.pop rfl) ?_
      convert ih using 1
      · rfl
      · funext u; cases u; simp
  apply FiniteRoutine.runs_ofStackCode_framed (by decide) rfl rfl (by intro b h; cases b <;> simp_all [clearCode]) (loop x)
  · intro u; cases u; rfl
  · intro u; cases u; rfl
  · intro i hi; cases i <;> first | rfl | exact (hi () rfl).elim

private theorem log_run (p n : ℕ) :
    ∃ t ≤ 4*(UnaryWord.width p n)+3, logarithm.Runs t (store [] [] (wordBits (powerWord p n)) [] [])
      (store [] [] [] (List.replicate (Nat.clog 2 (n^p)) true) []) := by
  obtain ⟨t, ht, h⟩ := WordCeilLog.runs (wordBits (powerWord p n)) []
  simp only [length_wordBits, TapeWord.value_wordBits, powerWord, List.append_nil] at ht h
  refine ⟨t, ht, ?_⟩
  apply FiniteRoutine.runs_ofStackCode_framed (by decide) rfl rfl (fun z hh => by simp only [beq_iff_eq] at hh; subst z; rfl) h
  · intro k; cases k <;> rfl
  · intro k; cases k <;> rfl
  · intro i hi; cases i <;> first | rfl | exact (hi .word rfl).elim | exact (hi .out rfl).elim

private theorem bucket_run (p q n : ℕ) (hq : 0 < q) :
    let k := Nat.clog 2 (n^p)
    let H := 2^(roundedUp p q n)
    ∃ t ≤ (k+1)*(q+10)*(H+1)+1, (bucket q hq).Runs t (store [] [] [] (List.replicate k true) [])
      (store [] [] [] [] (List.replicate H true)) := by
  obtain ⟨t, ht, h⟩ := InputBucket.bucket_run q (Nat.clog 2 (n^p)) hq
  dsimp only
  rw [roundedUp, Nat.clog_pow_left]
  refine ⟨t, ht, ?_⟩
  apply FiniteRoutine.runs_ofStackCode_framed (by decide) rfl rfl (fun z hh => by simp only [beq_iff_eq] at hh; subst z; rfl) h
  · intro k; cases k <;> rfl
  · intro k; cases k <;> rfl
  · intro i hi; cases i <;> first | rfl | exact (hi .src rfl).elim | exact (hi .out rfl).elim

/-- With exponent at most one, rounding to a binary power costs at most a
factor of two in the live bucket size. -/
theorem bucket_le {p q n : ℕ} (hq : 0 < q) (hpq : p ≤ q) (hn : 1 ≤ n) :
    2^(roundedUp p q n) ≤ 2*n := by
  have e : roundedUp p q n ≤ Nat.clog 2 n := by
    rw [roundedUp, Nat.clog_le_iff_le_pow (Nat.one_lt_pow hq.ne' (by decide))]
    calc
      n^p ≤ n^q := Nat.pow_le_pow_right (by omega) hpq
      _ ≤ (2^(Nat.clog 2 n))^q := Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) n) _
      _ = _ := by rw [← pow_mul, ← pow_mul, Nat.mul_comm]
  apply (Nat.pow_le_pow_right (by decide : 0 < 2) e).trans
  by_cases h : 1 < n
  · have he := Nat.clog_pos (by decide : 1 < 2) h
    have ht := Nat.pow_pred_clog_lt_self (by decide : 1 < 2) h
    calc
      2^(Nat.clog 2 n) = 2^(Nat.clog 2 n).pred*2 := by
        rw [← pow_succ]
        exact congrArg (2^·) (Nat.succ_pred_eq_of_pos he).symm
      _ ≤ 2*n := by omega
  · have : n = 1 := by omega
    subst n
    decide

/-- The clock's coefficient depends on the fixed rational. Its degree in
the input length is two for all numerators and denominators. -/
def clockCoefficient (p q : ℕ) : ℕ :=
  12*(p+1) + (36*p+1)*(p+1)^2 + 9*(p+1) + (6*(p+1)*(q+10)+1)

theorem runs (p q n : ℕ) (hq : 0 < q) (hpq : p ≤ q) (hn : 1 ≤ n) :
    ∃ t ≤ clockCoefficient p q * (n+1)^2,
      (routine p q hq).Runs t (store (List.replicate n true) [] [] [] [])
        (store [] [] [] [] (List.replicate (2^(roundedUp p q n)) true)) := by
  let w := UnaryWord.width p n
  let H := 2^(roundedUp p q n)
  let k := Nat.clog 2 (n^p)
  obtain ⟨t₁, ht₁, hlog⟩ := log_run p n
  obtain ⟨t₂, ht₂, hbucket⟩ := bucket_run p q n hq
  have hclear := clear_run (wordBits (UnaryWord.inputWord p n)) (wordBits (powerWord p n))
  rw [length_wordBits] at hclear
  have hrun := ((((unary_run p n).followedBy (power_run p n)).followedBy hclear).followedBy hlog).followedBy hbucket
  refine ⟨_, ?_, hrun⟩
  have hw : 1 ≤ w := UnaryWord.width_pos p n
  have hsq : w ≤ w^2 := by nlinarith
  have hnsq : n+1 ≤ (n+1)^2 := by nlinarith
  have ha := UnaryWord.work_le p n
  have hb : p*(8*w^2+18*w+10)+1 ≤ (36*p+1)*(p+1)^2*(n+1)^2 := calc
    _ ≤ p*(36*w^2)+w^2 := Nat.add_le_add (Nat.mul_le_mul_left _ (by omega)) (by omega)
    _ = _ := by simp only [w, UnaryWord.width]; ring
  have hc : (w+1)+t₁ ≤ 9*(p+1)*(n+1)^2 := calc
    _ ≤ 9*w := by change t₁ ≤ 4*w+3 at ht₁; omega
    _ ≤ 9*((p+1)*(n+1)^2) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ hnsq)
    _ = _ := by ring
  have hk : k ≤ w := Nat.clog_le_of_le_pow (power_fits p n).le
  have hH : H+1 ≤ 3*(n+1) := by have := bucket_le hq hpq hn; dsimp [H]; omega
  have hd : t₂ ≤ (6*(p+1)*(q+10)+1)*(n+1)^2 := calc
    _ ≤ (k+1)*(q+10)*(H+1)+1 := ht₂
    _ ≤ (2*w)*(q+10)*(3*(n+1))+(n+1)^2 :=
      Nat.add_le_add (Nat.mul_le_mul (Nat.mul_le_mul_right _ (by omega)) hH) (by omega)
    _ = _ := by simp only [w, UnaryWord.width]; ring
  change UnaryWord.work p n + (p*(8*w^2+18*w+10)+1) + (w+1) + t₁ + t₂ ≤ _
  rw [clockCoefficient, Nat.add_mul, Nat.add_mul, Nat.add_mul]
  omega

end RAMTape.InputBucketFromSize

end VPVNP
end Computability
end OAI
