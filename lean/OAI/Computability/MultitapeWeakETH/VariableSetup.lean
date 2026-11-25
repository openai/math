import OAI.Computability.MultitapeWeakETH.VariableInput
import OAI.Computability.MultitapeWeakETH.SparseRun

/-! # Building the actual padded inputs from the canonical formula alone -/

namespace OAI.Computability.MultitapeWeakETH.VariableSetup

open IntegerMultiplication Code Bits Strip Staff Carry DyadicBudget VariableClock SparsePreparation SparseIteration
open Algorithms.SubexponentialSAT SqrtLogSpace.DisjointReuse
open scoped Classical
noncomputable section

abbrev Case := (n : ℕ) × {F : SAT.CNF (Fin n) // SAT.WidthAtMost 3 F}

def input (i : Case) := Encoding.encodeCNF i.2.val
def base (i : Case) := 1+i.1+(input i).length

def charge (cut K d q : ℕ) (i : Case) := base i+2^(exponent cut K d q i.1)

theorem input_le (cut K d q : ℕ) : Dom (charge cut K d q) (fun i => (input i).length) :=
  (Dom.base _).mono (fun i => (Nat.le_add_left _ (1+i.1)).trans (Nat.le_add_right _ _))

def regime (cut K d q : ℕ) : Regime Case where
  scale := charge cut K d q
  header i := send (input i)
  gauge := by
    apply (((Dom.const _ 2).mul (input_le cut K d q)).add (Dom.const _ 1)).mono
    intro i
    change size (input i) ≤ _
    have mass (w : Word) : size w = 2*w.length+1 := by
      induction w with
      | nil => rfl
      | cons b w ih => simp [ih,Nat.mul_add]; omega
    exact (mass _).le

def visits (K n s : ℕ) := (24*K*s^2*n+1)^2*2^(n/s+1)

theorem visits_enough (K n s j : ℕ) (hs : 0<s)
    (hj : (j:ℝ) ≤ ((24*K*s^2*n+1:ℕ):ℝ)^2*(2:ℝ)^((n:ℝ)/s)) : j ≤ visits K n s := by
  have rem := Nat.mod_lt n hs
  have eq := Nat.mod_add_div n s
  have le : n ≤ (n/s+1)*s := by rw [Nat.add_mul,Nat.one_mul,Nat.mul_comm (n/s) s]; omega
  have real : (n:ℝ)/s ≤ ((n/s+1:ℕ):ℝ) := (div_le_iff₀ (by exact_mod_cast hs)).mpr (by exact_mod_cast le)
  have pow := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1:ℝ)≤2) real
  rw [Real.rpow_natCast] at pow
  exact_mod_cast hj.trans (mul_le_mul_of_nonneg_left pow (sq_nonneg _))

def raw (i : Case) := ExecCNF.normalize SAT.Literal.negate (ExecQuantitativeSparsify.formulaList i.2.val)

def query (cut K d q : ℕ) (w : Case → Word) (i : Case) :=
  let n := i.1
  let s := sparseBudget q n
  let N := volume cut K n s
  (tally (visits K n s), parameters n N (2^depth d N) (w i),([SparseCountProgram.encodeBody (raw i)],false))

/-- A single charged program prepares both unary clocks, the tape parameters
and the initial normalized frontier. Its only input is the canonical CNF. -/
theorem prepare (cut K d q : ℕ) (hd : 1<d) :
    ∃ w : Case → Word, (∀ i, BinaryArithmetic.toNat (w i) = SparseBudget.chooseM 3 1 (sparseBudget q i.1) (by decide)) ∧
      (regime cut K d q).Has (query cut K d q w) := by
  let r := regime cut K d q
  let n (i : Case) := i.1
  let s (i : Case) := sparseBudget q (n i)
  let N (i : Case) := volume cut K (n i) (s i)
  let L (i : Case) := depth d (N i)
  have original : r.Has input := r.self
  have read : r.Has (fun i => (tally (n i),Encoding.encodeCNFBody i.2.val)) := by
    convert original.thenDo header_poly using 1
    funext i
    exact (header_eq ..).symm
  have vars : Realizes r n := read.ez Easy.fst
  have nf := Figure.of_spoken vars
  have sf := reciprocal vars q
  obtain ⟨recipWord,pr,correct⟩ := sf
  obtain ⟨theta,pt,thetaEq⟩ := threshold_program
  let w (i : Case) := theta (recipWord i)
  have thresh : r.Has w := pr.thenDo pt
  refine ⟨w,fun i => ?_,?_⟩
  · have eq : BinaryArithmetic.toNat (recipWord i) = s i := (binary_value _).trans (correct i)
    simpa only [w,eq] using thetaEq (recipWord i) (eq ▸ (show 0<s i by dsimp [s,sparseBudget]; positivity))
  have sd : Dom r.scale s := ((diameter n vars).add (Dom.const _ 1)).mono (fun i => reciprocal_le q (n i))
  have su : Realizes r s := (show Figure r s from ⟨recipWord,pr,correct⟩).pay sd
  let four := (su.times su).times (su.times su)
  have vol : Realizes r N := by
    convert (((Realizes.fix cut).plus ((Realizes.fix 2).times vars)).plus
      ((Realizes.fix 8).times (vars.times ((Realizes.fix (4*K^2)).times four)))).plus (Realizes.fix 1) using 1
    funext i; dsimp [N,VariableClock.volume]; ring
  have dep : Realizes r L := by
    have prog := Regime.Has.thenDo (g:=fun i => tally (N i)) vol (searchWidth_poly d)
    simpa only [searchWidth_eq _ _ hd,L,VariableClock.depth,Realizes,box,Function.comp_def] using prog
  have power (e : Case → ℕ) (le : ∀ i, e i ≤ exponent cut K d q (n i)) :
      Dom r.scale (fun i => 2^e i) := (Dom.base _).mono (fun i =>
        (Nat.pow_le_pow_right (by decide) (le i)).trans (Nat.le_add_left _ _))
  have pool : Realizes r (fun i => 2^L i) := ((Figure.natural 2).repeated dep).pay (power L (fun i => Nat.le_add_left ..))
  have ratio := nf.quotients (Figure.of_spoken su)
  have div : Realizes r (fun i => n i/s i) := ratio.pay ((diameter n vars).mono (fun i => Nat.div_le_self ..))
  have bins : Realizes r (fun i => 2^(n i/s i+1)) := ((Figure.natural 2).repeated (div.plus (Realizes.fix 1))).pay (by
    apply ((power (fun i => n i/s i) (fun i => Nat.le_add_right ..)).mul (Dom.const _ 2)).mono
    intro i; rw [pow_succ])
  let tree := (((Realizes.fix (24*K)).times (su.times su)).times vars).plus (Realizes.fix 1)
  have fuel : Realizes r (fun i => visits K (n i) (s i)) := by
    convert (tree.times tree).times bins using 1
    funext i; dsimp [visits]; ring
  have cap : Realizes r (fun i => SparseCountProgram.formulaBound (n i) 3) := by
    let p := ((Realizes.fix 2).times vars).plus (Realizes.fix 1)
    convert (vars.plus (Realizes.fix 2)).plus
      (((Realizes.fix 4).plus ((((Realizes.fix 8).times vars).plus (Realizes.fix 8)).times (Realizes.fix 3))).times
        ((Realizes.fix 4).times ((p.times p).times p))) using 1
    funext i; dsimp [SparseCountProgram.formulaBound]; ring
  obtain ⟨norm,pnorm,normEq⟩ := normalization
  have body : r.Has (fun i => SparseCountProgram.encodeBody (raw i)) := by
    convert (read.ez Easy.snd).thenDo pnorm using 1
    funext i; exact (normEq _).symm
  have stack := (body.pair (r.fixed ([] : List Word))).ez Easy.cons
  exact Regime.Has.pair fuel ((Regime.Has.pair ((Regime.Has.pair (Regime.Has.pair vol vars) pool).pair thresh) cap).pair
    (stack.pair (r.fixed false)))

end
end OAI.Computability.MultitapeWeakETH.VariableSetup
