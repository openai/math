import OAI.Computability.VPVNP.ParseOracleRun
import OAI.Computability.VPVNP.GrammarSize
import OAI.Computability.VPVNP.SpaceRunMonotone

/-!
# Resource bounds for the grammar coefficient checker

At length `n` the grammar of §8.1 has `n^(C+5)` states at each positive degree.
The bounds below are uniform over the root state and layer and over the placement
of grammar labels in the joint parameter list. The word and exponent values are
runtime inputs. They do not contribute to the advice length.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseOracle

open ParseGrammar UniversalCountStack

/-- The `n^(C+5)` states available at each positive degree of the length-`n` parse grammar. -/
abbrev States (C n : ℕ) := Fin (n ^ (C + 5))

/-- Number of independently enumerated event flags, including invalid events that
the fixed incidence clauses force to zero. -/
def flagCount (C n : ℕ) : ℕ :=
  let S := n ^ (C + 5)
  n * n * S * (n * 2 + n * S * S)

theorem flags_eq_flagCount (C n : ℕ) : Flags n n (States C n) = flagCount C n := by
  simpa only [States, Var, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin, flagCount] using
    EventCode.card (Var n) (States C n) n

/-- There is one tally row for each terminal variable and each grammar label. -/
def rowBound (C n : ℕ) : ℕ :=
  let S := n ^ (C + 5)
  n * 2 + (S * (n * 2) + n ^ 2 * S ^ 3)

theorem card_row_le (C n : ℕ) : Fintype.card (Row n n (States C n)) ≤ rowBound C n := by
  change Fintype.card (Var n ⊕ Label n n (States C n)) ≤ _
  rw [Fintype.card_sum]
  apply Nat.add_le_add
  · simp [Var]
  · simpa only [States, Var, Fintype.card_prod, Fintype.card_bool, Fintype.card_fin] using
      card_grammarLabel_le (Var n) (States C n) n

/-- Bound on the AND/NOT circuit gates for the queried exponent width. -/
def gateBound (C n W : ℕ) : ℕ :=
  let k := flagCount C n
  let r := rowBound C n
  let wires := k + r * (k+1)
  4 * (wires * (W*3+3) + wires + k*(wires*8) + (r*(k+1)*10+2) +
    (3*(k+k*(5*k+4)) + 3*(1+k*(k+4)) + 4))

/-- Length of the compiled gate stream, including its unary addresses. -/
def adviceBound (C n L W : ℕ) : ℕ :=
  let g := gateBound C n W
  (g+2) * (2*(g+(n+L*W)+flagCount C n+2)+3)

/-- Uniform instruction budget for one choice of the event flags. -/
def choiceBound (C n L W : ℕ) : ℕ :=
  let k := flagCount C n
  32 * (adviceBound C n L W + (gateBound C n W+2) + (n+L*W) + k + 1) + 8*k + 9

/-- Bounds the height of every stack throughout enumeration. -/
def stackBound (C n L W : ℕ) : ℕ :=
  (n+L*W) + adviceBound C n L W + (flagCount C n+1) + choiceBound C n L W

/-- A polynomial exponent bounding the time to enumerate all flags. -/
def timeExponent (C n L W : ℕ) : ℕ := flagCount C n + choiceBound C n L W

variable {C n L : ℕ} (d : Fin n) (h : States C n)
  (addr : Label n n (States C n) → Fin L) (W : ℕ)

theorem checker_frame_size_le :
    4 * (frame (parseOracleMetadata (Var n) (States C n) n d h) addr W).size ≤
      gateBound C n W := by
  let M := parseOracleMetadata (Var n) (States C n) n d h
  apply (Nat.mul_le_mul_left 4 (frame_size_le M addr W)).trans
  have hl : HardnessCNF.literalCount M.clauses ≤
      flagCount C n + flagCount C n * (5 * flagCount C n + 4) := by
    rw [← flags_eq_flagCount]
    exact literalCount_incidenceCNF_le _ _ _ _
  have hc : M.clauses.length ≤ 1 + flagCount C n * (flagCount C n + 4) := by
    rw [← flags_eq_flagCount]
    exact length_incidenceCNF_le _ _ _ _
  dsimp only [gateBound]
  have hk : Fintype.card (EventCode (Var n) (States C n) n) ≤ flagCount C n := (flags_eq_flagCount ..).le
  gcongr <;> exact card_row_le ..

theorem checker_gates_le :
    (frame (parseOracleMetadata (Var n) (States C n) n d h) addr W).circuitSize () ≤
      gateBound C n W :=
  ((frame (parseOracleMetadata (Var n) (States C n) n d h) addr W).circuitSize_le ()).trans
    (checker_frame_size_le d h addr W)

theorem checker_advice_le : (AdviceCircuit.encode (AdviceCircuit.compile (checker d h addr W))).length ≤
    adviceBound C n L W := by
  apply (AdviceCircuit.compile_size _).trans
  dsimp only [adviceBound]
  change (_+2) * (2*(_+(n+L*W)+Flags n n (States C n)+2)+3) ≤ _
  rw [flags_eq_flagCount]
  gcongr <;> exact checker_gates_le d h addr W

theorem checker_perChoice_le : perChoice (checker d h addr W) ≤ choiceBound C n L W := by
  dsimp only [perChoice, choiceBound]
  rw [AdviceCircuit.compile_length]
  have hk : Fintype.card (EventCode (Var n) (States C n) n) ≤ flagCount C n := (flags_eq_flagCount ..).le
  have ha := checker_advice_le d h addr W
  have hg := checker_gates_le d h addr W
  omega

theorem checker_stackLimit_le : stackLimit (checker d h addr W) ≤ stackBound C n L W := by
  have ha := checker_advice_le d h addr W
  have hc := checker_perChoice_le d h addr W
  dsimp only [stackLimit, stackBound]
  have hk : Fintype.card (EventCode (Var n) (States C n) n) ≤ flagCount C n := (flags_eq_flagCount ..).le
  omega

theorem checker_time_le :
    2^(Flags n n (States C n)) * perChoice (checker d h addr W) ≤ 2^(timeExponent C n L W) := by
  conv_rhs => rw [timeExponent, pow_add]
  exact Nat.mul_le_mul (Nat.pow_le_pow_right (by decide) (flags_eq_flagCount C n).le)
    ((checker_perChoice_le d h addr W).trans Nat.lt_two_pow_self.le)

/-- Run the actual checker on the joint query, with bounds independent of the
choice of layer, root state, address map, and queried values. -/
theorem coefficient_query_runs_bounded (x : Fin n → Bool) (z : Fin L → ℕ)
    (hz : ∀ l, z (addr l) < 2^W) (e : Label n n (States C n) →₀ ℕ)
    (he : ∀ l, z (addr l) = e l) :
    let c := checker d h addr W
    let k := Flags n n (States C n)
    let aux := scalarInputs c (query x z W)
    ∃ t ≤ 2^(timeExponent C n L W),
      SpaceRun countCircuit.standalone (stackBound C n L W) t (some countCircuit.entry)
        (bank aux (digits k 0) (digits (k+1) 0) [] []) none
        (bank aux (digits k 0) (digits (k+1) ((labelQuery d h x).coeff e).toNat) [] []) := by
  obtain ⟨t, ht, hr⟩ := coefficient_query_runs d h addr x z hz e he
  exact ⟨t, ht.trans (checker_time_le d h addr W), hr.mono_cap (checker_stackLimit_le d h addr W)⟩

theorem flagCount_polynomial (C : ℕ) : PolynomiallyBounded (flagCount C) := by
  let hn := PolynomiallyBounded.id
  let hS := hn.pow (C+5)
  exact ((hn.mul hn).mul hS).mul ((hn.mul (.const 2)).add ((hn.mul hS).mul hS))

theorem rowBound_polynomial (C : ℕ) : PolynomiallyBounded (rowBound C) := by
  let hn := PolynomiallyBounded.id
  let hS := hn.pow (C+5)
  let hV := hn.mul (.const 2)
  exact hV.add ((hS.mul hV).add ((hn.pow 2).mul (hS.pow 3)))

variable {width labels : ℕ → ℕ}

theorem gateBound_polynomial (C : ℕ) (hW : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n ↦ gateBound C n (width n)) := by
  let hk := flagCount_polynomial C
  let hr := rowBound_polynomial C
  let cells := hr.mul (hk.add (.const 1))
  let wires := hk.add cells
  let hLit := hk.add (hk.mul (((PolynomiallyBounded.const 5).mul hk).add (.const 4)))
  let hLen := (PolynomiallyBounded.const 1).add (hk.mul (hk.add (.const 4)))
  let hCNF := (((PolynomiallyBounded.const 3).mul hLit).add
    ((PolynomiallyBounded.const 3).mul hLen)).add (.const 4)
  exact (PolynomiallyBounded.const 4).mul
    (((((wires.mul ((hW.mul (.const 3)).add (.const 3))).add wires).add
      (hk.mul (wires.mul (.const 8)))).add ((cells.mul (.const 10)).add (.const 2))).add hCNF)

theorem adviceBound_polynomial (C : ℕ) (hL : PolynomiallyBounded labels)
    (hW : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n ↦ adviceBound C n (labels n) (width n)) := by
  let hg := gateBound_polynomial C hW
  let hu := PolynomiallyBounded.id.add (hL.mul hW)
  let total := ((hg.add hu).add (flagCount_polynomial C)).add (.const 2)
  exact (hg.add (.const 2)).mul (((PolynomiallyBounded.const 2).mul total).add (.const 3))

theorem choiceBound_polynomial (C : ℕ) (hL : PolynomiallyBounded labels)
    (hW : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n ↦ choiceBound C n (labels n) (width n)) := by
  let hk := flagCount_polynomial C
  let hu := PolynomiallyBounded.id.add (hL.mul hW)
  let ha := adviceBound_polynomial C hL hW
  let hg := (gateBound_polynomial C hW).add (.const 2)
  exact (((PolynomiallyBounded.const 32).mul ((((ha.add hg).add hu).add hk).add (.const 1))).add
    ((PolynomiallyBounded.const 8).mul hk)).add (.const 9)

theorem stackBound_polynomial (C : ℕ) (hL : PolynomiallyBounded labels)
    (hW : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n ↦ stackBound C n (labels n) (width n)) :=
  (((PolynomiallyBounded.id.add (hL.mul hW)).add (adviceBound_polynomial C hL hW)).add
    ((flagCount_polynomial C).add (.const 1))).add (choiceBound_polynomial C hL hW)

theorem timeExponent_polynomial (C : ℕ) (hL : PolynomiallyBounded labels)
    (hW : PolynomiallyBounded width) :
    PolynomiallyBounded (fun n ↦ timeExponent C n (labels n) (width n)) :=
  (flagCount_polynomial C).add (choiceBound_polynomial C hL hW)

end ParseOracle

end VPVNP
end Computability
end OAI
