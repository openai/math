import OAI.Computability.VPVNP.OracleBinaryTarget
import OAI.Computability.VPVNP.FixedLabelReadback
import OAI.Computability.VPVNP.LiveHeaderBits

/-!
# A signed coefficient circuit for the fixed motif rows

The row selector and the motif exponent wires may be placed anywhere in the
joint query. The sparse tables and their integer coefficients are fixed for
the motif. The circuit compares one unsigned witness against the selected
positive or negative part. Repeated table keys are combined using the same
integer lookup as the scalar reader.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace JointScalar.Motif

open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open JointLabelSystem.FixedRows (tableLookup)

variable {σ : Type*} {q m W k : ℕ}

/-- Sparse representation of one motif equation as exponent vectors paired with integer
coefficients. -/
abbrev Table (m : ℕ) := List ((Fin m → ℕ) × ℤ)

/-- Natural magnitude of the selected sign of an integer, equal to zero when that sign
contributes nothing. -/
def part (negative : Bool) (c : ℤ) : ℕ := (if negative then -c else c).toNat

/-- Compare an unsigned word to a static threshold, from the high bit down.
Every level uses just one copy of the lower-bit comparison. -/
def below : {k : ℕ} → (Fin k → σ) → ℕ → Expr σ
  | 0, _, b => .const (decide (0 < b))
  | k+1, wire, b =>
    let highZero := Expr.not (.input (wire (Fin.last k)))
    let low := wire ∘ Fin.castSucc
    if b ≤ 2^k then .and highZero (below low b)
    else .or highZero (below low (b-2^k))

theorem below_eval (wire : Fin k → σ) (b u : ℕ) (hu : u < 2^k) (x : σ → Bool)
    (hw : ∀ j, x (wire j) = u.testBit j.val) : (below wire b).eval x = decide (u < b) := by
  induction k generalizing b u with
  | zero =>
    obtain rfl : u = 0 := by simpa using hu
    rfl
  | succ k ih =>
    have bound : u < 2^k*2 := by simpa only [pow_succ] using hu
    have hpos := Nat.two_pow_pos k
    have hl : ∀ j : Fin k, x ((wire ∘ Fin.castSucc) j) = (u % 2^k).testBit j.val := by
      intro j
      simp [hw, j.isLt]
    have low := fun t => ih (wire ∘ Fin.castSucc) t _ (Nat.mod_lt u hpos) hl
    have high := hw (Fin.last k)
    change x (wire (Fin.last k)) = u.testBit k at high
    by_cases small : u < 2^k
    · rw [Nat.testBit_lt_two_pow small] at high
      rw [Nat.mod_eq_of_lt small] at low
      by_cases cap : b ≤ 2^k
      · simp [below, cap, Expr.eval, high, low]
      · simp [below, cap, Expr.eval, high, show u < b by omega]
    · have quotient : u / 2^k = 1 := Nat.div_eq_of_lt_le (by omega) (by simpa [Nat.mul_comm] using bound)
      have hbit : u.testBit k = true := by simp [Nat.testBit_eq_decide_div_mod_eq, quotient]
      rw [hbit] at high
      have rem : u % 2^k = u - 2^k := by
        have eq := Nat.mod_add_div u (2^k)
        rw [quotient, Nat.mul_one] at eq
        omega
      rw [rem] at low
      by_cases cap : b ≤ 2^k
      · simp [below, cap, Expr.eval, high, show ¬u < b by omega]
      · simp [below, cap, Expr.eval, high, low, show (u-2^k < b-2^k) ↔ u < b by omega]

theorem below_size (wire : Fin k → σ) (b : ℕ) : (below wire b).size = 3*k+1 := by
  induction k generalizing b with
  | zero => rfl
  | succ k ih => simp only [below]; split <;> simp only [Expr.size, ih, Nat.mul_succ] <;> omega

private def exponentMatch (wire : Fin m → Fin W → σ) (z : Fin m → ℕ) : Expr σ :=
  .not (Expr.disjoin (List.ofFn fun i => .not (OracleBinaryTarget.expr (wire i) (z i))))

private theorem exponentMatch_eval (wire : Fin m → Fin W → σ) (e z : Fin m → ℕ)
    (fit : ∀ i, z i < 2^W) (x : σ → Bool) (hx : ∀ i j, x (wire i j) = (z i).testBit j.val) :
    (exponentMatch wire e).eval x = true ↔ z = e := by
  simp only [exponentMatch, Expr.eval, Bool.not_eq_true']
  rw [Bool.eq_false_iff]
  change (¬(Expr.disjoin _).eval x = true) ↔ _
  rw [Expr.eval_disjoin_true, funext_iff]
  simp only [List.mem_ofFn, exists_exists_eq_and, Expr.eval, Bool.not_eq_true',
    OracleBinaryTarget.expr_eval _ _ _ (fit _) x (hx _), decide_eq_false_iff_not, not_exists, not_not]

private def signAndWitness (negative : σ) (wire : Fin k → σ) (c : ℤ) : Expr σ :=
  .and (if c < 0 then .input negative else .not (.input negative)) (below wire c.natAbs)

private theorem signAndWitness_eval (negative : σ) (wire : Fin k → σ) (c : ℤ) (u : ℕ)
    (hu : u < 2^k) (x : σ → Bool) (hx : ∀ j, x (wire j) = u.testBit j.val) :
    (signAndWitness negative wire c).eval x = true ↔ u < part (x negative) c := by
  cases c with
  | ofNat n =>
    have hn : ¬(n : ℤ) < 0 := by omega
    cases h : x negative <;> simp [signAndWitness, hn, Expr.eval, part, h, below_eval _ _ _ hu x hx]
  | negSucc n =>
    cases h : x negative <;> simp [signAndWitness, Expr.eval, part, h, below_eval _ _ _ hu x hx]

private def rowExpr (row : Table m) (expo : Fin m → Fin W → σ) (negative : σ)
    (witness : Fin k → σ) : Expr σ :=
  Expr.disjoin (row.map fun entry => .and (exponentMatch expo entry.1)
    (signAndWitness negative witness (tableLookup row entry.1)))

private theorem tableLookup_absent (row : Table m) (z : Fin m → ℕ) (ha : ∀ e ∈ row, e.1 ≠ z) :
    tableLookup row z = 0 := by
  unfold tableLookup
  induction row with
  | nil => rfl
  | cons e es ih =>
    simp only [List.foldl_cons, ite_eq_right (ha e (by simp))]
    exact ih (fun a h => ha a (List.mem_cons_of_mem _ h))

/-- The largest magnitude in the fixed motif table after equal keys are combined. -/
def height (rows : Fin q → Table m) : ℕ :=
  Finset.univ.sup fun o => (rows o).toFinset.sup fun e => (tableLookup (rows o) e.1).natAbs

/-- Width of an unsigned witness whose initial segment can count either sign of every
coefficient in the motif tables. -/
def witnessBits (rows : Fin q → Table m) : ℕ := Nat.clog 2 (height rows)

/-- The fixed witness width covers both polarities of every sparse lookup,
including a key absent from the table. -/
theorem part_fits (rows : Fin q → Table m) (o : Fin q) (z : Fin m → ℕ) (neg : Bool) :
    part neg (tableLookup (rows o) z) ≤ 2^(witnessBits rows) := by
  apply le_trans _ (Nat.le_pow_clog (by decide : 1 < 2) (height rows))
  by_cases key : ∃ e ∈ rows o, e.1 = z
  · obtain ⟨e, he, rfl⟩ := key
    have small (c : ℤ) : part neg c ≤ c.natAbs := by cases c <;> cases neg <;> simp [part]
    let rowHeight (j : Fin q) := (rows j).toFinset.sup fun v => (tableLookup (rows j) v.1).natAbs
    have hm : e ∈ (rows o).toFinset := List.mem_toFinset.mpr he
    have hr : (tableLookup (rows o) e.1).natAbs ≤ rowHeight o :=
      Finset.le_sup (f := fun v : (Fin m → ℕ) × ℤ => (tableLookup (rows o) v.1).natAbs) hm
    have ha : rowHeight o ≤ height rows := Finset.le_sup (f := rowHeight) (Finset.mem_univ o)
    exact (small _).trans (hr.trans ha)
  · rw [tableLookup_absent (rows o) z (fun e hm hz => key ⟨e,hm,hz⟩)]
    cases neg <;> simp [part]

private theorem rowExpr_eval (row : Table m) (expo : Fin m → Fin W → σ) (negative : σ)
    (witness : Fin k → σ) (z : Fin m → ℕ) (u : ℕ) (hz : ∀ i, z i < 2^W) (hu : u < 2^k)
    (x : σ → Bool) (he : ∀ i j, x (expo i j) = (z i).testBit j.val)
    (hw : ∀ j, x (witness j) = u.testBit j.val) :
    (rowExpr row expo negative witness).eval x = true ↔ u < part (x negative) (tableLookup row z) := by
  rw [rowExpr, Expr.eval_disjoin_true]
  constructor
  · rintro ⟨test, hm, ht⟩
    obtain ⟨e, _, rfl⟩ := List.mem_map.mp hm
    rw [Expr.eval, Bool.and_eq_true, exponentMatch_eval _ _ _ hz x he,
      signAndWitness_eval _ _ _ _ hu x hw] at ht
    exact ht.1 ▸ ht.2
  · intro hu'
    by_cases existsKey : ∃ e ∈ row, e.1 = z
    · obtain ⟨e, hm, hz'⟩ := existsKey
      refine ⟨_, List.mem_map_of_mem (f := _) hm, ?_⟩
      rw [Expr.eval, Bool.and_eq_true, exponentMatch_eval _ _ _ hz x he,
        signAndWitness_eval _ _ _ _ hu x hw, hz']
      exact ⟨rfl,hu'⟩
    · rw [tableLookup_absent row z (fun e hm he => existsKey ⟨e,hm,he⟩)] at hu'
      cases hn : x negative <;> simp [part, hn] at hu'

/-- A true selector enables one sparse row. Non-motif coordinates are checked
by the enclosing joint-query circuit. -/
def expr (rows : Fin q → Table m) (rowMatches : Fin q → Expr σ)
    (expo : Fin m → Fin W → σ) (negative : σ) (witness : Fin k → σ) : Expr σ :=
  Expr.disjoin (List.ofFn fun o => .and (rowMatches o) (rowExpr (rows o) expo negative witness))

theorem eval_selected (rows : Fin q → Table m) (rowMatches : Fin q → Expr σ)
    (expo : Fin m → Fin W → σ) (negative : σ) (witness : Fin k → σ)
    (o : Fin q) (z : Fin m → ℕ) (u : ℕ) (hz : ∀ i, z i < 2^W) (hu : u < 2^k) (x : σ → Bool)
    (hr : ∀ j, (rowMatches j).eval x = decide (j = o))
    (he : ∀ i j, x (expo i j) = (z i).testBit j.val) (hw : ∀ j, x (witness j) = u.testBit j.val) :
    (expr rows rowMatches expo negative witness).eval x = decide (u < part (x negative) (tableLookup (rows o) z)) := by
  apply Bool.eq_iff_iff.mpr
  simp [expr, Expr.eval_disjoin_true, List.mem_ofFn, Expr.eval, hr, rowExpr_eval _ _ _ _ _ _ hz hu x he hw]

/-- Addresses outside the motif range produce zero for every witness. -/
theorem eval_unselected (rows : Fin q → Table m) (rowMatches : Fin q → Expr σ)
    (expo : Fin m → Fin W → σ) (negative : σ) (witness : Fin k → σ)
    (x : σ → Bool) (hr : ∀ j, (rowMatches j).eval x = false) :
    (expr rows rowMatches expo negative witness).eval x = false := by
  rw [Bool.eq_false_iff]
  simp [expr, Expr.eval_disjoin_true, List.mem_ofFn, Expr.eval, hr]

/-- Number of expression nodes, uniformly in the table entries' magnitudes.
`R` bounds a row selector and `L` bounds the length of a sparse row. -/
def sizeBound (q m W k R L : ℕ) := q * (R + L * (m * (W*3+4) + 3*k + 8) + 3) + 1

private theorem exponentMatch_size (wire : Fin m → Fin W → σ) (z : Fin m → ℕ) :
    (exponentMatch wire z).size ≤ m * (W*3+4) + 2 := by
  have h := Expr.size_disjoin_le (List.ofFn fun i => Expr.not (OracleBinaryTarget.expr (wire i) (z i)))
    (W*3+3) (by
      intro e he
      obtain ⟨i, rfl⟩ := List.mem_ofFn.mp he
      have h := OracleBinaryTarget.expr_size_le (wire i) (z i)
      change _ + 1 ≤ _
      omega)
  simp only [List.length_ofFn, show W*3+3+1 = W*3+4 by omega] at h
  change _ + 1 ≤ _
  omega

private theorem signAndWitness_size (negative : σ) (wire : Fin k → σ) (c : ℤ) :
    (signAndWitness negative wire c).size ≤ 3*k+4 := by
  unfold signAndWitness
  split <;> simp only [Expr.size, below_size] <;> omega

private theorem rowExpr_size (row : Table m) (expo : Fin m → Fin W → σ) (negative : σ) (witness : Fin k → σ) :
    (rowExpr row expo negative witness).size ≤ row.length * (m * (W*3+4) + 3*k + 8) + 1 := by
  unfold rowExpr
  apply (Expr.size_disjoin_le _ (m * (W*3+4) + 3*k + 7) ?_).trans (by simp)
  intro e he
  obtain ⟨entry, _, rfl⟩ := List.mem_map.mp he
  have h₁ := exponentMatch_size expo entry.1
  have h₂ := signAndWitness_size negative witness (tableLookup row entry.1)
  change _ + _ + 1 ≤ _
  omega

theorem expr_size_le (rows : Fin q → Table m) (rowMatches : Fin q → Expr σ)
    (expo : Fin m → Fin W → σ) (negative : σ) (witness : Fin k → σ) (R L : ℕ)
    (hr : ∀ j, (rowMatches j).size ≤ R) (hl : ∀ j, (rows j).length ≤ L) :
    (expr rows rowMatches expo negative witness).size ≤ sizeBound q m W k R L := by
  unfold expr sizeBound
  apply (Expr.size_disjoin_le _ (R + L*(m*(W*3+4)+3*k+8)+2) ?_).trans (by simp)
  intro e he
  obtain ⟨o, rfl⟩ := List.mem_ofFn.mp he
  have h₁ := rowExpr_size (rows o) expo negative witness
  have h₂ := Nat.mul_le_mul_right (m*(W*3+4)+3*k+8) (hl o)
  have h₃ := hr o
  change _ + _ + 1 ≤ _
  omega

/-- Gate compilation of the predicate, using the joint verifier's network. -/
noncomputable def frame [Fintype σ] (rows : Fin q → Table m) (rowMatches : Fin q → Expr σ)
    (expo : Fin m → Fin W → σ) (negative : σ) (witness : Fin k → σ) : VerifierNetwork.Frame σ Unit :=
  (VerifierNetwork.Frame.initial (id : σ → σ)).step (fun _ => expr rows rowMatches expo negative witness)

theorem circuit_eval [Fintype σ] (rows : Fin q → Table m) (rowMatches : Fin q → Expr σ)
    (expo : Fin m → Fin W → σ) (negative : σ) (witness : Fin k → σ) (x : σ → Bool) :
    ((frame rows rowMatches expo negative witness).circuit ()).eval x =
      (expr rows rowMatches expo negative witness).eval x := by
  have h : (VerifierNetwork.Frame.initial (id : σ → σ)).eval x = x := by funext i; simp
  simp [frame, h]

theorem circuit_size_le [Fintype σ] (rows : Fin q → Table m) (rowMatches : Fin q → Expr σ)
    (expo : Fin m → Fin W → σ) (negative : σ) (witness : Fin k → σ) (R L : ℕ)
    (hr : ∀ j, (rowMatches j).size ≤ R) (hl : ∀ j, (rows j).length ≤ L) :
    (frame rows rowMatches expo negative witness).circuitSize () ≤ 4 * sizeBound q m W k R L := by
  apply (VerifierNetwork.Frame.circuitSize_le _ ()).trans
  apply Nat.mul_le_mul_left
  have hs := VerifierNetwork.Frame.step_size_le (VerifierNetwork.Frame.initial (id : σ → σ))
    (fun _ : Unit => expr rows rowMatches expo negative witness) _ (fun _ =>
      expr_size_le rows rowMatches expo negative witness R L hr hl)
  simpa [frame] using hs

/-- Summing over the physical little-endian witness bank yields precisely the
selected part. This includes zero coefficients and a threshold equal to the
full word capacity. -/
theorem count_selected (rows : Fin q → Table m) (rowMatches : Fin q → Expr σ)
    (expo : Fin m → Fin W → σ) (negative : σ) (witness : Fin k → σ)
    (o : Fin q) (z : Fin m → ℕ) (neg : Bool) (hz : ∀ i, z i < 2^W)
    (fit : part neg (tableLookup (rows o) z) ≤ 2^k)
    (x : (Fin k → Bool) → σ → Bool) (hn : ∀ bits, x bits negative = neg)
    (hr : ∀ bits j, (rowMatches j).eval (x bits) = decide (j = o))
    (he : ∀ bits i j, x bits (expo i j) = (z i).testBit j.val)
    (hw : ∀ bits j, x bits (witness j) = bits j) :
    (∑ bits : Fin k → Bool, ((expr rows rowMatches expo negative witness).eval (x bits)).toNat) =
      part neg (tableLookup (rows o) z) := by
  rw [← (RAMSerialization.wordBits k).sum_comp]
  let M := part neg (tableLookup (rows o) z)
  calc
    _ = ∑ u : Fin (2^k), (if u.val < M then 1 else 0) := by
      apply Finset.sum_congr rfl
      intro u _
      let bits := RAMSerialization.wordBits k u
      rw [eval_selected rows rowMatches expo negative witness o z u.val hz u.isLt
        (x bits) (hr bits) (he bits) (fun j => (hw bits j).trans (LiveHeader.testBit_wordBits u j).symm), hn]
      by_cases h : u.val < M <;> simp [← show M = part neg (tableLookup (rows o) z) from rfl, h]
    _ = M := by
      rw [Finset.sum_boole, ← Fintype.card_subtype (fun u : Fin (2^k) => u.val < M)]
      exact Fintype.card_fin_lt_of_le fit

end JointScalar.Motif

end VPVNP
end Computability
end OAI
