import OAI.Computability.VPVNP.ParseOracleFlags
import OAI.Computability.VPVNP.OracleTallyCircuit
import OAI.Computability.VPVNP.OracleBinaryTarget
import OAI.Computability.VPVNP.OracleCNFExpr
import OAI.Computability.VPVNP.VerifierMachineSplice

/-!
# A polynomial-size Boolean checker for coefficient queries

The query contains the input word and a fixed-width binary exponent at each
label address. Guess bits select events. Static advice supplies the incidence
clauses and the terminal and label tags of each event. The circuit accepts
exactly those flags whose leaf and production tallies match the query.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace ParseOracle

open ParseGrammar VerifierNetwork HardnessCNF
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr.eval Expr.size)
open scoped Classical

variable {m D k L W : ℕ} {H : Type} [Fintype H]
/-- A paired input variable indexed by a word position and one of its two Boolean values. -/
abbrev Var (m : ℕ) := Fin m × Bool
/-- A terminal or binary production label for the grammar on the paired input variables through
degree `D`. -/
abbrev Label (m D : ℕ) (H : Type) := GrammarLabel (Var m) H D
/-- A tally row indexed by either a paired input variable or a grammar production label. -/
abbrev Row (m D : ℕ) (H : Type) := Var m ⊕ Label m D H
/-- The checker input addresses for the public word and packed label exponents, followed by a
separate address space for the guessed event flags. -/
abbrev Input (m L W k : ℕ) := Fin (m + L * W) ⊕ Fin k

/-- Public query layout, with the word first and little-endian label exponents next. -/
def query (x : Fin m → Bool) (z : Fin L → ℕ) (W : ℕ) : Fin (m + L * W) → Bool :=
  Fin.append x fun j ↦ let ij := finProdFinEquiv.symm j; (z ij.1).testBit ij.2.val

/-- Test whether the candidate event at a flag address carries the terminal or production tag
counted by the given row. -/
noncomputable def mask (M : ParseOracleMetadata (Var m) H D k) :
    Row m D H → Fin k → Bool
  | .inl v, i => decide (M.terminal i = some v)
  | .inr l, i => decide (M.label i = some l)

/-- The queried count at each terminal and production. -/
noncomputable def wanted (addr : Label m D H → Fin L) (x : Fin m → Bool)
    (z : Fin L → ℕ) : Row m D H → ℕ :=
  Sum.elim (pairedExponent x) (z ∘ addr)

private def targetExpr (addr : Label m D H → Fin L) (r : Row m D H) (j : Fin (k+1)) :
    Expr (Input m L W k) :=
  match r with
  | .inl (i, b) =>
    let x : Expr (Input m L W k) := .input (.inl (Fin.castAdd (L*W) i))
    let matchingBit := if b then x else .not x
    if j.val = 0 then .not matchingBit else if j.val = 1 then matchingBit else .const false
  | .inr l =>
    OracleBinaryTarget.expr (fun t : Fin W ↦ .inl (Fin.natAdd m (finProdFinEquiv (addr l, t)))) j.val

omit [Fintype H] in
private theorem target_eval (addr : Label m D H → Fin L) (x : Fin m → Bool) (z : Fin L → ℕ)
    (hz : ∀ l, z (addr l) < 2^W) (flags : Fin k → Bool) (r : Row m D H) (j : Fin (k+1)) :
    (targetExpr addr r j).eval (Sum.elim (query x z W) flags) = decide (wanted addr x z r = j.val) := by
  rcases r with ⟨i,b⟩ | l
  · cases b <;> cases hx : x i <;> by_cases h₀ : j.val = 0 <;> by_cases h₁ : j.val = 1 <;>
      simp [targetExpr, wanted, pairedExponent_apply, query, Expr.eval, hx, h₀, h₁] <;> omega
  · apply OracleBinaryTarget.expr_eval _ _ _ (hz l)
    intro i
    simp only [Sum.elim_inl, query, Fin.append_right, Equiv.symm_apply_apply]

private def initExpr (addr : Label m D H → Fin L) :
    OracleTally.Input (Row m D H) k → Expr (Input m L W k)
  | .inl i => .input (.inr i)
  | .inr (r,j) => targetExpr addr r j

private noncomputable def tallyInput (addr : Label m D H → Fin L) (W k : ℕ) :
    Frame (Input m L W k) (OracleTally.Input (Row m D H) k) :=
  (Frame.initial id).step (initExpr addr)

private noncomputable def tallyFrame (M : ParseOracleMetadata (Var m) H D k)
    (addr : Label m D H → Fin L) (W : ℕ) : Frame (Input m L W k) Unit :=
  (OracleTally.frame (mask M)).subst (tallyInput addr W k)

private def finish (M : ParseOracleMetadata (Var m) H D k) (_ : Unit) :
    Expr (Input m L W k ⊕ Unit) :=
  .and (.input (.inr ())) (OracleCNFExpr.formula (fun i ↦ .inl (.inr i)) M.clauses)

/-- The query evaluator is independent of all actual queried exponent and word values. -/
noncomputable def frame (M : ParseOracleMetadata (Var m) H D k)
    (addr : Label m D H → Fin L) (W : ℕ) : Frame (Input m L W k) Unit :=
  (tallyFrame M addr W).withInput.step (finish M)

omit [Fintype H] in
private theorem rowCount_mask (M : ParseOracleMetadata (Var m) H D k)
    (flags : Fin k → Bool) (r : Row m D H) :
    OracleTally.rowCount (mask M) flags r =
      Sum.elim (tallyFlags M.terminal flags) (tallyFlags M.label flags) r := by
  cases r <;> simp only [OracleTally.rowCount, mask, Sum.elim_inl, Sum.elim_inr,
    tallyFlags_apply, Finset.card_filter, Bool.and_eq_true, decide_eq_true_eq, and_comm]

theorem frame_eval_iff (M : ParseOracleMetadata (Var m) H D k)
    (addr : Label m D H → Fin L) (x : Fin m → Bool) (z : Fin L → ℕ) (hz : ∀ l, z (addr l) < 2^W)
    (e : Label m D H →₀ ℕ) (he : ∀ l, z (addr l) = e l) (flags : Fin k → Bool) :
    (frame M addr W).eval (Sum.elim (query x z W) flags) () = true ↔
      M.Accepts (pairedExponent x) e flags := by
  let bits := Sum.elim (query x z W) flags
  have hi : (tallyInput addr W k).eval bits =
      Sum.elim flags (Function.uncurry fun r j ↦ decide (wanted addr x z r = j.val)) := by
    funext i
    cases i with
    | inl i => simp [tallyInput, initExpr, Expr.eval, bits]
    | inr ij =>
      have hi0 : (Frame.initial (id : Input m L W k → _)).eval bits = bits :=
        funext fun _ ↦ Frame.initial_eval ..
      rw [tallyInput, Frame.step_eval, hi0]
      exact target_eval addr x z hz flags ij.1 ij.2
  change (frame M addr W).eval bits () = true ↔ _
  rw [frame, Frame.step_eval]
  simp only [finish, Expr.eval, Bool.and_eq_true, Frame.withInput_eval_inr, OracleCNFExpr.formula_eval_iff]
  have hflags : (tallyFrame M addr W).withInput.eval bits ∘ (fun i : Fin k ↦ .inl (.inr i)) = flags := by
    funext i
    simp [bits]
  rw [hflags, tallyFrame, Frame.subst_eval, hi, OracleTally.frame_eval_iff,
    OracleTally.rowCountsOK_oneHot_iff]
  simp only [rowCount_mask, wanted, Sum.forall, Sum.elim_inl, Sum.elim_inr,
    Function.comp_apply, he, ParseOracleMetadata.Accepts, DFunLike.ext_iff]
  tauto

omit [Fintype H] in
private theorem init_size_le (addr : Label m D H → Fin L) (u : OracleTally.Input (Row m D H) k) :
    (initExpr (W := W) addr u).size ≤ W*3 + 3 := by
  rcases u with i | ⟨r,j⟩
  · change 1 ≤ _; omega
  · cases r with
    | inl v =>
      rcases v with ⟨i,b⟩
      cases b <;> by_cases h₀ : j.val = 0 <;> by_cases h₁ : j.val = 1 <;>
        simp [initExpr, targetExpr, h₀, h₁, Expr.size]
    | inr l => exact (OracleBinaryTarget.expr_size_le _ _).trans (by omega)

/-- The frame size is polynomial in the static flag count, row count, exponent
word width, and length of the incidence formula. -/
theorem frame_size_le (M : ParseOracleMetadata (Var m) H D k)
    (addr : Label m D H → Fin L) (W : ℕ) :
    let r := Fintype.card (Row m D H)
    (frame M addr W).size ≤
      ((k + r*(k+1))*(W*3+3) + (k + r*(k+1)) + k*((k+r*(k+1))*8) +
        (r*(k+1)*10+2) + (3*literalCount M.clauses + 3*M.clauses.length+4)) := by
  have hinit := Frame.step_size_le (Frame.initial (id : Input m L W k → _)) (initExpr addr)
    (W*3+3) (fun u ↦ init_size_le addr u)
  have hin : Fintype.card (OracleTally.Input (Row m D H) k) =
      k + Fintype.card (Row m D H)*(k+1) := by
    change Fintype.card (Fin k ⊕ Row m D H × Fin (k+1)) = _
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
  rw [Frame.initial_size, zero_add, hin] at hinit
  change (tallyInput addr W k).size ≤ _ at hinit
  have hscan := OracleTally.frame_size_le (mask M)
  have hfinish := Frame.step_size_le (tallyFrame M addr W).withInput (finish M)
    (3*literalCount M.clauses+3*M.clauses.length+4) (by
      intro i
      have h := OracleCNFExpr.formula_size_le (W := Input m L W k ⊕ Unit) (fun j ↦ .inl (.inr j)) M.clauses
      change 1 + _ + 1 ≤ _
      omega)
  simp only [Frame.withInput_size, tallyFrame, Frame.subst_size,
    Fintype.card_unit, one_mul] at hfinish
  change (frame M addr W).size ≤ _ at hfinish
  omega

/-- The circuit size is polynomial in the static flag count, row count, exponent
word width, and length of the incidence formula. -/
theorem circuitSize_le (M : ParseOracleMetadata (Var m) H D k)
    (addr : Label m D H → Fin L) (W : ℕ) :
    let r := Fintype.card (Row m D H)
    (frame M addr W).circuitSize () ≤ 4 *
      ((k + r*(k+1))*(W*3+3) + (k + r*(k+1)) + k*((k+r*(k+1))*8) +
        (r*(k+1)*10+2) + (3*literalCount M.clauses + 3*M.clauses.length+4)) :=
  ((frame M addr W).circuitSize_le ()).trans (Nat.mul_le_mul_left _ (frame_size_le M addr W))

end ParseOracle

end VPVNP
end Computability
end OAI
