import OAI.Computability.VPVNP.MacaulayReadRouter
import OAI.Computability.VPVNP.MacaulayRowIndex

/-! # Joining the three physical row blocks on the determinant engine's ABI

The first two blocks have product indices for an equation and its multiplier
monomial. The appended monomials have one index each. This proof combines the
three typed native reads without reconstructing a matrix or restricting its
queried row or column.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RankQuery.Stack.MacaulayRead

open RAMTape MacaulayRowDispatch BurstRAM Engine

variable {K : Type} [DecidableEq K] {p e rows pins mult extra cols w v B S : ℕ} {c : SliceArithmetic.Vector p e}

/-- Index the row for equation or affine pin `r` multiplied by monomial `o` in the augmented
matrix. -/
abbrev rowOf (r : Fin (rows+pins)) (o : Fin mult) : Fin ((rows+pins)*mult+extra) :=
  (finProdFinEquiv (r,o)).castAdd extra
/-- Index the powered monomial at suffix ordinal `o`, after all multiples of equations and
pins. -/
abbrev appended (o : Fin extra) : Fin ((rows+pins)*mult+extra) := o.natAdd ((rows+pins)*mult)

variable (M : Matrix (Fin ((rows+pins)*mult+extra)) (Fin cols) (Scalar c))
variable (leaf : Stacks K) (arms : Kind → FiniteRoutine (Bus K))

/-- All three local reads preserve the decoder and its coefficient advice. -/
abbrev BlockRun (kind : Kind) (rs : Reg → Word w) (i : Fin ((rows+pins)*mult+extra)) (j : Fin cols) :=
  ∃ ticks ≤ B, (arms kind).BoundedRun S ticks (frame rs [] leaf) (frame rs (scalar v (M i j)) leaf)

private theorem rowVal (r : Fin (rows+pins)) (o : Fin mult) : (rowOf (extra := extra) r o).val = r.val*mult+o.val := by
  dsimp [rowOf,finProdFinEquiv]; ac_rfl

/-- From one typed call for each row block, obtain the raw arm contract on
all addresses, with one common immutable coefficient bank. -/
theorem armCorrect_of_blocks
    (eqn : ∀ (rs : Reg → Word w) (r : Fin rows) (o : Fin mult) (j : Fin cols),
      (rs (outReg 1)).val = r.val → (rs (outReg 2)).val = o.val → (rs (outReg 3)).val = j.val →
      BlockRun (B := B) (S := S) (v := v) M leaf arms .equation rs (rowOf (r.castAdd pins) o) j)
    (affine : ∀ (rs : Reg → Word w) (r : Fin pins) (o : Fin mult) (j : Fin cols),
      (rs (outReg 1)).val = r.val → (rs (outReg 2)).val = o.val → (rs (outReg 3)).val = j.val →
      BlockRun (B := B) (S := S) (v := v) M leaf arms .affine rs (rowOf (r.natAdd rows) o) j)
    (power : ∀ (rs : Reg → Word w) (o : Fin extra) (j : Fin cols),
      (rs (outReg 2)).val = o.val → (rs (outReg 3)).val = j.val →
      BlockRun (B := B) (S := S) (v := v) M leaf arms .power rs (appended o) j) :
    ArmCorrect M w v rows pins mult B S (fun s => s = leaf) arms := by
  intro i j rs state hin hout hs
  subst state
  have params : Params rows pins mult rs := by
    intro a h
    rw [hin]
    fin_cases a <;> first | rfl | exact False.elim ((by decide : ¬ (2 ≤ (0 : Fin 8).val)) h) | exact False.elim ((by decide : ¬ (2 ≤ (1 : Fin 8).val)) h)
  have hf (bits : List Bool) : frame rs bits leaf = bank w i j bits (auxBank rs leaf) := by
    change bank w _ _ bits _ = _
    rw [show (rs (inReg 0)).val = i.val from hin 0, show (rs (inReg 1)).val = j.val from hin 1]
  have finish (u : Fin ((rows+pins)*mult+extra)) (k : Kind) (hk : (address u j rows pins mult).kind = k)
      (run : BlockRun (B := B) (S := S) (v := v) M leaf arms k rs u j) (hu : u = i) :
      ∃ z ≤ B, ∃ out, Ready w rows pins mult (fun s => s = leaf) out ∧
        (arms (address i j rows pins mult).kind).BoundedRun S z (frame rs [] leaf)
          (bank w i j (scalar v (M i j)) out) := by
    subst u
    obtain ⟨z,hz,run⟩ := run
    exact ⟨z,hz,auxBank rs leaf,⟨rs,leaf,params,rfl,rfl⟩,hk.symm ▸ hf _ ▸ run⟩
  cases i using Fin.addCases with
  | left i =>
    obtain ⟨⟨r,o⟩,rfl⟩ := finProdFinEquiv.surjective i
    cases r using Fin.addCases with
    | left r =>
      have ha : address (rowOf (extra := extra) (r.castAdd pins) o) j rows pins mult = ⟨.equation,r.val,o.val,j.val⟩ := by
        rw [rowVal]; exact original_address r o j
      change ∀ a, (rs (outReg a)).val = (address (rowOf (extra := extra) (r.castAdd pins) o) j rows pins mult).fields a at hout
      rw [ha] at hout
      exact finish _ _ (congrArg Address.kind ha) (eqn rs r o j (hout 1) (hout 2) (hout 3)) rfl
    | right r =>
      have ha : address (rowOf (extra := extra) (r.natAdd rows) o) j rows pins mult = ⟨.affine,r.val,o.val,j.val⟩ := by
        rw [rowVal]; exact affine_address r o j
      change ∀ a, (rs (outReg a)).val = (address (rowOf (extra := extra) (r.natAdd rows) o) j rows pins mult).fields a at hout
      rw [ha] at hout
      exact finish _ _ (congrArg Address.kind ha) (affine rs r o j (hout 1) (hout 2) (hout 3)) rfl
  | right o =>
    have ha : address (appended (rows := rows) (pins := pins) (mult := mult) o) j rows pins mult = ⟨.power,0,o.val,j.val⟩ := power_address ..
    change ∀ a, (rs (outReg a)).val = (address (appended (rows := rows) (pins := pins) (mult := mult) o) j rows pins mult).fields a at hout
    rw [ha] at hout
    exact finish _ _ (congrArg Address.kind ha) (power rs o j (hout 2) (hout 3)) rfl

end RankQuery.Stack.MacaulayRead

end VPVNP
end Computability
end OAI
