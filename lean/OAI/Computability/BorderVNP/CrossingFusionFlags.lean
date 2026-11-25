import OAI.Computability.BorderVNP.CrossingFusionModeFlags
import OAI.Computability.BorderVNP.CrossingFusionWitnesses
import OAI.Computability.VPVNP.VerifierMachineSplice

/-!
# Physical output flags for a fused crossing side

A shared dynamic-programming circuit ranks the final occupation mask. Fixed wires place
these bits and the mode fields into the bridge blocks, filling unused positions with
zero. A binary equality test for each label gives the actual one-hot output used by the
weighted coefficient verifier. The additional validity flag rejects unused mode codes.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.FusionFlags

open VPVNP
open VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

/-- Terminal bit fields, raw mode fields, and the final occupation mask. -/
abbrev EncodedInput (d m a E : ℕ) := (Fin d × Fin m) ⊕ (Fin d × Fin a) ⊕ Fin E

/-- A one-hot indicator for each port value and one check on all mode fields. -/
abbrev Output (d p m : ℕ) := ((Fin d ⊕ Fin p) × Fin (2^m)) ⊕ Unit

variable {d p m M E : ℕ}
local notation "Raw" => EncodedInput d m (Nat.clog 2 M) E
local notation "Ranked" => Raw ⊕ Fin (E+1)
local notation "Bus" => ((Fin d ⊕ Fin p) × Fin m) ⊕ (Fin d × Fin (Nat.clog 2 M))

/-- Physical bit representation of a legal terminal/mode tuple and final mask. -/
def encoded (x : Fin d → Fin (2^m)) (j : Fin d → Fin M) (v : StateIndex.ValidMask E) : Raw → Bool :=
  Sum.elim (fun ib => (x ib.1).val.testBit ib.2.val)
    (Sum.elim (fun ib => (j ib.1).val.testBit ib.2.val) v.val)

private theorem rankWidth (E : ℕ) : Nat.clog 2 (stateCountAt E) ≤ E+1 := by
  apply (Nat.clog_le_iff_le_pow Nat.one_lt_two).mpr
  rw [stateCountAt, ← StateIndex.count_eq_cutoff]
  exact (StateIndex.count_bound _ _).trans (Nat.pow_le_pow_right (by decide) (by omega))

private noncomputable def rankWires : Frame Raw Ranked :=
  ((StateIndex.rankFrame E).subst (Frame.initial (fun k => Sum.inr (Sum.inr k) : Fin E → Raw))).withInput

private def fieldExpr (b : CutBit d M (stateCountAt E)) : Expr Ranked :=
  match b with
  | .inl ib => .input (.inl (.inr (.inl ib)))
  | .inr i => .input (.inr (i.castLE (rankWidth E)))

variable (addr : CutBit d M (stateCountAt E) ↪ Fin p × Fin m)

private noncomputable def busExpr : Bus → Expr Ranked
  | .inl (.inl i, b) => .input (.inl (.inl (i,b)))
  | .inl (.inr i, b) => Function.extend addr fieldExpr (fun _ => .const false) (i,b)
  | .inr ib => .input (.inl (.inr (.inl ib)))

private noncomputable def busFrame : Frame Raw Bus := rankWires.step (busExpr addr)

private def outputExpr : Output d p m → Expr Bus
  | .inl (i,z) => OracleBinaryTarget.expr (fun b => .inl (i,b)) z.val
  | .inr _ => modeValidity (fun i b => .inr (i,b))

/-- The shared frame producing the physical labels for the output monomial. -/
noncomputable def frame : Frame Raw (Output d p m) := (busFrame addr).step outputExpr

private theorem field_eval (x : Fin d → Fin (2^m)) (j : Fin d → Fin M)
    (v : StateIndex.ValidMask E) (b : CutBit d M (stateCountAt E)) :
    (fieldExpr b).eval (rankWires.eval (encoded x j v)) =
      cutValueBit (j,FusionStage.maskIndex E v) b := by
  cases b with
  | inl ib => simp [fieldExpr, rankWires, Expr.eval, encoded, cutValueBit]
  | inr i =>
    have h : (Frame.initial (fun k => Sum.inr (Sum.inr k) : Fin E → Raw)).eval (encoded x j v) =
        v.val := by funext k; simp [encoded]
    simp only [fieldExpr, rankWires, Expr.eval, Frame.withInput_eval_inr, Frame.subst_eval, h,
      StateIndex.rankFrame_validMask, FusionStage.maskIndex, cutValueBit, Equiv.trans_apply, Fin.val_castLE]

private theorem bus_port (x : Fin d → Fin (2^m)) (j : Fin d → Fin M)
    (v : StateIndex.ValidMask E) (i : Fin d ⊕ Fin p) (b : Fin m) :
    (busFrame addr).eval (encoded x j v) (.inl (i,b)) =
      ((Sum.elim x (binaryBridge addr (j,FusionStage.maskIndex E v))) i).val.testBit b.val := by
  cases i with
  | inl i => simp [busFrame, busExpr, rankWires, Expr.eval, encoded]
  | inr i =>
    simp only [busFrame, Frame.step_eval, busExpr, Sum.elim_inr]
    by_cases h : (i,b) ∈ Set.range addr
    · obtain ⟨c,hc⟩ := h
      have hw := binaryBridge_bit addr (j,FusionStage.maskIndex E v) c
      rw [hc] at hw
      rw [← hc, addr.injective.extend_apply, field_eval, hw]
    · rw [Function.extend_apply' _ _ _ h, binaryBridge_unused _ _ _ h]
      rfl

/-- Each legal encoding lights precisely the selected terminal or bridge label. -/
theorem frame_flag (x : Fin d → Fin (2^m)) (j : Fin d → Fin M)
    (v : StateIndex.ValidMask E) (i : Fin d ⊕ Fin p) (z : Fin (2^m)) :
    (frame addr).eval (encoded x j v) (.inl (i,z)) =
      decide (Sum.elim x (binaryBridge addr (j,FusionStage.maskIndex E v)) i = z) := by
  rw [frame, Frame.step_eval, outputExpr]
  let u := Sum.elim x (binaryBridge addr (j,FusionStage.maskIndex E v)) i
  simpa only [Fin.ext_iff] using OracleBinaryTarget.expr_eval (fun b => Sum.inl (i,b)) z.val u.val
    u.isLt ((busFrame addr).eval (encoded x j v)) (bus_port addr x j v i)

/-- The validity output reads the original physical mode fields even on arbitrary masks. -/
theorem frame_modeValid (u : Raw → Bool) :
    (frame addr).eval u (.inr ()) = true ↔
      ∀ i : Fin d, (decoded (fun b => u (.inr (.inl (i,b))))).val < M := by
  rw [frame, Frame.step_eval, outputExpr, modeValidity_eval]
  simp [busFrame, busExpr, rankWires, Function.comp_def, Expr.eval]

/-- Every canonical mode tuple passes the validity output. -/
theorem frame_valid_encoded (x : Fin d → Fin (2^m)) (j : Fin d → Fin M)
    (v : StateIndex.ValidMask E) : (frame addr).eval (encoded x j v) (.inr ()) = true := by
  apply (frame_modeValid addr _).mpr
  intro i
  let y : Fin (2 ^ Nat.clog 2 M) := ⟨(j i).val, (j i).isLt.trans_le (Nat.le_pow_clog Nat.one_lt_two M)⟩
  have he : (fun b : Fin (Nat.clog 2 M) => (j i).val.testBit b.val) = RAMSerialization.wordBits _ y :=
    funext (fun b => LiveHeader.testBit_wordBits y b)
  change (decoded (fun b : Fin (Nat.clog 2 M) => (j i).val.testBit b.val)).val < M
  rw [he, decoded, Equiv.symm_apply_apply]
  exact (j i).isLt

/-- Explicit polynomial gate bound, including the shared state-ranking circuit, the physical
bit wiring, all one-hot equality tests, and the rejection of unused mode codes. -/
theorem frame_size :
    (frame addr).size ≤ (E+(2*E+1)*(E+2)) * (1+E*(4*E+17)) +
      ((d+p)*m + d*Nat.clog 2 M) +
      ((d+p)*2^m+1) * (m*3+2 + d*(M*(Nat.clog 2 M*3+3)+3)+2) := by
  have hwire (i : Bus) : (busExpr addr i).size ≤ 1 := by
    rcases i with ⟨i|i,b⟩ | ib
    · rfl
    · by_cases he : (i,b) ∈ Set.range addr
      · obtain ⟨c,hc⟩ := he
        simp only [busExpr, ← hc, addr.injective.extend_apply]
        cases c <;> rfl
      · simp only [busExpr, Function.extend_apply' _ _ _ he, Expr.size, le_rfl]
    · rfl
  have hbus := Frame.step_size_le rankWires (busExpr addr) 1 hwire
  have hr := StateIndex.rankFrame_size E
  have hsize (i : Output d p m) : (outputExpr (M := M) i).size ≤
      m*3+2 + d*(M*(Nat.clog 2 M*3+3)+3)+2 := by
    rcases i with ⟨i,z⟩ | ⟨⟩
    · exact (OracleBinaryTarget.expr_size_le _ _).trans (by omega)
    · exact (modeValidity_size _).trans (by omega)
  have hout := Frame.step_size_le (busFrame addr) outputExpr _ hsize
  simp only [rankWires, Frame.withInput_size, Frame.subst_size, Frame.initial_size, zero_add,
    Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, mul_one] at hbus
  simp only [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_unit] at hout
  exact hout.trans (Nat.add_le_add_right (hbus.trans (Nat.add_le_add_right hr _)) _)

end Crossing.FusionFlags

end BorderVNP
end Computability
end OAI
