import OAI.ThreeFlat.Diagonal.TraceIssueRows
import OAI.ThreeFlat.Diagonal.TracePairRead

namespace OAI
/-! # Physical two-row checker for all fixed native opcodes -/

namespace ThreeFlat.Diagonal.TracePair

open TraceBanks TraceRows TraceIssue TraceWords Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w p r k : ℕ}

private def haltFlag : StepResult w p r → Bool
  | .halt _ => true
  | .move .. => false

private theorem haltFlag_eq (q : StepResult w p r) :
    (decide (q.tag = .accept) || decide (q.tag = .result)) = haltFlag q := by
  cases q with
  | halt r => cases r <;> rfl
  | move e s => cases e with
    | tick | read | write => rfl
    | choice b => cases b <;> rfl

private theorem current_ne_pad (s : CPU w p r) (q : StepResult w p r) :
    current s q ≠ .pad := by cases q <;> simp [current]

variable (h : 3 ≤ w+1) (hp : p ≤ 2^(w+1)) (M : Machine w p r k)

private theorem pair_active (s : CPU w p r) (q : StepResult w p r) (y : Record w p r) (hy : nextMatches y q) :
    (pairCircuit M).2.eval (packed h hp (current s q) y) = true ↔
      haltFlag q = decide (y = .pad) ∧ Follows ((exposed M).step s) q := by
  let val := fun a => (packet M a).2.eval (packed h hp (current s q) y)
  have hv (a : Port w p r) : val (.inl a) = valuation M s q a := packet_active h hp y M s q hy a
  have hz : val (.inr false) = false := by
    simp [val, packet, tagIs_pad, current_ne_pad]
  have hz' : val (.inr true) = decide (y = .pad) := by simp [val, packet, tagIs_pad]
  have hu : ((issue M).rename Sum.inl).eval val = (issue M).eval (valuation M s q) := by
    simpa using congrArg (issue M).eval (funext hv)
  rw [pairCircuit_eval]
  change (checkExpr M).eval val = true ↔ _
  simp only [checkExpr, Expr.eval_mux, Expr.eval, hz, Bool.false_eq_true, ↓reduceIte,
    Bool.and_eq_true, same_true, hu, issue_true, hz', hv, valuation, haltFlag_eq]

private theorem pair_move_pad (s : CPU w p r) (e : Event (w+1)) :
    (pairCircuit M).2.eval (packed h hp (.move s e) .pad) = false := by
  let q : StepResult w p r := .move e s
  let val := fun a => (packet M a).2.eval (packed h hp (.move s e) .pad)
  have hz : val (.inr false) = false := by simp [val, packet, tagIs_pad]
  have hnext : val (.inr true) = true := by simp [val, packet, tagIs_pad]
  have ht (t : Tag) : val (.inl (.tag t)) = decide (q.tag = t) := by
    unfold val
    rw [packet, formulaPacket_eval, tag_current h hp (.move s e) .pad false s q (tagNumber t) rfl]
    simp [tagNumber_injective.eq_iff]
  rw [pairCircuit_eval]
  change (checkExpr M).eval val = false
  have hfalse : (same ((Expr.input (.inl (.tag .accept))).or (.input (.inl (.tag .result))))
      (Expr.input (.inr true))).eval val = false := by
    apply Bool.eq_false_iff.mpr
    simp [same_true, Expr.eval, ht, hnext, haltFlag_eq, haltFlag, q]
  simp [checkExpr, Expr.eval, hz, hfalse]

/-- All gates of the two-row checker are fixed by the machine and widths. The
input bits consist solely of the two physically packed rows. -/
theorem pairCircuit_correct (x y : Record w p r) :
    (pairCircuit M).2.eval (packed h hp x y) = true ↔ pair (exposed M) x y := by
  cases x with
  | pad =>
    simp [pairCircuit_eval, checkExpr, Expr.eval, packet, tagIs_pad, pair]
  | halt s out =>
    simpa [current, haltFlag, pair, follows_halt_iff, and_comm] using
      pair_active h hp M s (.halt out) y trivial
  | move s e =>
    cases y with
    | pad => simp [pair_move_pad, pair, before]
    | halt d out =>
      simpa [current, haltFlag, pair, before, follows_move_iff] using
        pair_active h hp M s (.move e d) (.halt d out) rfl
    | move d e' =>
      simpa [current, haltFlag, pair, before, follows_move_iff] using
        pair_active h hp M s (.move e d) (.move d e') rfl

end ThreeFlat.Diagonal.TracePair

end OAI
