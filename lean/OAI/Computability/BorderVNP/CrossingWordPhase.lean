import OAI.Computability.BorderVNP.CrossingWordPorts
import OAI.Computability.BorderVNP.CrossingMaskCounter

/-! # Exterior and normal-order signs of a padded field packet -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.Signed.WordFrame

open Lemmata.FockCircuits.FiniteIdentity (Index)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit
open VPVNP.VerifierNetwork (Frame)
open VPVNP.JointScalar (parallel parallel_size parallel_eval)

private def belowExpr {L : ℕ} (m k : Fin L) : Expr (Inputs L) :=
  .and (.not (Lookup.less _ (modePort m) (k.val+1)))
    (Expr.mux (.input (delPort m)) (.input (.inl (.inr (.inr k)))) (.input (.inl (.inr (.inl k)))))

private noncomputable def below {L : ℕ} (m : Fin L) : Frame (Inputs L) (Fin L) :=
  (Frame.initial id).step (belowExpr m)

private def lowerState {L : ℕ} (g : Padded.Packet L) (I J : Index L) : Index L :=
  ⟨(if g.1 then J.val else I.val).filter (· < g.2.1.val), Finset.mem_powerset.mpr
    ((Finset.filter_subset ..).trans (by cases h : g.1 <;> simp [Finset.mem_powerset.mp]))⟩

private theorem below_eval {L : ℕ} (m : Fin L) (A I J : Index L) (x : Witnesses L → Bool) :
    (below m).eval (pack A.val I.val J.val x) = MaskCounter.mask (lowerState (packet x m) I J) := by
  have hx : (Frame.initial (id : Inputs L → Inputs L)).eval (pack A.val I.val J.val x) =
      pack A.val I.val J.val x := by ext; simp
  funext k
  rw [below, Frame.step_eval, hx, belowExpr, Expr.eval, Expr.eval, Lookup.less_eval, Expr.eval_mux]
  apply Bool.eq_iff_iff.mpr
  cases hd : x (m,.inl ()) <;> simp [MaskCounter.mask, lowerState, Expr.eval, delPort, modePort, packet, pack,
    Function.comp_def, hd, and_comm]

private theorem below_size {L : ℕ} (m : Fin L) :
    (below m).size ≤ L * (3 * Padded.width L + 12) := by
  apply (Frame.step_size_le (Frame.initial id) (belowExpr m) (3*Padded.width L+12) ?_).trans
  · simp
  intro k
  have := Lookup.less_size _ (modePort m) (k.val+1)
  simp only [belowExpr, Expr.mux, Expr.size]
  omega

/-- The number of occupied derivative orders still to be processed. -/
def remaining (T A : Finset ℕ) : ℕ := (A.filter (· ∈ T)).card

private abbrev PhasePorts (L : ℕ) := Inputs L ⊕ (Unit ⊕ Unit)

private def phaseExpr {L : ℕ} (m : Fin L) (neg : Bool) : Expr (PhasePorts L) :=
  let lower : Expr (PhasePorts L) := .input (.inr (.inl ()))
  let normal : Expr (PhasePorts L) := .and (.input (.inl (delPort m))) (.input (.inr (.inr ())))
  let minus := Expr.and (.input (.inl (.inl (.inl m)))) (Expr.mux normal (.not lower) lower)
  if neg then minus else .not minus

/-- The pair of flags recording the product of the exterior and normal-ordering signs. -/
noncomputable def phase {L : ℕ} (m : Fin L) (T : Finset ℕ) : Frame (Inputs L) Bool :=
  let lower := (MaskCounter.parity (fun _ : Fin L => true)).subst (below m)
  let tail := (MaskCounter.parity (fun i : Fin L => decide (i.val ∈ T))).subst
    (Frame.initial (fun i : Fin L => (Sum.inl (Sum.inl i) : Inputs L)))
  (parallel lower tail).withInput.step (phaseExpr m)

/-- Mathematical sign computed by the parity counters. -/
def phaseValue {L : ℕ} (m : Fin L) (T A I J : Finset ℕ) (g : Padded.Packet L) : ℤ :=
  if m.val ∈ A then
    (if g.1 then (-1 : ℤ) ^ remaining T A else 1) *
      insertionSign g.2.1.val ((if g.1 then J else I).erase g.2.1.val)
  else 1

private theorem erase_lower (S : Finset ℕ) (k : ℕ) :
    (S.erase k).filter (· < k) = S.filter (· < k) := by ext; simp; omega

private theorem sign_flag (n : ℕ) (b : Bool) :
    flag ((-1 : ℤ)^n) b = if b then decide (n%2=1) else !(decide (n%2=1)) := by
  rw [neg_one_pow_eq_pow_mod_two]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> cases b <;> simp [h, flag]

theorem phase_eval {L : ℕ} (m : Fin L) (T : Finset ℕ) (A I J : Index L) (x : Witnesses L → Bool)
    (b : Bool) :
    (phase m T).eval (pack A.val I.val J.val x) b =
      flag (phaseValue m T A.val I.val J.val (packet x m)) b := by
  let g := packet x m
  let S := if g.1 then J.val else I.val
  let n := (S.filter (· < g.2.1.val)).card
  have h₁ : ((MaskCounter.parity (fun _ : Fin L => true)).subst (below m)).eval
      (pack A.val I.val J.val x) () = decide (n % 2 = 1) := by
    rw [Frame.subst_eval, below_eval]
    simpa [lowerState, n, S, g] using MaskCounter.parity_eval_index (fun _ => true) (lowerState g I J)
  have h₂ : ((MaskCounter.parity (fun i : Fin L => decide (i.val ∈ T))).subst
      (Frame.initial (fun i : Fin L => (Sum.inl (Sum.inl i) : Inputs L)))).eval (pack A.val I.val J.val x) () =
      decide (remaining T A.val % 2 = 1) := by
    rw [Frame.subst_eval]
    have hi : (Frame.initial (fun i : Fin L => (Sum.inl (Sum.inl i) : Inputs L))).eval
        (pack A.val I.val J.val x) = MaskCounter.mask A := by ext; simp [pack, MaskCounter.mask]
    rw [hi, MaskCounter.parity_eval_index (fun i => decide (i ∈ T))]
    have he : A.val.filter (fun i => decide (i ∈ T)) = A.val.filter (· ∈ T) := by ext; simp
    rw [he]
    rfl
  have hr : (phase m T).eval (pack A.val I.val J.val x) b =
      let minus := decide (m.val ∈ A.val) &&
        (if g.1 && decide (remaining T A.val % 2 = 1) then !(decide (n % 2 = 1)) else decide (n % 2 = 1))
      if b then minus else !minus := by
    cases b <;>
      simp only [phase, Frame.step_eval, phaseExpr, Bool.false_eq_true, ite_false, ite_true, Expr.eval,
        Expr.eval_mux, Frame.withInput_eval_inl, Frame.withInput_eval_inr, parallel_eval, Sum.elim_inl,
        Sum.elim_inr, h₁, h₂] <;> rfl
  rw [hr]
  have he : insertionSign g.2.1.val (S.erase g.2.1.val) = (-1)^n := by rw [insertionSign, erase_lower]
  by_cases hm : m.val ∈ A.val
  · simp only [phaseValue, hm, ite_true, decide_true, Bool.true_and]
    change _ = flag ((if g.1 then (-1:ℤ) ^ remaining T A.val else 1) * insertionSign g.2.1.val (S.erase g.2.1.val)) b
    rw [he]
    cases hd : g.1
    · simp [sign_flag]
    · simp only [ite_true, Bool.true_and, ← pow_add, sign_flag]
      rcases Nat.mod_two_eq_zero_or_one n with hn | hn <;>
        rcases Nat.mod_two_eq_zero_or_one (remaining T A.val) with ht | ht <;> cases b <;>
        simp [Nat.add_mod, hn, ht]
  · cases b <;> simp [phaseValue, hm, flag]

theorem phase_size {L : ℕ} (m : Fin L) (T : Finset ℕ) : (phase m T).size ≤ 120*(L+1)^2 := by
  unfold phase
  apply (Frame.step_size_le _ _ 20 (fun b => ?_)).trans
  · simp only [Frame.withInput_size, parallel_size, Frame.subst_size, Frame.initial_size, zero_add,
      Fintype.card_bool]
    have h₁ := MaskCounter.parity_size (fun _ : Fin L => true)
    have h₂ := MaskCounter.parity_size (fun i : Fin L => decide (i.val ∈ T))
    have h₃ := below_size m
    unfold Padded.width at h₃
    nlinarith
  · cases b <;> simp [phaseExpr, Expr.mux, Expr.size]

end Crossing.Signed.WordFrame

end BorderVNP
end Computability
end OAI
