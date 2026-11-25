import OAI.Computability.BorderVNP.CrossingCoefficientFrame
import OAI.Computability.BorderVNP.CrossingFusionVerifierAPI

/-!
# Wiring a local Fock-space coefficient verifier to a fused crossing

Terminal selectors decode the chosen wire state from a polynomial-size read-only table.
An old occupation mask is zero-extended to the common Fock space, the orientation fixes
the row and column, and invalid padded mode numbers suppress both output flags. The
reverse marked cut exchanges the two flags when its integral orientation sign is negative.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.KernelWrapper

open Signed Lemmata.FockCircuits Lemmata.FockCircuits.FiniteIdentity
open Lemmata.FockCircuits.CrossingCircuit
open VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit

variable {q H E g : ℕ} (w : WireStates H q)

private abbrev Input (q H E g : ℕ) := FusionStage.Query q H E ⊕ Fin g

private noncomputable def rom (E g : ℕ) (i : Fin (E+H)) : Expr (Input q H E g) :=
  Expr.disjoin (Finset.univ.toList.map fun a : Fin q =>
    if i.val ∈ (w.labels E a).val then .input (.inl (.inl a)) else .const false)

private theorem rom_eval (x : Fin q) (j : Fin (2*H)) (old : EnergyState E)
    (next : EnergyState (E+H)) (y : Fin g → Bool) (i : Fin (E+H)) :
    (rom w E g i).eval (Sum.elim (FusionStage.queryBits x j old next) y) =
      MaskCounter.mask (w.labels E x) i := by
  apply Bool.eq_iff_iff.mpr
  simp only [rom, Expr.eval_disjoin_true, List.mem_map, Finset.mem_toList, Finset.mem_univ, true_and,
    MaskCounter.mask, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨a,rfl⟩, he⟩
    split_ifs at he with ha
    · have hax : a = x := of_decide_eq_true he
      exact hax ▸ ha
    · contradiction
  · intro h
    refine ⟨_, ⟨x,rfl⟩, ?_⟩
    rw [ite_eq_left h]
    simp [Expr.eval, FusionStage.queryBits]

private def oldBit (q H E g : ℕ) (i : Fin (E+H)) : Expr (Input q H E g) :=
  if h : i.val < E then .input (.inl (.inr (.inr (.inl ⟨i,h⟩)))) else .const false

private def newBit (q H E g : ℕ) (i : Fin (E+H)) : Expr (Input q H E g) :=
  .input (.inl (.inr (.inr (.inr i))))

private theorem oldBit_eval (x : Fin q) (j : Fin (2*H)) (old : EnergyState E)
    (next : EnergyState (E+H)) (y : Fin g → Bool) (i : Fin (E+H)) :
    (oldBit q H E g i).eval (Sum.elim (FusionStage.queryBits x j old next) y) =
      MaskCounter.mask (cutoffEmbedding (Nat.le_add_right E H) old) i := by
  change _ = decide (i.val ∈ old.val)
  by_cases h : i.val < E
  · simp [oldBit, h, Expr.eval, FusionStage.queryBits]
  · have hs := Finset.mem_powerset.mp (cutoffEmbedding (E := E) le_rfl old).property
    have hn : i.val ∉ old.val := fun hm => h (Finset.mem_range.mp (hs hm))
    simp [oldBit, h, Expr.eval, hn]

private def newIndex (next : EnergyState (E+H)) : Index (E+H) := cutoffEmbedding le_rfl next
private def oldIndex (old : EnergyState E) : Index (E+H) := cutoffEmbedding (Nat.le_add_right E H) old

private noncomputable def inputs (E g : ℕ) (oldFirst : Bool) :
    CoefficientFrame.Query (E+H) w.weight ⊕ Fin g → Expr (Input q H E g)
  | .inr k => .input (.inr k)
  | .inl (.inl r) => .input (.inl (.inr (.inl (Fin.castLE w.weight_le r))))
  | .inl (.inr (.inl i)) => rom w E g i
  | .inl (.inr (.inr (.inl i))) => if oldFirst then oldBit q H E g i else newBit q H E g i
  | .inl (.inr (.inr (.inr i))) => if oldFirst then newBit q H E g i else oldBit q H E g i

private noncomputable def wired (E g : ℕ) (oldFirst : Bool) :
    Frame (Input q H E g) (CoefficientFrame.Query (E+H) w.weight ⊕ Fin g) :=
  (Frame.initial id).step (inputs w E g oldFirst)

private theorem wired_eval (oldFirst : Bool) (x : Fin q) (j : Fin (2*H)) (hj : j.val < w.weight)
    (old : EnergyState E) (next : EnergyState (E+H)) (y : Fin g → Bool) :
    (wired w E g oldFirst).eval (Sum.elim (FusionStage.queryBits x j old next) y) =
      Sum.elim (CoefficientFrame.query ⟨j,hj⟩ (w.labels E x)
        (if oldFirst then oldIndex old else newIndex next)
        (if oldFirst then newIndex next else oldIndex old)) y := by
  funext v
  have he (z : Input q H E g → Bool) : (Frame.initial id).eval z = z :=
    funext (fun i => Frame.initial_eval id z i)
  simp only [wired, Frame.step_eval, he]
  rcases v with (r | i | i | i) | k
  · simp [inputs, Expr.eval, FusionStage.queryBits, CoefficientFrame.query, Fin.ext_iff, eq_comm]
  · exact rom_eval w x j old next y i
  · cases oldFirst
    · rfl
    · exact oldBit_eval x j old next y i
  · cases oldFirst
    · exact oldBit_eval x j old next y i
    · rfl
  · rfl

private noncomputable def goodMode (E g : ℕ) : Expr (Input q H E g ⊕ Bool) :=
  Expr.disjoin (Finset.univ.toList.map fun r : Fin w.weight =>
    .input (.inl (.inl (.inr (.inl (Fin.castLE w.weight_le r))))))

private theorem goodMode_eval (x : Fin q) (j : Fin (2*H)) (old : EnergyState E)
    (next : EnergyState (E+H)) (y : Fin g → Bool) (flags : Bool → Bool) :
    (goodMode w E g).eval (Sum.elim (Sum.elim (FusionStage.queryBits x j old next) y) flags) =
      decide (j.val < w.weight) := by
  apply Bool.eq_iff_iff.mpr
  simp only [goodMode, Expr.eval_disjoin_true, List.mem_map, Finset.mem_toList, Finset.mem_univ,
    true_and, decide_eq_true_eq]
  constructor
  · rintro ⟨_, ⟨r,rfl⟩, he⟩
    have hr : Fin.castLE w.weight_le r = j := of_decide_eq_true he
    exact hr ▸ r.isLt
  · intro h
    refine ⟨_, ⟨⟨j,h⟩,rfl⟩, ?_⟩
    change decide (Fin.castLE w.weight_le (⟨j,h⟩ : Fin w.weight) = j) = true
    simp

private def orientationSign (W : ℕ) (reverse left : Bool) : ℤ :=
  if reverse && left then -sigma W else 1

private theorem unit_sign (W : ℕ) (reverse left : Bool) :
    orientationSign W reverse left = 1 ∨ orientationSign W reverse left = -1 := by
  have h := sigma_mul_self W
  have h' : sigma W = 1 ∨ sigma W = -1 := by
    have hp : (sigma W - 1) * (sigma W + 1) = 0 := by nlinarith
    rcases mul_eq_zero.mp hp with h | h <;> omega
  cases reverse <;> cases left <;> simp [orientationSign]
  omega

private theorem value_swap {z : ℤ} (hz : z = 1 ∨ z = -1) (o : Bool → Bool) :
    FusionStage.signValue (fun b => o (if z = -1 then !b else b)) = z * CoefficientFrame.value o := by
  rcases hz with rfl | rfl <;> simp [FusionStage.signValue, CoefficientFrame.value]

/-- Input decoding, orientation and padded-mode checks around a signed Fock verifier. -/
noncomputable def frame (reverse left : Bool)
    (f : Frame (CoefficientFrame.Query (E+H) w.weight ⊕ Fin g) Bool) :
    Frame (Input q H E g) Bool :=
  ((f.subst (wired w E g (reverse == left))).withInput).step fun b =>
    .and (goodMode w E g) (.input (.inr (if orientationSign w.weight reverse left = -1 then !b else b)))

private theorem frame_flags (reverse left : Bool)
    (f : Frame (CoefficientFrame.Query (E+H) w.weight ⊕ Fin g) Bool)
    (x : Fin q) (j : Fin (2*H)) (old : EnergyState E) (next : EnergyState (E+H)) (y : Fin g → Bool) :
    (frame w reverse left f).eval (Sum.elim (FusionStage.queryBits x j old next) y) =
      fun b => decide (j.val < w.weight) &&
        (f.subst (wired w E g (reverse == left))).eval (Sum.elim (FusionStage.queryBits x j old next) y)
          (if orientationSign w.weight reverse left = -1 then !b else b) := by
  let z := Sum.elim (FusionStage.queryBits x j old next) y
  let F := f.subst (wired w E g (reverse == left))
  have h : F.withInput.eval z = Sum.elim z (F.eval z) := by
    funext a
    cases a <;> simp
  funext b
  change ((F.withInput.step _).eval z b) = _
  rw [Frame.step_eval, h]
  simp only [Expr.eval, goodMode_eval, Sum.elim_inr, z, F]

/-- The signed sum of the wired verifier is exactly the specified padded coefficient. -/
theorem frame_sum (reverse left : Bool)
    (f : Frame (CoefficientFrame.Query (E+H) w.weight ⊕ Fin g) Bool)
    (hf : ∀ (r : Fin w.weight) (A I J : Index (E+H)),
      ∑ y : Fin g → Bool, CoefficientFrame.value (f.eval (Sum.elim (CoefficientFrame.query r A I J) y)) =
        if left then markedMode ℤ (E+H) w.weight r (dualState ℤ (E+H) A.val) I J
        else oppositeMode ℤ (E+H) w.weight r (dualSign A.val • Pi.single A 1) I J)
    (x : Fin q) (j : Fin (2*H)) (old : EnergyState E) (next : EnergyState (E+H)) :
    (∑ y : Fin g → Bool, FusionStage.signValue ((frame w reverse left f).eval
      (Sum.elim (FusionStage.queryBits x j old next) y))) =
      if hj : j.val < w.weight then w.factors E reverse left (⟨j,hj⟩,next) x old else 0 := by
  simp_rw [frame_flags]
  by_cases h : j.val < w.weight
  · simp only [h, decide_true, Bool.true_and, dite_true, Frame.subst_eval, wired_eval w _ _ _ h]
    simp_rw [value_swap (unit_sign ..), ← Finset.mul_sum, hf]
    cases reverse <;> cases left <;> simp [orientationSign, WireStates.factors, oldIndex, newIndex]
    all_goals first | rfl | exact Or.inl rfl
  · simp [h, FusionStage.signValue]

private theorem inputs_size (oldFirst : Bool) (i : CoefficientFrame.Query (E+H) w.weight ⊕ Fin g) :
    (inputs w E g oldFirst i).size ≤ 2*q+1 := by
  rcases i with (r | i | i | i) | k
  · simp [inputs, Expr.size]
  · have hb := Expr.size_disjoin_le (Finset.univ.toList.map fun a : Fin q =>
        if i.val ∈ (w.labels E a).val then Expr.input (.inl (.inl a) : Input q H E g) else .const false)
        1 (by intro e he; obtain ⟨a,_,rfl⟩ := List.mem_map.mp he; split_ifs <;> rfl)
    simpa [inputs, rom, Nat.mul_comm] using hb
  · by_cases hi : i.val < E <;> cases oldFirst <;> simp [inputs, oldBit, newBit, hi, Expr.size]
  · by_cases hi : i.val < E <;> cases oldFirst <;> simp [inputs, oldBit, newBit, hi, Expr.size]
  · simp [inputs, Expr.size]

/-- The ROM and padded-mode check add polynomially many gates to the underlying kernel. -/
theorem frame_size (reverse left : Bool)
    (f : Frame (CoefficientFrame.Query (E+H) w.weight ⊕ Fin g) Bool) :
    (frame w reverse left f).size ≤ f.size + (w.weight+3*(E+H)+g)*(2*q+1) + 2*(2*w.weight+3) := by
  have hi := Frame.step_size_le (Frame.initial (id : Input q H E g → _))
    (inputs w E g (reverse == left)) _ (inputs_size w _)
  have hw : (wired w E g (reverse == left)).size ≤ (w.weight+3*(E+H)+g)*(2*q+1) := by
    change (wired w E g (reverse == left)).size ≤ _ at hi
    simp only [Frame.initial_size, zero_add, CoefficientFrame.Query, Fintype.card_sum, Fintype.card_fin] at hi
    convert hi using 1
    ring
  have hv : (goodMode w E g).size ≤ 2*w.weight+1 := by
    apply (Expr.size_disjoin_le _ 1 (by intro e he; obtain ⟨_,_,rfl⟩ := List.mem_map.mp he; rfl)).trans
    simp [Nat.mul_comm]
  have bound := Frame.step_size_le (f.subst (wired w E g (reverse == left))).withInput
    (fun b : Bool => .and (goodMode w E g) (.input (.inr
      (if orientationSign w.weight reverse left = -1 then !b else b)))) (2*w.weight+3)
      (fun _ => by simp only [Expr.size]; omega)
  change (frame w reverse left f).size ≤ _ at bound
  simp only [Frame.withInput_size, Frame.subst_size, Fintype.card_bool] at bound
  omega

end Crossing.KernelWrapper

end BorderVNP
end Computability
end OAI
