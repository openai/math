import OAI.Computability.BorderVNP.CrossingFusionStageFrames
import OAI.Computability.BorderVNP.CrossingFusionFlags

/-!
# Assembling the complete signed side verifier

A terminal or bridge output lights exactly one flag in its group. Each signed
stage supplies a negative flag. The acceptance output combines all the energy
and mode tests with the requirement that each local path has a nonzero sign.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Crossing.FusionStage

open VPVNP VPVNP.VerifierNetwork
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr.eval Expr.size Expr.disjoin
  Expr.eval_disjoin_true Expr.size_disjoin_le Expr.not Expr.input)

variable {m d p : ℕ} {w : WireStates (leastEnergy m) (2^m)} {left : Bool} {b : Fin d → Bool}

/-- Output monomial labels, together with the single sign flag for each stage. -/
abbrev Labels (d p m : ℕ) := ((Fin d ⊕ Fin p) × Fin (2^m)) ⊕ Fin d

private abbrev Bus (d p m : ℕ) := FusionFlags.Output d p m ⊕ (Fin d × Bool) ⊕ Fin (d+1)

private def flagSource (f : Checkers w left b) :
    FusionFlags.EncodedInput d m (Nat.clog 2 (2*leastEnergy m)) (d*leastEnergy m) → Raw f
  | .inl pair => .inl pair
  | .inr (.inl pair) => .inr (.inl pair)
  | .inr (.inr k) => .inr (.inr (.inl ⟨Fin.last d,k⟩))

private noncomputable def externalFrame (f : Checkers w left b)
    (addr : CutBit d (2*leastEnergy m) (stateCountAt (d*leastEnergy m)) ↪ Fin p × Fin m) :
    Frame (Raw f) (FusionFlags.Output d p m) := (FusionFlags.frame addr).subst (Frame.initial (flagSource f))

private theorem external_encode (f : Checkers w left b) (g : Data f) :
    (Frame.initial (flagSource f)).eval (encode f g) =
      FusionFlags.encoded g.1 g.2.1 (g.2.2.1 (Fin.last d)) := by
  funext k
  rw [Frame.initial_eval]
  rcases k with ⟨i,j⟩ | ⟨i,j⟩ | j
  · exact (LiveHeader.testBit_wordBits (g.1 i) j).symm
  · exact (LiveHeader.testBit_wordBits ((g.2.1 i).castLE (Nat.le_pow_clog Nat.one_lt_two _)) j).symm
  · rfl

private def allExpr {n : ℕ} {X : Type*} (e : Fin n → Expr X) : Expr X :=
  .not (.disjoin (List.ofFn fun i => .not (e i)))

private theorem allExpr_eval {n : ℕ} {X : Type*} (e : Fin n → Expr X) (x : X → Bool) :
    (allExpr e).eval x = true ↔ ∀ i, (e i).eval x = true := by
  rw [allExpr, Expr.eval, Bool.not_eq_true', Bool.eq_false_iff]
  change (¬ _ = true) ↔ _
  rw [Expr.eval_disjoin_true]
  simp only [List.mem_ofFn, exists_exists_eq_and, not_exists, Expr.eval, Bool.not_eq_true']
  simp

private theorem allExpr_size {n : ℕ} {X : Type*} (e : Fin n → Expr X) (N : ℕ)
    (h : ∀ i, (e i).size ≤ N) : (allExpr e).size ≤ n*(N+2)+2 := by
  have h₁ := Expr.size_disjoin_le (List.ofFn fun i => Expr.not (e i)) (N+1) (by
    rintro t ht
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp ht
    exact Nat.add_le_add_right (h i) 1)
  simp only [List.length_ofFn, show N+1+1 = N+2 by omega] at h₁
  change _ + 1 ≤ _
  omega

private def distinctFlags {X : Type*} (a c : X) : Expr X :=
  .or (.and (.input a) (.not (.input c))) (.and (.not (.input a)) (.input c))

private theorem distinct_eval {X : Type*} (a c : X) (x : X → Bool) :
    (distinctFlags a c).eval x = true ↔ x a ≠ x c := by
  cases ha : x a <;> cases hc : x c <;> simp [distinctFlags, Expr.eval, ha, hc]

private def outputExpr : Option (Labels d p m) → Expr (Bus d p m)
  | none => .and (.input (.inl (.inr ()))) (.and
      (allExpr (fun i => .input (.inr (.inr i))))
      (allExpr (fun i => distinctFlags (.inr (.inl (i,false))) (.inr (.inl (i,true))))))
  | some (.inl label) => .input (.inl (.inl label))
  | some (.inr i) => .input (.inr (.inl (i,true)))

private theorem outputExpr_size (t : Option (Labels d p m)) : (outputExpr t).size ≤ 30*(d+2) := by
  rcases t with _ | (label | i)
  · have h₁ := allExpr_size (fun i : Fin (d+1) => Expr.input (.inr (.inr i) : Bus d p m)) 1 (fun _ => le_rfl)
    have h₂ := allExpr_size (fun i : Fin d => distinctFlags (.inr (.inl (i,false)) : Bus d p m)
      (.inr (.inl (i,true)))) 9 (fun _ => le_rfl)
    simp only [outputExpr, Expr.size]
    omega
  · change 1 ≤ _
    omega
  · change 1 ≤ _
    omega

/-- Semantic and size guarantees for the complete Boolean verifier of a side. -/
structure CompleteFrame (f : Checkers w left b)
    (addr : CutBit d (2*leastEnergy m) (stateCountAt (d*leastEnergy m)) ↪ Fin p × Fin m) where
  /-- The sole shared Boolean frame, with acceptance at `none`. -/
  circuit : Frame (Raw f) (Option (Labels d p m))
  /-- Gate count before the standard weighted-CNF compilation. -/
  size_le : circuit.size ≤ (FusionFlags.frame addr).size +
    (1 + ∑ i, (stageFrame f i).size) + (1 + ∑ i, (stateFrame f i).size) +
    (1 + d + (d+p)*2^m)*(30*(d+2))
  /-- Acceptance excludes invalid state or mode encodings and all zero-valued paths. -/
  accepted : ∀ r, circuit.eval r none = true ↔ legal f r ∧
    ∀ i, (stageFrame f i).eval r false ≠ (stageFrame f i).eval r true
  /-- On canonical paths the variable flags report exactly their external word values. -/
  flag : ∀ (g : Data f) i z, circuit.eval (encode f g) (some (.inl (i,z))) =
    decide (Sum.elim g.1 (binaryBridge addr (g.2.1,maskIndex _ (g.2.2.1 (Fin.last d)))) i = z)
  /-- The negative local flags are individually available for the product of signs. -/
  negative : ∀ (g : Data f) i, circuit.eval (encode f g) (some (.inr i)) =
    stageFlags f g.1 g.2.1 g.2.2.1 g.2.2.2 i true

/-- A single finite circuit produces all the weighted flags, including the common
acceptance predicate, with additive cost for the shared stage programs. -/
theorem exists_fullFrame (f : Checkers w left b)
    (addr : CutBit d (2*leastEnergy m) (stateCountAt (d*leastEnergy m)) ↪ Fin p × Fin m) :
    Nonempty (CompleteFrame f addr) := by
  obtain ⟨st, stSize, stEval⟩ := exists_parallelFrames (stageFrame f)
  obtain ⟨vs, vsSize, vsEval⟩ := exists_parallelFrames (stateFrame f)
  let bus := parallelFrame (externalFrame f addr) (parallelFrame
    (st.select (fun k : Fin d × Bool => ⟨k.1,k.2⟩)) (vs.select (fun i => ⟨i,()⟩)))
  let F := bus.step (outputExpr (d := d) (p := p) (m := m))
  have hext r (j : FusionFlags.Output d p m) : bus.eval r (.inl j) =
      (FusionFlags.frame addr).eval ((Frame.initial (flagSource f)).eval r) j := by
    simp [bus, externalFrame]
  have hst r i sign : bus.eval r (.inr (.inl (i,sign))) = (stageFrame f i).eval r sign := by
    simp [bus, stEval]
  have hv r i : bus.eval r (.inr (.inr i)) = (stateFrame f i).eval r () := by
    simp only [bus, parallelFrame_eval_inr, Frame.select_eval, vsEval]
  have hmode r : (FusionFlags.frame addr).eval ((Frame.initial (flagSource f)).eval r) (.inr ()) = true ↔
      ∀ i, (readMode f r i).val < 2*leastEnergy m := by
    rw [FusionFlags.frame_modeValid]
    apply forall_congr'
    intro i
    have eq : (fun k => (Frame.initial (flagSource f)).eval r (.inr (.inl (i,k)))) =
        (fun k => r (.inr (.inl (i,k)))) := funext (fun _ => Frame.initial_eval _ _ _)
    rw [eq]
    rfl
  refine ⟨⟨F, ?_, ?_, ?_, ?_⟩⟩
  · have h := Frame.step_size_le bus outputExpr (30*(d+2)) outputExpr_size
    have hc : Fintype.card (Option (Labels d p m)) = 1+d+(d+p)*2^m := by simp [Labels]; omega
    simp only [bus, externalFrame, parallelFrame_size, Frame.select_size, Frame.subst_size,
      Frame.initial_size, zero_add, hc] at h
    apply h.trans
    omega
  · intro r
    simp only [F, Frame.step_eval, outputExpr, Expr.eval, Bool.and_eq_true, allExpr_eval, distinct_eval,
      hext, hst, hv, stateFrame_eval, hmode, legal]
    exact and_assoc.symm
  · intro g i z
    simp only [F, Frame.step_eval, outputExpr, Expr.eval, hext, external_encode, FusionFlags.frame_flag]
  · intro g i
    simp only [F, Frame.step_eval, outputExpr, Expr.eval, hst, stageFrame_encode]

end Crossing.FusionStage

end BorderVNP
end Computability
end OAI
