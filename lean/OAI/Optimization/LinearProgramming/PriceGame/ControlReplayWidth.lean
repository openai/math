import OAI.Optimization.LinearProgramming.PriceGame.ControlReplayMachine

/-! Every intermediate public control state lies on the chosen chronological execution.
This includes short tapes and the fixed states reached after an ordinary halt. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Native
namespace Replay

open ExactQuantumFactoring.BitStackProgram Procedure

/-- An invariant of the live states and final bit along a complete run holds for
every replay tick, including all ticks spent at the terminal. -/
theorem duringComplete {P : Driver.PC → Prop} {o e tr ticks} (run : Driver.GuardedSteps P o tr ticks e)
    {micro : ℕ × Driver.PC → Driver.Action} {n M : ℕ} (W : State → Prop)
    (agree : ∀ s, P s → micro (n,s) = Driver.step s)
    (hlive : ∀ s bs, P s → bs.length ≤ M → W (live n bs s))
    (hdone : ∀ b, W (done b)) (bit : Bool) :
    P e → micro (n,e) = .halt bit → ∀ tail : List Bool, (tr.map Prod.snd ++ tail).length ≤ M →
      ∀ j, W ((advance micro)^[j] (live n (tr.map Prod.snd ++ tail) o)) := by
  induction run with
  | refl s =>
    intro he stop tail hb j
    simp only [List.map_nil,List.nil_append] at hb ⊢
    cases j with
    | zero => exact hlive s tail he hb
    | succ j =>
      rw [Function.iterate_succ_apply]
      change W ((advance micro)^[j] (respond (n,tail) (micro (n,s))))
      rw [stop]
      change W ((advance micro)^[j] (Sum.inr (Sum.inl bit)))
      rw [stopped_fixed]
      exact hdone bit
  | silent hs edge rest ih =>
    intro he stop tail hb j
    cases j with
    | zero => exact hlive _ _ hs hb
    | succ j =>
      rw [Function.iterate_succ_apply]
      simp only [live,advance,agree _ hs,edge,respond]
      exact ih he stop tail hb j
  | answer b hs edge rest ih =>
    intro he stop tail hb j
    cases j with
    | zero => exact hlive _ _ hs hb
    | succ j =>
      rw [Function.iterate_succ_apply]
      simp only [List.map_cons,List.cons_append,live,advance,agree _ hs,edge,respond]
      apply ih he stop tail _ j
      simp only [List.map_cons,List.cons_append,List.length_cons] at hb
      omega

/-- An invariant of the traversed states and unanswered requests holds on a short
tape regardless of how much extra clock time is available after suspension. -/
theorem duringShort {P : Driver.PC → Prop} {o e tr ticks} (run : Driver.GuardedSteps P o tr ticks e)
    {micro : ℕ × Driver.PC → Driver.Action} {n M : ℕ} (W : State → Prop)
    (agree : ∀ s, P s → micro (n,s) = Driver.step s)
    (hlive : ∀ s bs, P s → bs.length ≤ M → W (live n bs s))
    (hask : ∀ s q f t, P s → Driver.step s = .ask q f t → W (pending q)) :
    ∀ k (_hk : k < tr.length), ((tr.take k).map Prod.snd).length ≤ M →
      ∀ j, W ((advance micro)^[j] (live n ((tr.take k).map Prod.snd) o)) := by
  induction run with
  | refl => simp
  | silent hs edge rest ih =>
    intro k hk hb j
    cases j with
    | zero => exact hlive _ _ hs hb
    | succ j =>
      rw [Function.iterate_succ_apply]
      simp only [live,advance,agree _ hs,edge,respond]
      exact ih k hk hb j
  | answer b hs edge rest ih =>
    intro k hk hb j
    cases j with
    | zero => exact hlive _ _ hs hb
    | succ j =>
      rw [Function.iterate_succ_apply]
      cases k with
      | zero =>
        simp only [List.take_zero,List.map_nil,live,advance,agree _ hs,edge,respond]
        rw [show pending _ = Sum.inr (Sum.inr _) from rfl,stopped_fixed]
        exact hask _ _ _ _ hs edge
      | succ k =>
        simp only [List.take_succ_cons,List.map_cons,live,advance,agree _ hs,edge,respond]
        apply ih k (by simpa using hk) _ j
        simp only [List.take_succ_cons,List.map_cons,List.length_cons] at hb
        omega

private noncomputable def microInput (pc : Polynomial ℕ) : Polynomial ℕ := 2*Polynomial.X + 1 + pc

/-- A bound on raw PCs lifts to one on all replay states, including stored root
requests. The latter are bounded by the instructions that physically emitted them. -/
noncomputable def functionWidth (pc stepTime : Polynomial ℕ) : Polynomial ℕ :=
  4*Polynomial.X + pc + 5 + microInput pc + stepTime.comp (microInput pc)

private theorem input_le (N M : ℕ) (pc : Driver.PC) (cap : Polynomial ℕ)
    (hN : N ≤ M) (hs : (Wire.combinedCode pc).length ≤ cap.eval M) :
    (prodCode unaryCode Wire.combinedCode (N,pc)).length ≤ (microInput cap).eval M := by
  simp only [microInput,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat,
    Polynomial.eval_one,prodCode,pairBits_length,unaryCode,List.length_replicate]
  omega

theorem live_width {N M : ℕ} {s : Driver.PC} {bs : List Bool} {pc work : Polynomial ℕ}
    (hN : N ≤ M) (hb : bs.length ≤ M) (hs : (Wire.combinedCode s).length ≤ pc.eval M) :
    (stateCode (live N bs s)).length ≤ (functionWidth pc work).eval M := by
  simp only [stateCode,live,sumCode,runningCode,prodCode,pairBits_length,unaryCode,id_eq,
    List.length_replicate,List.length_cons,functionWidth,Polynomial.eval_add,Polynomial.eval_mul,
    Polynomial.eval_X,Polynomial.eval_ofNat]
  omega

theorem done_width (M : ℕ) (pc work : Polynomial ℕ) (b : Bool) :
    (stateCode (done b)).length ≤ (functionWidth pc work).eval M := by
  change 3 ≤ _
  simp only [functionWidth,Polynomial.eval_add,Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat]
  omega

theorem query_width {N M : ℕ} {s f t : Driver.PC} {q : PackedQuery} {pc : Polynomial ℕ}
    {micro : ℕ × Driver.PC → Driver.Action}
    (stepP : Procedure (prodCode unaryCode Wire.combinedCode) Join.actionCode micro)
    (hN : N ≤ M) (hs : (Wire.combinedCode s).length ≤ pc.eval M)
    (edge : micro (N,s) = .ask q f t) :
    (stateCode (pending q)).length ≤ (functionWidth pc stepP.bound).eval M := by
  have hi := input_le N M s pc hN hs
  have ho := stepP.output_length_le (N,s)
  rw [edge] at ho
  have ha : (Wire.packedQueryCode q).length ≤ (Join.actionCode (.ask q f t)).length := by
    simp only [Join.actionCode,Join.outerReplyCode,prodCode,pairBits_length,List.length_cons]
    omega
  have ht := Nat.add_le_add hi (Procedure.eval_nat_mono stepP.bound hi)
  have ux : (Wire.packedQueryCode q).length ≤ (microInput pc).eval M +
      stepP.bound.eval ((microInput pc).eval M) := ha.trans (ho.trans ht)
  simp only [stateCode,pending,stoppedCode,sumCode,List.length_cons,functionWidth,Polynomial.eval_add,
    Polynomial.eval_mul,Polynomial.eval_X,Polynomial.eval_ofNat, Polynomial.eval_comp]
  omega

/-- Width during any prefix of a complete chronological run. -/
theorem width_on_complete {P : Driver.PC → Prop} {o e tr ticks} (run : Driver.GuardedSteps P o tr ticks e)
    {micro : ℕ × Driver.PC → Driver.Action} {n : ℕ} {pc : Polynomial ℕ}
    (stepP : Procedure (prodCode unaryCode Wire.combinedCode) Join.actionCode micro)
    (M : ℕ) (hN : n ≤ M) (agree : ∀ s, P s → micro (n,s) = Driver.step s)
    (bound : ∀ s, P s → (Wire.combinedCode s).length ≤ pc.eval M) (b : Bool)
    (he : P e) (stop : micro (n,e) = .halt b) (tail : List Bool)
    (len : (tr.map Prod.snd ++ tail).length ≤ M) (j : ℕ) :
    (stateCode ((advance micro)^[j] (live n (tr.map Prod.snd ++ tail) o))).length ≤
      (functionWidth pc stepP.bound).eval M :=
  duringComplete run (fun z => (stateCode z).length ≤ (functionWidth pc stepP.bound).eval M) agree (fun s _ ps hb => live_width hN hb (bound s ps))
    (done_width M pc stepP.bound) b he stop tail len j

/-- Width up to and beyond the first unanswered request of a short tape. -/
theorem width_on_short {P : Driver.PC → Prop} {o e tr ticks} (run : Driver.GuardedSteps P o tr ticks e)
    {micro : ℕ × Driver.PC → Driver.Action} {n : ℕ} {pc : Polynomial ℕ}
    (stepP : Procedure (prodCode unaryCode Wire.combinedCode) Join.actionCode micro)
    (M : ℕ) (hN : n ≤ M) (agree : ∀ s, P s → micro (n,s) = Driver.step s)
    (bound : ∀ s, P s → (Wire.combinedCode s).length ≤ pc.eval M)
    (k : ℕ) (hk : k < tr.length) (len : ((tr.take k).map Prod.snd).length ≤ M) (j : ℕ) :
    (stateCode ((advance micro)^[j] (live n ((tr.take k).map Prod.snd) o))).length ≤
      (functionWidth pc stepP.bound).eval M :=
  duringShort run (fun z => (stateCode z).length ≤ (functionWidth pc stepP.bound).eval M) agree (fun s _ ps hb => live_width hN hb (bound s ps))
    (fun s _ _ _ hs edge => query_width stepP hN (bound s hs) ((agree s hs).trans edge))
    k hk len j

end Replay
end Native
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
