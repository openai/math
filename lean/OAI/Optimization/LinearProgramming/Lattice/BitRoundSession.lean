import OAI.Optimization.LinearProgramming.Lattice.BitRoundRuntimeCore
import OAI.Optimization.LinearProgramming.Lattice.BitRoundSemantic
import OAI.Optimization.LinearProgramming.Lattice.LLLWire

/-! Compose the complete bounded dialogue at an arbitrary incoming oracle transcript. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Lattice
namespace Bit
namespace Driver

open OracleSpec SignType ExactQuantumFactoring.BitStackProgram

/-- Stateless canonical two-bit representative of the supplied mathematical sign. -/
def signAnswer {p : ℕ} (s : (Fin p → ℤ) → SignType) : Word → Word :=
  wordSignOracle (fun a => orderOfSign (s a)) []

@[simp] theorem signAnswer_query {p : ℕ} (s : (Fin p → ℤ) → SignType) (a : Fin p → ℤ) :
    signAnswer s (signRowWord a) = signReply (orderOfSign (s a)) := wordSignOracle_query _ _ _

private theorem signAnswer_packed {p : ℕ} (s : (Fin p → ℤ) → SignType) (a : Fin p → ℤ) :
    rowOracle (signAnswer s) (List.ofFn a) = decide (0 ≤ s a) := by
  simp only [rowOracle,signPacket_pack,signAnswer,wordSignOracle_query,nonnegativeAnswer_sign]
  cases s a <;> rfl

private theorem signAnswer_length {p : ℕ} (s : (Fin p → ℤ) → SignType) (w : Word) :
    (signAnswer s w).length ≤ 2 := by
  unfold signAnswer wordSignOracle
  cases hh : readSignRow p w with
  | none => simp
  | some x =>
    obtain ⟨a,tail⟩ := x
    cases tail <;> simp

/-- A possibly history-dependent physical oracle need only agree on rows actually
requested by the typed computation. -/
theorem rounding_session_with {f : Kernels} (sem : RoundKernelSemantics f) {p M : ℕ} (hp : 0<p) (hM : 0<M) (v : Fin p→ℝ)
    (s : (Fin p→ℤ)→SignType) (hs : ∀ a, s a = sign (dotProduct (realCoordinates a) v))
    (o : WordOracle) (wire : ∀ h a, a ∈ SignQueries.history (fun r => decide (0 ≤ s r))
      (lllRoundingProgram p M) → o h (signRowWord a) = signReply (orderOfSign (s a)))
    (past : Transcript) :
    let test := fun a => decide (0 ≤ s a)
    let t := lllRoundingProgram p M
    let qs := wordQueries test t
    ∃ count ≤ p*(2*p+1+p*searchPrecision p M),
      WordDialogue.Session inputCode carryCode (dispatch f) o
        (frameBound.eval (p+M.size+12)) (.inl (p,M)) past (signRowWord (SignQueries.run test t))
        ((qs.map (fun q => (q,signAnswer s q))).reverse ++ past) (count+1) := by
  intro test t qs
  let reply := signAnswer s
  let N := RoundWidth.parameter p M
  let L := frameBound.eval N
  have ho a : test a = true ↔ 0 ≤ formValue a v := by
    simp only [test,decide_eq_true_eq,hs,sign_nonneg_iff]
    rfl
  obtain ⟨steps,run,history,reached,hcount⟩ :=
    rounding_dialogue_with sem hp hM v test ho reply (signAnswer_packed s)
  change steps.map Prod.fst = qs at history
  have agree h e (he : e ∈ steps) : o h e.1 = reply e.1 := by
    have hmem : e.1 ∈ qs := history ▸ List.mem_map.mpr ⟨e,he,rfl⟩
    change e.1 ∈ (SignQueries.history test t).reverse.map signRowWord at hmem
    obtain ⟨a,hm,ha⟩ := List.mem_map.mp hmem
    rw [← ha,wire h a (List.mem_reverse.mp hm)]
    change signReply (orderOfSign (s a)) = signAnswer s (signRowWord a)
    exact (signAnswer_query s a).symm
  have hfit e (he : e ∈ steps) : requestFits L reply e :=
    reached_fits_with sem (reached e he) reply (signAnswer_length s)
  have hcorrect := lllRoundingProgram_correct hp hM v s hs
  have outOK : (signRowWord (SignQueries.run test t)).length ≤ L := output_frame hcorrect.2.2.1
  have session := dialogueSession f o reply run agree L outOK hfit (.inl (p,M))
    rfl (opening_frame p M) past
  have historyEq : wireHistory reply steps = (qs.map (fun q => (q,reply q))).reverse := calc
    _ = ((steps.map Prod.fst).map (fun q => (q,reply q))).reverse := by
      simp [wireHistory,Function.comp_def]
    _ = _ := by rw [history]
  exact ⟨steps.length,hcount,historyEq ▸ session⟩

/-- The uniform polynomially bounded driver can be entered at any oracle transcript. -/
theorem rounding_session_on_history {p M : ℕ} (hp : 0<p) (hM : 0<M) (v : Fin p→ℝ)
    (s : (Fin p→ℤ)→SignType) (hs : ∀ a, s a = sign (dotProduct (realCoordinates a) v))
    (o : WordOracle) (wire : ∀ h a, a ∈ SignQueries.history (fun r => decide (0 ≤ s r))
      (lllRoundingProgram p M) → o h (signRowWord a) = signReply (orderOfSign (s a)))
    (past : Transcript) :
    let test := fun a => decide (0 ≤ s a)
    let t := lllRoundingProgram p M
    let qs := wordQueries test t
    ∃ count ≤ p*(2*p+1+p*searchPrecision p M),
      WordDialogue.Session inputCode carryCode (dispatch actualKernels) o
        (frameBound.eval (p+M.size+12)) (.inl (p,M)) past (signRowWord (SignQueries.run test t))
        ((qs.map (fun q => (q,signAnswer s q))).reverse ++ past) (count+1) :=
  rounding_session_with actual_round_kernel_semantics hp hM v s hs o wire past

end Driver
end Bit
end Lattice
end LinearProgramming
end Optimization
end OAI
