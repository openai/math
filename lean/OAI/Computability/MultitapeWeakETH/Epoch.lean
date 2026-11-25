import OAI.Computability.MultitapeWeakETH.Trace

/-! # Locality of a witness for an epoch

An epoch can be replayed on any tapes with the specified contents on its
participating blocks. The other absolute cells keep their original symbols.
-/

namespace OAI.Computability.MultitapeWeakETH

open IntegerMultiplication

variable {A Q I : Type}

structure AgreesOn (cells : I → Set ℤ) (a b : TM.Config A Q I) : Prop where
  state : a.pc = b.pc
  heads : ∀ i, (a.tape i).pos = (b.tape i).pos
  contents : ∀ i z, z ∈ cells i → (a.tape i).absolute z = (b.tape i).absolute z

theorem AgreesOn.same_reads {cells : I → Set ℤ} {a b : TM.Config A Q I}
    (matchAB : AgreesOn cells a b) (inside : ∀ i, (a.tape i).pos ∈ cells i) :
    (fun i => (a.tape i).view 0) = fun i => (b.tape i).view 0 := by
  funext i
  have eq := matchAB.contents i _ (inside i)
  simpa [TM.Tape.absolute, matchAB.heads i] using eq

theorem replay_step (rule : TM.Rule A Q I) {cells : I → Set ℤ} {a b a' : TM.Config A Q I}
    (matchAB : AgreesOn cells a b) (inside : ∀ i, (a.tape i).pos ∈ cells i)
    (step : TM.advance rule a = some a') :
    ∃ b', TM.advance rule b = some b' ∧ AgreesOn cells a' b' ∧
      ∀ i z, z ∉ cells i → (b'.tape i).absolute z = (b.tape i).absolute z := by
  obtain ⟨q,ops,h,ha⟩ : ∃ q ops, rule a.pc (fun i => (a.tape i).view 0) = some (q,ops) ∧
      a' = ⟨q,fun i => (a.tape i).apply (ops i)⟩ := by
    cases e : rule a.pc (fun i => (a.tape i).view 0) with
    | none => simp [TM.advance,e] at step
    | some qo =>
      obtain ⟨q,ops⟩ := qo
      exact ⟨q,ops,rfl,by simpa [TM.advance,e] using step.symm⟩
  have hb := h
  rw [matchAB.state,matchAB.same_reads inside] at hb
  subst a'
  refine ⟨⟨q,fun i => (b.tape i).apply (ops i)⟩,by simp [TM.advance,hb],⟨rfl,?_,?_⟩,?_⟩
  · intro i
    simp [TM.Tape.apply, matchAB.heads i]
  · intro i z hz
    simp only [TM.Tape.absolute_apply,matchAB.heads i,matchAB.contents i z hz]
  · intro i z hz
    have ne : z ≠ (b.tape i).pos := fun eq => hz (eq ▸ (matchAB.heads i ▸ inside i))
    simp [TM.Tape.absolute_apply,ne]

/-- Replay a finite sequence of local rules. On each chosen path the
nondeterministic choices are already fixed, so the same result applies. -/
theorem replay_epoch (rules : ℕ → TM.Rule A Q I) (cells : I → Set ℤ)
    (path : ℕ → TM.Config A Q I) (b : TM.Config A Q I)
    (initial : AgreesOn cells (path 0) b) (length : ℕ)
    (inside : ∀ t < length, ∀ i, ((path t).tape i).pos ∈ cells i)
    (step : ∀ t < length, TM.advance (rules t) (path t) = some (path (t+1))) :
    ∃ runs : ℕ → TM.Config A Q I, runs 0 = b ∧
      (∀ t < length, TM.advance (rules t) (runs t) = some (runs (t+1))) ∧
      AgreesOn cells (path length) (runs length) ∧
      ∀ i z, z ∉ cells i → ((runs length).tape i).absolute z = (b.tape i).absolute z := by
  induction length with
  | zero => exact ⟨fun _ => b,rfl,by simp,initial,by simp⟩
  | succ k ih =>
    obtain ⟨runs,start,steps,agrees,unchanged⟩ :=
      ih (fun t ht => inside t (by omega)) (fun t ht => step t (by omega))
    obtain ⟨next,hs,ha,hc⟩ := replay_step (rules k) agrees (inside k (by omega)) (step k (by omega))
    refine ⟨Function.update runs (k+1) next,by simpa using start,?_,by simpa using ha,?_⟩
    · intro t ht
      by_cases last : t = k
      · subst t
        simpa using hs
      · simpa [Function.update_of_ne (show t ≠ k+1 by omega),
          Function.update_of_ne (show t+1 ≠ k+1 by omega)] using steps t (by omega)
    · intro i z hz
      simpa using (hc i z hz).trans (unchanged i z hz)

end OAI.Computability.MultitapeWeakETH
