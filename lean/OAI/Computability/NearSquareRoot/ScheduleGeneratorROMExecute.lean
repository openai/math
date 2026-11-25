import OAI.Computability.NearSquareRoot.ScheduleGeneratorROMPipeline
import OAI.Computability.NearSquareRoot.CommonAlphabetROMCells

/-! # Uniform generation and interpretation of finite transition tables -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorPipeline
open IntegerMultiplication TM Turing Turing.ToPartrec Turing.PartrecToTM2 Universal
variable {A Q I : Type} {M N : ℕ}

private instance : Fintype K' :=
  ⟨{.main,.rev,.aux,.stack},by intro k; cases k <;> simp⟩

theorem finite_indices [Finite I] : Finite (Index I) := inferInstance

theorem finite_control (c : Code) (m : ℕ) : Finite (Control c m) := by
  have := Generator.finite_physical_control c
  infer_instance

private theorem elapsed_space {B R J : Type} [Fintype J] (r : Rule B R J)
    (x : Config B R J) (g : ℕ) : VisitsAtMost r x g (Fintype.card J * (2*g+1)) := by
  have slow := visitsAtMost_of_tape_fences (m := r) (init := x) (steps := g)
    (fun i => (x.tape i).pos-g) (fun i => (x.tape i).pos+g)
    (by intro u h z run i; have e := head_excursion run i; omega)
  have hw (i : J) : ((x.tape i).pos + g + 1 - ((x.tape i).pos-g)).toNat = 2*g+1 := by omega
  simpa [hw] using slow

/-- One fixed finite rule generates a ROM on its input index, installs it and
runs the candidate. For this particular index the time and space overhead
constants are independent of the candidate input, runtime and visited cells. -/
theorem run_numbered_sharp [Finite A] [Fintype I] (blank : A) (c : Code) (enum : Tag A I ≃ Fin (M+1))
    (w : List ℕ) (states : Q ≃ Fin N) (entry : Q) (candidate : Rule A Q I)
    (reads : List (I → A)) (complete : ∀ r, r ∈ reads)
    (hcode : symbolWord enum (Reindex.encode states entry candidate reads) ∈ c.eval w) :
    ∃ E : ℕ, 0 < E ∧ ∀ (d : I → Tape A) {z : Config A Q I} {t S : ℕ},
      Trace (advance candidate) ⟨entry,d⟩ t z → advance candidate z = none →
      VisitsAtMost candidate ⟨entry,d⟩ t S →
      ∃ n finish, n ≤ E*(t+1) ∧
        Trace (advance (rule blank c enum)) (initial blank c w d) n finish ∧
        advance (rule blank c enum) finish = none ∧
        (∀ i, finish.tape (.inr (.inl i)) = dataCell (z.tape i)) ∧
        VisitsAtMost (rule blank c enum) (initial blank c w d) n (S+E) := by
  classical
  let v := Reindex.encode states entry candidate reads
  let K := 4*(v.length+1)
  obtain ⟨g,prefixRun⟩ := prepare_run blank c enum w v hcode
  let J := Fintype.card (Index I)
  let pre := J*(2*g+1)
  let U := g+1+2*v.length+3
  let V := pre + Fintype.card I + 2*(v.length+1) + 2*(v.length+2*K+1) + J
  let E := U + K + V + 1
  refine ⟨E,by dsimp [E]; omega,?_⟩
  intro d z t S candidateRun candidateHalt candidateSpace
  obtain ⟨a,ra,ha,layout⟩ := prefixRun d
  obtain ⟨s,b,ht,hb,endB,dataB,spaceB⟩ := Reindex.install_numbered_sharp states entry blank
    candidate reads complete d candidateRun candidateHalt candidateSpace
  let first := prepare blank c enum
  let firstStart : Config _ (GenControl c ⊕ GeneratorROM.Control M) _ :=
    ⟨.inl (Generator.initial c []).pc,inputTapes blank w d⟩
  let boot : Config (Letter A I) (Loader.Control ⊕ PC) (Universal.Index I) := TapeSequence.relabel Sum.inl (Loader.initial blank v d)
  let onBank := CommonTapes.config loaderIndex a.tape (Q := Loader.Control ⊕ PC)
  have layout' : onBank boot = ⟨.inl .copy,a.tape⟩ := by
    apply congrArg (Config.mk _)
    funext j
    cases j with
    | inl k =>
      exact CommonTapes.extend_off _ _ _ _ (by rintro ⟨j,h⟩; contradiction)
    | inr j =>
      change CommonTapes.extend loaderIndex _ _ (loaderIndex j) = _
      rw [CommonTapes.extend_apply]
      exact (layout j).symm
  have second : Trace (advance (execute blank)) (onBank boot) s (onBank b) :=
    CommonTapes.trace _ _ _ hb
  have halted : advance (execute blank) (onBank b) = none := by
    unfold execute
    rw [CommonTapes.advance_config,endB]; rfl
  have cover := CommonTapes.visits loaderIndex (Loader.installAndRun blank) a.tape boot s _ spaceB
  rw [layout'] at second
  change VisitsAtMost (execute blank) (onBank boot) s _ at cover
  rw [layout'] at cover
  obtain ⟨allSteps,done⟩ := TapeSequence.run _ _ _ ra ha second halted
  have allSpace := TapeSequence.visitsAtMost _ _ _ ra ha second (elapsed_space first firstStart g) cover
  refine ⟨_,_,?_,allSteps,done,?_,?_⟩
  · calc
      g+1+s ≤ U + K*(t+1) := by dsimp [U,K,v]; omega
      _ ≤ (U+K)*(t+1) := by nlinarith
      _ ≤ E*(t+1) := Nat.mul_le_mul_right _ (by dsimp [E]; omega)
  · intro i
    change CommonTapes.extend loaderIndex _ _ (loaderIndex (.inl i)) = _
    rw [CommonTapes.extend_apply]
    exact dataB i
  · obtain ⟨cells,count,contains⟩ := allSpace
    refine ⟨cells,count.trans ?_,contains⟩
    change pre + (Fintype.card I + 2*(v.length+1) +
        (S + 2*(v.length+2*K+1)) + J) ≤ S+E
    dsimp [E,V]
    omega

theorem run_numbered [Finite A] [Fintype I] (blank : A) (c : Code) (enum : Tag A I ≃ Fin (M+1))
    (w : List ℕ) (states : Q ≃ Fin N) (entry : Q) (candidate : Rule A Q I)
    (reads : List (I → A)) (complete : ∀ r, r ∈ reads)
    (hcode : symbolWord enum (Reindex.encode states entry candidate reads) ∈ c.eval w) :
    ∃ E : ℕ, 0 < E ∧ ∀ (d : I → Tape A) {z : Config A Q I} {t S : ℕ},
      Trace (advance candidate) ⟨entry,d⟩ t z → advance candidate z = none →
      VisitsAtMost candidate ⟨entry,d⟩ t S →
      ∃ n finish, n ≤ E*(t+1) ∧
        Trace (advance (rule blank c enum)) (initial blank c w d) n finish ∧
        advance (rule blank c enum) finish = none ∧
        (∀ i, finish.tape (.inr (.inl i)) = dataCell (z.tape i)) ∧
        VisitsAtMost (rule blank c enum) (initial blank c w d) n (E*(S+1)) := by
  obtain ⟨E,hE,run⟩ := run_numbered_sharp blank c enum w states entry candidate reads complete hcode
  refine ⟨E,hE,fun d _ _ S tr halt space => ?_⟩
  obtain ⟨n,f,ht,hr,hh,data,V,hV,cover⟩ := run d tr halt space
  refine ⟨n,f,ht,hr,hh,data,V,hV.trans ?_,cover⟩
  rw [Nat.mul_add_one]
  exact Nat.add_le_add_right (Nat.le_mul_of_pos_left S hE) E

end GeneratorPipeline

end NearSquareRoot
end Computability
end OAI
