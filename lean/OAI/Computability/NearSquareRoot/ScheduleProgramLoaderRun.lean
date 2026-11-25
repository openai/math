import OAI.Computability.NearSquareRoot.ScheduleProgramLoader
import OAI.Computability.NearSquareRoot.ScheduleProgramLoadSpace

/-! # Distinct cells across table installation and interpretation -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace TapeSequence

open IntegerMultiplication

/-- Handoff leaves all head positions fixed. The union of two per-machine
physical cell covers contains every position in the composite run. -/
theorem visitsAtMost {A Q R I : Type} (m : TM.Rule A Q I) (n : TM.Rule A R I) (entry : R)
    {a b : TM.Config A Q I} {z : TM.Config A R I} {s t S T : ℕ}
    (first : Trace (TM.advance m) a s b) (halt : TM.advance m b = none)
    (second : Trace (TM.advance n) ⟨entry,b.tape⟩ t z)
    (firstSpace : VisitsAtMost m a s S) (secondSpace : VisitsAtMost n ⟨entry,b.tape⟩ t T) :
    VisitsAtMost (rule m n entry) (relabel Sum.inl a) (s+1+t) (S+T) := by
  classical
  obtain ⟨set₁,h₁,f₁⟩ := firstSpace
  obtain ⟨set₂,h₂,f₂⟩ := secondSpace
  refine ⟨set₁ ∪ set₂, le_trans (Finset.card_union_le _ _) (Nat.add_le_add h₁ h₂), ?_⟩
  intro u hu c hc i
  by_cases small : u ≤ s
  · obtain ⟨x,hx,_⟩ := trace_split first small
    have eq := trace_endpoint_unique hc (first_trace m n entry hx)
    rw [eq]
    exact Finset.mem_union_left _ (f₁ u small x hx i)
  · have past : s+1 ≤ u := by omega
    let v := u-(s+1)
    have hv : v ≤ t := by dsimp [v]; omega
    obtain ⟨y,hy,_⟩ := trace_split second hv
    have swap := (first_trace m n entry first).trans (Trace.single (handoff m n entry halt))
    have ht := swap.trans (second_trace m n entry hy)
    rw [show s+1+v = u by dsimp [v]; omega] at ht
    rw [trace_endpoint_unique hc ht]
    exact Finset.mem_union_right _ (f₂ v hv y hy i)

end TapeSequence

namespace Universal.Loader

open IntegerMultiplication TM

theorem load_space {A I : Type} [Fintype I] {m : ℕ} (blank : A)
    (machine : Rule A (Fin m) I) (rs : List (I → A)) (d : I → Tape A) :
    let code := program machine rs
    VisitsAtMost rule (initial blank code d) (2 * code.length + 2)
      (Fintype.card I + 2 * (code.length + 1)) := by
  have h := (load_program blank machine rs d).visitsAtMost
  simpa [Fintype.sum_sum_type, bound, two_mul, Nat.add_comm, Nat.add_left_comm,
    Nat.add_assoc] using h

/-- A space certificate for the single-table input needs only one cell per data tape
and the two finite table intervals in addition to the interpreter's own cover. -/
theorem install_space {A I : Type} [Fintype I] [Finite A] {m : ℕ} (blank : A)
    (machine : Rule A (Fin m) I) (rs : List (I → A)) (d : I → Tape A)
    {z : Config (Letter A I) PC (Index I)} {t S : ℕ}
    (run : Trace (advance (Universal.rule blank))
      (loadedConf blank (program machine rs) d false .seek 1 0) t z)
    (space : VisitsAtMost (Universal.rule blank)
      (loadedConf blank (program machine rs) d false .seek 1 0) t S) :
    let code := program machine rs
    VisitsAtMost (installAndRun blank) (TapeSequence.relabel Sum.inl (initial blank code d))
      (2*code.length+3+t) (Fintype.card I + 2*(code.length+1) + S) := by
  have first := (load_program blank machine rs d).1
  have e : (⟨(false,.seek),(ready blank (program machine rs) d).tape⟩ :
      Config (Letter A I) PC (Index I)) = loadedConf blank (program machine rs) d false .seek 1 0 := by
    rw [ready_tapes]
    rfl
  rw [←e] at run space
  exact TapeSequence.visitsAtMost rule (Universal.rule blank) _ first (by rfl) run
    (load_space blank machine rs d) space


/-- Compiling one generated candidate table into the common interpreter preserves
a fixed candidate's time and space orders. All overhead constants are explicit
functions of the length of its finite transition table and the common tape count. -/
theorem install_halting_space_sharp {A I : Type} [Fintype I] [Finite A] {m : ℕ} (hm : 0 < m)
    (blank : A) (machine : Rule A (Fin m) I) (rs : List (I → A)) (complete : ∀ r, r ∈ rs)
    (d : I → Tape A) {z : Config A (Fin m) I} {t S : ℕ}
    (run : Trace (advance machine) ⟨⟨0,hm⟩,d⟩ t z) (halt : advance machine z = none)
    (candidateSpace : VisitsAtMost machine ⟨⟨0,hm⟩,d⟩ t S) :
    let code := program machine rs
    let K := 4*(code.length+1)
    let start := TapeSequence.relabel Sum.inl (initial blank code d)
    ∃ n finish, n ≤ 2*code.length+3 + K*(t+1) ∧
      Trace (advance (installAndRun blank)) start n finish ∧
      advance (installAndRun blank) finish = none ∧
      (∀ i, finish.tape (.inl i) = dataCell (z.tape i)) ∧
      VisitsAtMost (installAndRun blank) start n
        (Fintype.card I + 2*(code.length+1) + (S + 2*(code.length+2*K+1))) := by
  let code := program machine rs
  obtain ⟨v,w,hv,hw,hh,hd,hs⟩ := interpret_loaded_halting_space_sharp blank machine rs complete false
    run halt candidateSpace
  have start : loadedConf blank (program machine rs) d false .seek
      (rowAddress machine rs ⟨0,hm⟩) 0 = loadedConf blank code d false .seek 1 0 := by
    simp [code]
  change Trace (advance (Universal.rule blank))
    (loadedConf blank _ d false .seek (rowAddress machine rs ⟨0,hm⟩) 0) v w at hw
  change VisitsAtMost (Universal.rule blank)
    (loadedConf blank _ d false .seek (rowAddress machine rs ⟨0,hm⟩) 0) v _ at hs
  rw [start] at hw hs
  have cover := install_space blank machine rs d hw hs
  have e : (⟨(false,.seek),(ready blank code d).tape⟩ :
      Config (Letter A I) PC (Index I)) = loadedConf blank code d false .seek 1 0 := by
    rw [ready_tapes]
    rfl
  rw [← e] at hw
  obtain ⟨completeRun,halted⟩ := TapeSequence.run rule (Universal.rule blank) (false,.seek)
    (load_program blank machine rs d).1 (by rfl) hw hh
  exact ⟨_,_,Nat.add_le_add_left hv _,completeRun,halted,hd,cover⟩

theorem install_halting_space {A I : Type} [Fintype I] [Finite A] {m : ℕ} (hm : 0 < m)
    (blank : A) (machine : Rule A (Fin m) I) (rs : List (I → A)) (complete : ∀ r, r ∈ rs)
    (d : I → Tape A) {z : Config A (Fin m) I} {t S : ℕ}
    (run : Trace (advance machine) ⟨⟨0,hm⟩,d⟩ t z) (halt : advance machine z = none)
    (candidateSpace : VisitsAtMost machine ⟨⟨0,hm⟩,d⟩ t S) :
    let code := program machine rs
    let K := 4*(code.length+1)
    let start := TapeSequence.relabel Sum.inl (initial blank code d)
    ∃ n finish, n ≤ 2*code.length+3 + K*(t+1) ∧
      Trace (advance (installAndRun blank)) start n finish ∧
      advance (installAndRun blank) finish = none ∧
      (∀ i, finish.tape (.inl i) = dataCell (z.tape i)) ∧
      VisitsAtMost (installAndRun blank) start n
        (Fintype.card I + 2*(code.length+1) + (S*(2*K+1) + 2*(code.length+2*K+1))) := by
  obtain ⟨u,f,hu,run',stop,data,V,hV,cover⟩ :=
    install_halting_space_sharp hm blank machine rs complete d run halt candidateSpace
  refine ⟨u,f,hu,run',stop,data,V,hV.trans (Nat.add_le_add_left (Nat.add_le_add_right ?_ _) _),cover⟩
  exact Nat.le_mul_of_pos_right S (by omega)

end Universal.Loader

end NearSquareRoot
end Computability
end OAI
