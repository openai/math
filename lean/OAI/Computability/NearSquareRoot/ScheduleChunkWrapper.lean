import OAI.Computability.NearSquareRoot.ScheduleChunkPhysical
import OAI.Computability.NearSquareRoot.ScheduleChunkVisited
import OAI.Computability.NearSquareRoot.ScheduleChunkCalleeSpace
import OAI.Computability.NearSquareRoot.ScheduleChunkTapeCount

/-!
# Composition of guarded chunked multiplication

One choice of controller programs works for every split, every input, and
every candidate digit multiplier. The premise on a candidate measures
distinct physical tape cells during its compiled run. The conclusion bounds
every prefix of the accumulating controller, its return stack and output
copy included. A fixed dyadic split absorbs each candidate's linear constant.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace ChunkControl

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Bits
open ChunkLoop ChunkTask ChunkDispatch ChunkPhases
open Schoolbook (raw)

/-- Time is measured in register-program transitions; space is measured by
the distinct physical cells visited in the first two tape ticks per transition. -/
noncomputable def Isolated (c : Cmd) (m : Operands → Word) (T S : ℕ → ℕ) : Prop :=
  let U := Prog.sites [] c
  let g := SM.complete (ChunkVisited.inputReg U) (Prog.compile U)
  ∀ a : EqualWords, ∃ t ≤ T a.val.1.length,
    Prog.Run [] c (raw (send a.val).spell) t (raw (send (m a.val)).spell) ∧
    VisitsAtMost g (ChunkGuard.origin (ChunkVisited.start U c (fun _ h => h))
      (ChunkVisited.inputReg U) ((send a.val).spell.map Sum.inl)) (2*t) (S a.val.1.length)

theorem digit_of_isolated (d : Driver) (c : Cmd) (m : Operands → Word) (T S : ℕ → ℕ)
    (callee : Isolated c m T S) (p : Input) (cap i : ℕ) (hi : i < p.count)
    (fit : S p.u ≤ p.n) :
    digitBlock d c m p i (T p.u) ((cap+34)*(p.n+1)) := by
  let cmd := program d c
  have width := p.query_width m i
  let q := digitQuery m p i
  let a : EqualWords := ⟨q, width.1.trans width.2.symm,width.1.symm ▸ p.width_pos⟩
  have aq : a.val.1.length = p.u := width.1
  obtain ⟨t,ht,source,space⟩ := callee a
  rw [aq] at ht space
  let U := Prog.sites [] c
  have orig := ChunkVisited.compiled_segment U (c:=c) (fun _ h => h) source le_rfl space
  have moved := ChunkCalleeSpace.succ_segment c (send q).spell (send (m q)).spell
    (record m p i) source orig (area cmd) (good cmd .digit)
  obtain ⟨run,height⟩ := moved
  have h := lift_run cmd (route cmd) .digit run
  have hlim : max ((send q).spell.length + S p.u) (record m p i).length ≤ (cap+34)*(p.n+1) := by
    have h₁ := ChunkPhases.query_length m p i
    have h₂ := record_length m p i hi.le
    change (send q).spell.length ≤ _ at h₁
    rw [Nat.add_mul]
    omega
  refine ⟨t, ht, h, ?_⟩
  intro k z hk hz j
  obtain ⟨base,pre,rfl⟩ := (prefix_iff cmd (route cmd) .digit run hk z).1 hz
  exact (height hk pre j).trans hlim

/-- The whole product on the fresh physical output tape, including leading zeros. -/
noncomputable def Completed (d : Driver) (C : ℕ) (c : Cmd) (m : Operands → Word)
    (T : ℕ → ℕ) (p : Input) : Prop :=
  ∃ t ≤ (6*C+16)*((p.count+1)*(p.n+T p.u+1)), ∃ z,
    Trace (TM.advance (guarded d c)) (initial d c (radius C p.n) (input p)) t z ∧
    TM.advance (guarded d c) z = none ∧ z.pc.1 = false ∧
    TM.whole none (((send (answer m p)).spell.map Sum.inl).map some) (ChunkGuard.data (z.tape none)) ∧
    (answer m p).length = 2*p.n ∧ bitValue (answer m p) = bitValue p.x * bitValue p.y

/-- One fixed controller caps all trials sharing a bounded callee tape
count. Its output guarantee uses only a standalone call on the digit width,
including that call's own physical visited-cell bound. -/
theorem wrapper :
    ∃ (d : Driver) (C : ℕ),
      (∀ K : ℕ, ∃ W : ℕ, ∀ c : Cmd, Nat.card (Prog.Ix (Prog.sites [] c)) ≤ K →
        ∀ (n budget : ℕ) (s : List Ltr),
          VisitsAtMost (guarded d c) (initial d c (radius C n) s) budget (W*(n+1))) ∧
      ∀ (c : Cmd) (m : Operands → Word) (T S : ℕ → ℕ), Isolated c m T S →
        (∀ q : EqualWords, (m q.val).length = 2*q.val.1.length) →
        (∀ q : EqualWords, bitValue (m q.val) = bitValue q.val.1 * bitValue q.val.2) →
        ∀ p : Input, S p.u ≤ p.n → Completed d C c m T p := by
  obtain ⟨load,test,prep,collect,emit,C,ctl⟩ := controllers
  let d : Driver := ⟨load,test,prep,collect,emit⟩
  refine ⟨d,C,?_,?_⟩
  · intro K
    obtain ⟨w,hw⟩ := output_tape_count_overhead d
    refine ⟨(w+K)*(4*(C+34)+5), fun c hc n steps s => ?_⟩
    obtain ⟨cells,hcells,cover⟩ := guarded_space d c C n steps s
    refine ⟨cells,hcells.trans ?_,cover⟩
    have bound : tapeCount d c ≤ w+K := by
      have h := hw c
      rw [Nat.card_eq_fintype_card] at h
      exact h.trans (by omega)
    have dim : 2*radius C n+1 ≤ (4*(C+34)+5)*(n+1) := by
      unfold radius
      rw [Nat.add_mul]
      ring_nf
      omega
    exact (Nat.mul_le_mul bound dim).trans_eq (Nat.mul_assoc ..).symm
  · intro c m T S callee width correct p fit
    apply guarded_run d c m p C (T p.u) (ctl m p) _ correct
    · exact fun i hi => digit_of_isolated d c m T S callee p C i hi fit
    · intro t _
      have wd := p.query_width m t
      let a : EqualWords := ⟨_,wd.1.trans wd.2.symm,wd.1.symm ▸ p.width_pos⟩
      simpa only [a,wd.1,digitReply,digitQuery] using width a

/-- Each linear-space candidate admits one split exponent that succeeds at
every sufficiently large length, using the very same radius as every other candidate. -/
theorem fixed_split :
    ∃ (d : Driver) (C : ℕ),
      (∀ K : ℕ, ∃ W : ℕ, ∀ c : Cmd, Nat.card (Prog.Ix (Prog.sites [] c)) ≤ K →
        ∀ (n budget : ℕ) (s : List Ltr),
          VisitsAtMost (guarded d c) (initial d c (radius C n) s) budget (W*(n+1))) ∧
      ∀ (c : Cmd) (m : Operands → Word) (T : ℕ → ℕ) (L : ℕ),
        Isolated c m T (fun u => L*(u+1)) →
        (∀ q : EqualWords, (m q.val).length = 2*q.val.1.length) →
        (∀ q : EqualWords, bitValue (m q.val) = bitValue q.val.1 * bitValue q.val.2) →
        ∃ k : ℕ, ∀ p : Input, p.k = k → 2*2^k ≤ p.n → Completed d C c m T p := by
  obtain ⟨d,C,space,complete⟩ := wrapper
  refine ⟨d,C,space,?_⟩
  intro c m T L callee width correct
  obtain ⟨k,hk⟩ := Uniform.exists_dyadic_split L
  refine ⟨k,fun p heq hsize => complete c m T _ callee width correct p ?_⟩
  simpa only [Input.u,Input.r,heq] using (hk p.n hsize).2

end ChunkControl

end NearSquareRoot
end Computability
end OAI
