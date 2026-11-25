import OAI.Optimization.LinearProgramming.PriceGame.ControlTrialCore

/-! Bounds on every reachable trial stack, valid at intermediate suspensions and on
arbitrary replies. Fuel decreases on pushes. The remaining count and completed prefix
share one fixed budget in every active or suspended node. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace PriceGame
namespace Control
namespace Trial

universe u
variable {I P R C Q : Type u}

def StackShape (depth calls : ℕ) : List (Frame I P C) → Prop
  | [] => True
  | f :: fs => StackShape depth calls fs ∧ fs.length + f.childFuel + 1 ≤ depth ∧
    f.prefix.length + f.remaining + 1 ≤ calls

def LocalShape (depth calls ticks level : ℕ) : PC I P R C → Prop
  | .enter fuel _ => level + fuel ≤ depth
  | .schedule fuel remaining _ rows => level + fuel + 1 ≤ depth ∧ rows.length + remaining ≤ calls
  | .returned _ => level ≤ depth
  | .feedback f _ replies => level + f.childFuel + 1 ≤ depth ∧
    f.prefix.length + f.remaining + 1 ≤ calls ∧ replies.length ≤ ticks

def Shape (depth calls ticks : ℕ) (s : State I P R C) : Prop :=
  StackShape depth calls s.stack ∧ LocalShape depth calls ticks s.stack.length s.pc

theorem initial_shape (depth calls : ℕ) (i : I) :
    Shape depth calls 0 (initial (P:=P) (R:=R) (C:=C) depth i) :=
  ⟨True.intro, by simp [initial,LocalShape]⟩

theorem shape_step (ops : Kernel I P R C Q) (depth calls ticks : ℕ)
    (s : State I P R C) (hs : Shape depth calls ticks s) :
    match step ops calls s with
    | .halt _ => True
    | .proceed t => Shape depth calls (ticks+1) t
    | .ask _ no yes => Shape depth calls (ticks+1) no ∧ Shape depth calls (ticks+1) yes := by
  rcases s with ⟨pc,stack⟩
  obtain ⟨ss,hpc⟩ := hs
  cases pc with
  | enter fuel i =>
    cases fuel with
    | zero =>
      exact ⟨ss,by simpa [LocalShape] using hpc⟩
    | succ f =>
      exact ⟨ss,by simpa [step,LocalShape, Nat.add_assoc] using
        (show stack.length + (f+1) ≤ depth from hpc),by simp⟩
  | schedule fuel rem i rows =>
    change stack.length + fuel + 1 ≤ depth ∧ rows.length + rem ≤ calls at hpc
    cases rem with
    | zero => exact ⟨ss,by dsimp [LocalShape]; omega⟩
    | succ k =>
      refine ⟨⟨ss,hpc.1,?_⟩,?_⟩
      · exact hpc.2
      · change (stack.length+1) + fuel ≤ depth
        omega
  | returned out =>
    cases stack with
    | nil => exact True.intro
    | cons f fs =>
      change StackShape depth calls fs ∧ fs.length + f.childFuel + 1 ≤ depth ∧
        f.prefix.length + f.remaining + 1 ≤ calls at ss
      exact ⟨ss.1,ss.2.1,ss.2.2,by simp⟩
  | feedback f out replies =>
    change stack.length + f.childFuel + 1 ≤ depth ∧
      f.prefix.length + f.remaining + 1 ≤ calls ∧ replies.length ≤ ticks at hpc
    cases hfin : ops.finish f.input f.prefix f.prepared out replies with
    | inl c =>
      simp only [step,hfin]
      exact ⟨ss,hpc.1,by simp only [List.length_append,List.length_singleton]; omega⟩
    | inr q =>
      simp only [step,hfin]
      constructor <;> exact ⟨ss,hpc.1,hpc.2.1,by simpa using hpc.2.2⟩

theorem Steps.shape {ops : Kernel I P R C Q} {calls n : ℕ} {s t : State I P R C} {tr}
    (hs : Steps ops calls s tr n t) {d k : ℕ} (h : Shape d calls k s) : Shape d calls (k+n) t := by
  induction hs generalizing k with
  | refl => simpa using h
  | silent step _ ih =>
    have hn := shape_step ops d calls k _ h
    rw [step] at hn
    simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ih (k:=k+1) hn
  | answer reply step _ ih =>
    have hn := shape_step ops d calls k _ h
    rw [step] at hn
    cases reply with
    | false => simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ih (k:=k+1) hn.1
    | true => simpa [Nat.add_comm,Nat.add_left_comm,Nat.add_assoc] using ih (k:=k+1) hn.2

theorem shape_of_reachable {ops : Kernel I P R C Q} {calls n depth : ℕ} {i : I}
    {s : State I P R C} {tr} (run : Steps ops calls (initial depth i) tr n s) :
    Shape depth calls n s := by
  simpa using run.shape (initial_shape depth calls i)

theorem stack_length_of_shape {depth calls ticks : ℕ} {s : State I P R C} (ok : Shape depth calls ticks s) :
    s.stack.length ≤ depth := by
  have h := ok.2
  cases e : s.pc <;> rw [e] at h <;> simp only [LocalShape] at h <;> omega

theorem frame_sizes_of_shape {depth calls ticks : ℕ} {s : State I P R C} (ok : Shape depth calls ticks s)
    (f : Frame I P C) (hf : f ∈ s.stack) :
    f.childFuel ≤ depth ∧ f.remaining ≤ calls ∧ f.prefix.length ≤ calls := by
  have aux (fs : List (Frame I P C)) (h : StackShape depth calls fs) (m : f ∈ fs) :
      f.childFuel ≤ depth ∧ f.remaining ≤ calls ∧ f.prefix.length ≤ calls := by
    induction fs with
    | nil => simp at m
    | cons a fs ih =>
      obtain ⟨hfs,hd,hc⟩ := h
      rcases List.mem_cons.mp m with rfl | hmm
      · omega
      · exact ih hfs hmm
  exact aux _ ok.1 hf

end Trial
end Control
end PriceGame
end LinearProgramming
end Optimization
end OAI
