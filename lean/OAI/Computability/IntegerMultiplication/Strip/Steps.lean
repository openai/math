import OAI.Computability.IntegerMultiplication.Spindle.All

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code
variable {I J K : Type} {r : Regime I} {L M : I→ℕ} {f g : I→ℝ} {A B Z : I → Tree}

/-- Loop compiled with uniform constant (essential for passing over varying list lengths).
Both sides of cover used to choose actual program by tag; cover needn't be injective. -/
theorem forkTwo
    (tag : I→Bool) (hi : J→I) (low : K→I)
    (covers : ∀ i,(tag i=false → ∃ k,i=low k) ∧ (tag i=true → ∃ j,i=hi j))
    (s : Sized (f ∘ low) (A ∘ low) (B ∘ low))
    (t : Sized (f ∘ hi) (A ∘ hi) (B ∘ hi)) :
    Sized f (together (send ∘ tag) A) B := by
  classical
  have z : ∀ i,1≤f i := by
    intro i
    cases h : tag i
    · obtain ⟨k,rfl⟩ := (covers i).1 h; exact s.1 _
    obtain ⟨j,rfl⟩ := (covers i).2 h; exact t.1 _
  refine ⟨z,(fun i=>⌈f i⌉₊),Task.control tag ?_ ?_,3,?_⟩
  · let X := {i // tag i=false}
    choose k e using fun i:X=> (covers i.1).1 i.2
    simpa only [Function.comp_def,← e] using Task.on s.release k
  · let X := {i // tag i=true}
    choose j e using fun i:X=> (covers i.1).2 i.2
    simpa only [Function.comp_def,← e] using Task.on t.release j
  intro i; specialize z i
  have h := Nat.ceil_lt_add_one (show 0≤f i by linarith)
  push_cast; linarith

theorem classify_b
    (tag : I→Bool) (z : Rip r M L A (send ∘ tag)) (hi : J→I) (low : K→I)
    (covers : ∀ i,(tag i=false → ∃ k,i=low k) ∧ (tag i=true → ∃ j,i=hi j))
    (s : Breeze (f ∘ low) (r.pull low) (M ∘ low) (L ∘ low) (A ∘ low) (B ∘ low))
    (t : Breeze (f ∘ hi) (r.pull hi) (M ∘ hi) (L ∘ hi) (A ∘ hi) (B ∘ hi)) :
    Breeze f r M L A B := by
  have q : ∀ i,1 ≤ f i := by
    intro i
    cases h : tag i
    · obtain ⟨k,rfl⟩ := (covers i).1 h; exact s.1 _
    obtain ⟨j,rfl⟩ := (covers i).2 h; exact t.1 _
  obtain ⟨_,k,z₀⟩ := Breeze.launch (z.twice z.again) q
  obtain ⟨_,m,S⟩ := s
  obtain ⟨_,n,T⟩ := t
  let Z := runrate f r M L
  let c := k+m+n
  have P := z₀.larger (fun i=> rate_higher i (q i) (by omega : k≤c))
  refine ⟨q,c,P.sequence (forkTwo tag hi low covers ?_ ?_)⟩
  · exact S.runs.mono (fun i=> rate_higher (r:=r) (n:=M) (l:=L) (low i) (q _) (by omega : m≤c))
  exact T.runs.mono (fun i=> rate_higher (r:=r) (n:=M) (l:=L) (hi i) (q _) (by omega : n≤c))

open _root_.OAI.Computability.IntegerMultiplication.Code.Task
/-- List schedules: move from one layout frame to another with a supplied Tag.
Scale/record costs must not increase after each jump. Goal coefficientwise runtime
upper bounded by cumulative factor charge. -/
theorem spin (tag : I→Bool) (z : Rip r M L A (send ∘ tag))
    (step : I→Option I) (low : K→I)
    (hi : J→I) (covers : ∀ i,(tag i=false→∃k,i=low k)∧(tag i=true→∃ j,i=hi j))
    (finish : ∀ i,step (low i)=Option.none)
    (dest : J→I) (continues : ∀ j,step (hi j)=some (dest j))
    (s : Breeze (f ∘ low) (r.pull low) (M ∘ low) (L ∘ low) (A ∘ low) (B ∘ low))
    (t : Breeze (f ∘ hi) (r.pull hi) (M ∘ hi) (L ∘ hi) (A ∘ hi) (A ∘ dest))
    (eq : ∀ i j, step i=some j → B j=B i)
    (ledger : ∀ i,0 ≤ g i)
    (terminal : ∀ i, step i=Option.none→ f i ≤ g i)
    (charge : ∀ i j, step i=some j→
      g i ≥ f i+g j ∧ M j ≤ M i ∧ L j ≤ L i ∧ r.scale j ≤ r.scale i) :
    Breeze g r M L A B := by
  let e (i:I) := Option.elim (step i) Event.done Event.jump
  let V i := Event.signal A B i (e i)
  have sl : Breeze (f ∘ low) (r.pull low) (M ∘ low) (L ∘ low) (A ∘ low) (V ∘ low) := by
    obtain ⟨a,b,c⟩ := s
    refine ⟨a,b,?_⟩
    suffices h : V ∘ low=together (fun _=>Tree.atom false) (B ∘ low) by
      rw [h]; exact (fixture c.small c.budget _).twice c
    simp [Function.comp_def,V,e,finish,Event.signal]
  have su : Breeze (f ∘ hi) (r.pull hi) (M ∘ hi) (L ∘ hi) (A ∘ hi) (V ∘ hi) := by
    obtain ⟨a,b,c⟩ := t
    refine ⟨a,b,?_⟩
    suffices h : V ∘ hi=together (fun _=>Tree.atom true)
      (together (fun _=>Tree.atom false) (A ∘ dest)) by
      rw [h]; exact (fixture c.small c.budget _).twice ((fixture c.small c.budget _).twice c)
    simp [Function.comp_def,V,e,continues,Event.signal]
  obtain ⟨a,b,c⟩ := (classify_b (B:=V) (f:=f) tag z hi low covers sl su)
  let N := mass r M L b
  let W := runrate g r M L b
  have u (i) : 0 < N i := by
    have z := c.budget i
    by_contra! e
    exact absurd (mul_nonpos_of_nonpos_of_nonneg e (show 0≤f i by linarith [a i]))
      (not_le_of_gt (lt_of_lt_of_le (by norm_num : (0:ℝ)<1) z))
  have v i : f i ≤ g i := by
    cases y : step i with
    | none => exact terminal i y
    | some j =>
      have q := (charge _ _ y).1
      linarith [ledger j]
  have l i : 1 ≤ g i := (a i).trans (v i)
  have h i : runrate f r M L b i ≤ W i :=
    mul_le_mul_of_nonneg_left (v i) (u i).le
  refine ⟨l,b,⟨Sized.suspend e c.runs ?_ (fun i=> (c.budget i).trans (h i)) ?_, (c.larger h).small⟩⟩
  · intro i
    cases y : step i with
    | none => simp only [e,y]; trivial
    | some j => unfold e; rw [y]; exact eq _ _ y
  intro i
  cases k : step i with
  | none => simpa [k,e] using h i
  | some j =>
    unfold e; rw [k]
    change N i*f i+N j*g j ≤ N i*g i
    obtain ⟨m,P,T,S⟩ := charge _ _ k
    have o : N j ≤ N i := by unfold N mass; gcongr
    calc
     _ ≤ N i*f i+N i*g j := by gcongr; exact ledger j
     _ ≤ N i*g i := by rw [← mul_add]; exact mul_le_mul_of_nonneg_left m (u i).le

end Strip

end IntegerMultiplication
end Computability
end OAI
