import OAI.Computability.NearSquareRoot.ScheduleStagingFamily

/-! # Rejecting a staged attempt without reporting a successful halt -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingReject

open IntegerMultiplication TM

variable {A Q I : Type}

def rule (bad : Q → Bool) (m : Rule A Q I) : Rule A Q I := fun q heads =>
  if bad q then some (q, fun i => (heads i, Move.stay)) else m q heads

theorem step (bad : Q → Bool) (m : Rule A Q I) (x : Config A Q I) :
    advance (rule bad m) x = if bad x.pc then some x else advance m x := by
  cases h : bad x.pc with
  | false => simp [advance,rule,h]
  | true =>
    obtain ⟨pc,tapes⟩ := x
    simp only [advance,rule,h,ite_true,Option.map_some,Option.some.injEq,Config.mk.injEq,true_and]
    funext j
    exact SM.Action.apply_stay _

theorem frozen (bad : Q → Bool) (m : Rule A Q I) {x y : Config A Q I} {n : ℕ}
    (tr : Trace (advance (rule bad m)) x n y) (h : bad x.pc = true) : y = x := by
  induction tr with
  | nil => rfl
  | cons hs _ ih =>
    simp only [step,h,ite_true,Option.some.injEq] at hs
    subst_vars
    exact ih h

/-- A finite prefix of the filtered execution is reachable on the source
in at most the same number of transitions, even after entering rejection. -/
theorem reflect (bad : Q → Bool) (m : Rule A Q I) {x y : Config A Q I} {t : ℕ}
    (tr : Trace (advance (rule bad m)) x t y) :
    ∃ k ≤ t, Trace (advance m) x k y := by
  induction tr with
  | nil x => exact ⟨0,le_rfl,.nil x⟩
  | @cons x v y n hs tail ih =>
    cases h : bad x.pc with
    | true =>
      simp only [step,h,ite_true,Option.some.injEq] at hs
      subst v
      rw [frozen bad m tail h]
      exact ⟨0,Nat.zero_le _,.nil _⟩
    | false =>
      obtain ⟨k,hk,path⟩ := ih
      exact ⟨1+k,by omega,.cons (by simpa [step,h] using hs) path⟩

theorem lift (bad : Q → Bool) (m : Rule A Q I)
    (stuck : ∀ x : Config A Q I, bad x.pc = true → advance m x = none)
    {x y : Config A Q I} {t : ℕ} (tr : Trace (advance m) x t y) :
    Trace (advance (rule bad m)) x t y := by
  induction tr with
  | nil => exact .nil _
  | @cons x v _ _ hs _ ih =>
    have ok : bad x.pc = false := by
      cases h : bad x.pc with
      | false => rfl
      | true => rw [stuck _ h] at hs; contradiction
    exact .cons (by simpa [step,ok] using hs) ih

theorem halted (bad : Q → Bool) (m : Rule A Q I) (x : Config A Q I) :
    advance (rule bad m) x = none ↔ advance m x = none ∧ bad x.pc = false := by
  cases h : bad x.pc <;> simp [step,h]

section Product
open CommonAlphabet CommonAlphabet.Pipeline Code Bits ChunkTask ChunkLoop ChunkPhases
open ChunkControl (Driver)

variable [Fintype I] [DecidableEq I]

/-- The finite controls of the guarded loop and of the successful-only loop coincide. -/
noncomputable def successful (d : Driver) (g : Rule Public.Letter Q (Index I)) (q : Q) :=
  rule Prod.fst (StagingProduct.guarded d g q)

theorem reject_stuck (d : Driver) (g : Rule Public.Letter Q (Index I)) (q : Q)
    (x : Config (StagingProtection.Cell d) (StagingProtection.State d (StagingDigit.PC Q I))
      (StagingProtection.Tapes d I)) (h : x.pc.1 = true) :
    advance (StagingProduct.guarded d g q) x = none := by
  simp [advance,StagingProduct.guarded,StagingProtection.rule,ChunkWhole.Mirror.rule,Uniform.Fence.guard,h]

theorem sound (d : Driver) (C : ℕ) (m : Operands → Word) (p : ChunkTask.Input)
    (g : Rule Public.Letter Q (Index I)) (q : Q) (T S : ℕ → ℕ)
    (ctl : StagingPhases.Calls d.load d.test d.prepare d.collect d.emit C m p ((answer m p).map Ltr.bit))
    (callee : StagingCall.Computes g q m T S) (width : StagingProduct.HasWidth m) (correct : StagingProduct.Multiplies m)
    {t y} (run : Trace (advance (successful d g q)) (StagingProtection.initial d C p.n (input p)) t y)
    (halt : advance (successful d g q) y = none) :
    whole (StagingProtection.blank d) ((answer m p).map (StagingProtection.bit d)) (y.tape none) ∧
    (answer m p).length = 2*p.n ∧ bitValue (answer m p) = bitValue p.x * bitValue p.y := by
  obtain ⟨_,_,hist⟩ := reflect _ _ run
  obtain ⟨stop,ok⟩ := (halted _ _ _).mp halt
  exact StagingProduct.sound d C m p g q T S ctl callee width correct hist stop ok

/-- Every physical prefix, including arbitrarily many idle rejecting steps,
has the common input-linear workspace bound. -/
theorem visited (d : Driver) (K C n budget : ℕ) (s : List Ltr)
    (g : Rule Public.Letter Q (Index I)) (q : Q) (size : Nat.card I ≤ K) :
    VisitsAtMost (successful d g q) (StagingProtection.initial d C n s) budget
      (((Nat.card (StagingControl.Axis d)+K+3)*(8*(C+50)+1))*(n+1)) := by
  obtain ⟨cells,cap,cover⟩ := StagingProtection.visited_linear d K C n budget s
    (StagingProduct.digit d g q) StagingDigit.start size
  refine ⟨cells,cap,?_⟩
  intro v hv y pre j
  obtain ⟨u,hu,run⟩ := reflect _ _ pre
  exact cover _ (hu.trans hv) _ run j

/-- The postfilter preserves every bounded successful trace, including its
time and complete literal output. -/
theorem success (d : Driver) (C : ℕ) (m : Operands → Word)
    (g : Rule Public.Letter Q (Index I)) (q : Q) (p : ChunkTask.Input) (t : ℕ)
    (h : StagingProduct.Returns d C m g q p t) :
    ∃ y, FencedRun (successful d g q) (fun _ => -(StagingOuter.radius C p.n : ℤ))
        (fun _ => (StagingOuter.radius C p.n : ℤ)) (StagingProtection.initial d C p.n (input p)) t y ∧
      advance (successful d g q) y = none ∧
      whole (StagingProtection.blank d) ((answer m p).map (StagingProtection.bit d)) (y.tape none) := by
  obtain ⟨y,hist,halt,ok,out⟩ := h
  refine ⟨y,⟨lift _ _ (reject_stuck d g q) hist,?_⟩,(halted _ _ _).mpr ⟨halt,ok⟩,out⟩
  intro v _ y pre j
  obtain ⟨_,_,path⟩ := reflect _ _ pre
  exact StagingProtection.prefix_within d C p.n (input p) (StagingProduct.digit d g q)
    StagingDigit.start path j

end Product
end StagingReject

end NearSquareRoot
end Computability
end OAI
