import OAI.Computability.NearSquareRoot.ScheduleStagingStartupExecution

/-! # Raw-input candidate family for the uniform schedule

The split exponent belongs to finite control. Every attempt begins with two
bare binary strings and a separator on the public input. A halt returns the
whole padded product on a separate public output tape. The common space
bound also covers an aborted guard and an inadmissible split.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingStartupCandidate

open IntegerMultiplication TM Code Bits CommonAlphabet CommonAlphabet.Pipeline Filter
open ChunkControl (Driver)
open ChunkTask ChunkLoop ChunkPhases
open StagingProtection (Cell Tapes)

variable {I Q : Type} [Fintype I] [DecidableEq I] (d : Driver)

abbrev PostState (d : Driver) (Q I : Type) := StagingProtection.State d (StagingDigit.PC Q I)
abbrev State (d : Driver) (k C : ℕ) (Q I : Type) := StagingStartup.PC k (StagingWidth.Phase C) ⊕ PostState d Q I

noncomputable def entry : PostState d Q I :=
  (false,some (.inl (.inl (ChunkDispatch.start (StagingOpen.cmd d) .load))))

def start (k C : ℕ) : State d k C Q I := .inl (StagingStartup.start k)

noncomputable def initial (k C : ℕ) (x y : Word) :
    Config (Cell d) (State d k C Q I) (StagingStartup.Axis d I) :=
  initialConfig (start d k C) (.inl false) (StagingProtection.bit d) (StagingSerialize.put d .sep)
    (StagingProtection.blank d) x y

variable [DecidableEq (StagingControl.Letter d)]

noncomputable def rule (k C : ℕ) (g : Rule Public.Letter Q (Index I)) (q : Q) :
    Rule (Cell d) (State d k C Q I) (StagingStartup.Axis d I) :=
  StagingStartup.machine d k C (StagingReject.successful d g q) (entry d)

omit [Fintype I] [DecidableEq I] [DecidableEq (StagingControl.Letter d)] in
theorem installed (C n : ℕ) (s : List Ltr) :
    StagingStartup.staged (I:=I) d (entry (I:=I) (Q:=Q) d) C n s =
      StagingProtection.initial d C n s := rfl

/-- Any successful post-startup computation executes from the ordinary
one-tape initial configuration with only the common linear startup cost. -/
theorem execute (C : ℕ) (m : Operands → Word) (g : Rule Public.Letter Q (Index I)) (q : Q)
    (p : Input) {t} (h : StagingProduct.Returns d C m g q p t) :
    ∃ u ≤ StagingStartup.budget C p.n+1+t, ∃ z,
      Trace (advance (rule d p.k C g q)) (initial d p.k C p.x p.y) u z ∧
      advance (rule d p.k C g q) z = none ∧
      whole (StagingProtection.blank d) ((answer m p).map (StagingProtection.bit d)) (z.tape (.inr none)) := by
  obtain ⟨y,tr,halt,out⟩ := StagingReject.success d C m g q p t h
  have hist : Trace (advance (StagingReject.successful d g q))
      (StagingStartup.staged d (entry d) C p.n (input p)) t y := by
    rw [installed]
    exact tr.1
  obtain ⟨u,hu,actual,stop⟩ := StagingStartup.execute d C p _ _ hist halt
  exact ⟨u,hu,_,actual,stop,out⟩

/-- Every halt at every fixed split returns the properly padded product.
Oversized exponents are excluded by their physical stationary rejection loop. -/
theorem sound (k C : ℕ) (m : Operands → Word) (g : Rule Public.Letter Q (Index I)) (q : Q)
    (T S : ℕ → ℕ) (ctl : ∀ p : Input, StagingPhases.Calls d.load d.test d.prepare d.collect d.emit C m p
      ((answer m p).map Ltr.bit))
    (callee : StagingCall.Computes g q m T S) (width : StagingProduct.HasWidth m)
    (correct : StagingProduct.Multiplies m) (x y : Word) (same : y.length = x.length)
    {t z} (hist : Trace (advance (rule d k C g q)) (initial d k C x y) t z)
    (halt : advance (rule d k C g q) z = none) :
    ∃ w : Word, whole (StagingProtection.blank d) (w.map (StagingProtection.bit d)) (z.tape (.inr none)) ∧
      w.length = 2*x.length ∧ bitValue w = bitValue x * bitValue y := by
  by_cases fit : 2^k ≤ x.length
  · let p : Input := ⟨x,y,k,same,fit⟩
    obtain ⟨_,_,v,tr,stop,eq⟩ := StagingStartup.reflect d C p (StagingReject.successful d g q) (entry d) hist halt
    rw [installed] at tr
    rw [eq]
    exact ⟨_,StagingReject.sound d C m p g q T S (ctl p) callee width correct tr stop⟩
  · exact False.elim ((StagingStartup.oversize_ne_halt d k C (StagingReject.successful d g q) (entry d)
      x y (by omega) hist) halt)

theorem prefix_within (k C : ℕ) (g : Rule Public.Letter Q (Index I)) (q : Q)
    (x y : Word) (same : y.length = x.length) {t z}
    (hist : Trace (advance (rule d k C g q)) (initial d k C x y) t z) (i : StagingStartup.Axis d I) :
    -((StagingStartup.budget C x.length+1 : ℕ):ℤ) ≤ (z.tape i).pos ∧
      (z.tape i).pos ≤ StagingStartup.budget C x.length+1 := by
  by_cases fit : 2^k ≤ x.length
  · let p : Input := ⟨x,y,k,same,fit⟩
    apply StagingStartup.prefix_fit d C p (StagingReject.successful d g q) (entry d) _ hist i
    intro a v h j
    rw [installed] at h
    obtain ⟨_,_,tr⟩ := StagingReject.reflect _ _ h
    exact StagingProtection.prefix_within d C p.n (input p) (StagingProduct.digit d g q) StagingDigit.start tr j
  · have small := StagingStartup.oversize_prefix d k C (StagingReject.successful d g q) (entry d)
      x y (by omega) hist i
    have size : x.length ≤ StagingStartup.budget C x.length := by unfold StagingStartup.budget; nlinarith
    omega

/-- Only the controller and the global digit tape count enter the linear
space coefficient, including for cutoffs far beyond a rejection. -/
theorem visited (K k C clock : ℕ) (g : Rule Public.Letter Q (Index I)) (q : Q)
    (x y : Word) (same : y.length = x.length) (tapes : Nat.card I ≤ K) :
    VisitsAtMost (rule d k C g q) (initial d k C x y) clock
      (((Nat.card (StagingControl.Axis d)+K+5)*(2*(24*(C+50)+77)+3))*(x.length+1)) := by
  classical
  let : Fintype (StagingStartup.Axis d I) := Fintype.ofFinite _
  let b := StagingStartup.budget C x.length+1
  have box := visitsAtMost_of_common_fence (m:=rule d k C g q) (init:=initial d k C x y) (steps:=clock)
    (-(b:ℤ)) (b:ℤ) (fun _ _ _ r i => prefix_within d k C g q x y same r i)
  obtain ⟨cells,h,cover⟩ := box
  refine ⟨cells,h.trans ?_,cover⟩
  have count : Fintype.card (StagingStartup.Axis d I) ≤ Nat.card (StagingControl.Axis d)+K+5 := by
    rw [← Nat.card_eq_fintype_card]
    change Nat.card (Bool ⊕ Option (Option (StagingControl.Axis d ⊕ Option I))) ≤ _
    rw [Nat.card_sum,Finite.card_option,Finite.card_option,Nat.card_sum,Finite.card_option (α:=I)]
    have cardBool : Nat.card Bool = 2 := by simp
    omega
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul count
  rw [show ((b:ℤ)+1-(-(b:ℤ))).toNat=2*b+1 by omega]
  dsimp only [b,StagingStartup.budget]
  nlinarith

/-- The initialization clock is absorbed into the selected candidate's
original logarithmic rate on all positive input lengths. -/
theorem startup_rate (C n t u : ℕ) (e H : ℝ) (hn : 1 ≤ n) (he : 0 ≤ e)
    (source : ((t+1:ℕ):ℝ) ≤ H*n*logScale n^e)
    (cost : u ≤ StagingStartup.budget C n+1+t) :
    ((u+1:ℕ):ℝ) ≤ (H+(2*(24*(C+50)+77)+1 : ℕ))*n*logScale n^e := by
  let B := 24*(C+50)+77
  have extra : StagingStartup.budget C n+1 ≤ (2*B+1)*n := by
    change B*(n+1)+1 ≤ (2*B+1)*n
    have := Nat.mul_le_mul_left B hn
    nlinarith
  have sum : u+1 ≤ (2*B+1)*n+(t+1) := by omega
  have sumR : (u+1:ℝ) ≤ (2*B+1)*n+(t+1) := by exact_mod_cast sum
  have hn' : (1:ℝ) ≤ n := by exact_mod_cast hn
  have hlog : 1 ≤ logScale n^e := Real.one_le_rpow (by unfold logScale; linarith [Real.log_nonneg hn']) he
  have lin : (2*(B:ℝ)+1)*n ≤ (2*(B:ℝ)+1)*n*logScale n^e :=
    le_mul_of_one_le_right (by positivity) hlog
  rw [Nat.cast_add,Nat.cast_one] at source ⊢
  change (u:ℝ)+1 ≤ (H+((2*B+1:ℕ):ℝ))*n*logScale n^e
  push_cast
  linarith only [sumR,source,lin]

/-- For each candidate with a linear-space digit implementation and the
indicated logarithmic exponent, one hardcoded split succeeds on all large
equal-width ordinary input pairs. This includes the initial tape preparation. -/
theorem selected (C : ℕ) (m : Operands → Word) (g : Rule Public.Letter Q (Index I)) (q : Q)
    (T S : ℕ → ℕ) (ctl : ∀ p : Input, StagingPhases.Calls d.load d.test d.prepare d.collect d.emit C m p
      ((answer m p).map Ltr.bit))
    (callee : StagingCall.Computes g q m T S) (width : StagingProduct.HasWidth m)
    (correct : StagingProduct.Multiplies m) (L : ℕ) (linear : ∀ᶠ u : ℕ in atTop, S u ≤ L*(u+1))
    (e A : ℝ) (he : 0 ≤ e) (hA : 0 ≤ A)
    (time : ∀ᶠ u : ℕ in atTop, (T u : ℝ) ≤ A*u*logScale u^e) :
    ∃ k : ℕ, ∃ H : ℝ, 0 ≤ H ∧ ∀ᶠ n : ℕ in atTop, ∀ x y : Word, x.length = n → y.length = n →
      ∃ t z w, ((t+1:ℕ):ℝ) ≤ H*n*logScale n^e ∧
        Trace (advance (rule d k C g q)) (initial d k C x y) t z ∧ advance (rule d k C g q) z = none ∧
        whole (StagingProtection.blank d) (w.map (StagingProtection.bit d)) (z.tape (.inr none)) ∧
        w.length = 2*n ∧ bitValue w = bitValue x * bitValue y := by
  obtain ⟨k,H,hH,late⟩ := StagingProduct.selected d C m g q T S ctl callee width correct L linear e A he hA time
  refine ⟨k,H+((2*(24*(C+50)+77)+1:ℕ):ℝ),by positivity,?_⟩
  filter_upwards [late,eventually_ge_atTop (1:ℕ)] with n hs hn
  intro x y hx hy
  let p : Input := ⟨x,y,k,hy.trans hx.symm,hx ▸ hs.1⟩
  obtain ⟨t,ht,ret⟩ := hs.2 p hx rfl
  obtain ⟨u,hu,z,tr,stop,out⟩ := execute d C m g q p ret
  have spec := answer_spec m correct p
  change u ≤ StagingStartup.budget C x.length+1+t at hu
  rw [hx] at hu
  exact ⟨u,z,answer m p,startup_rate C n t u e H hn he ht hu,tr,stop,out,
    spec.1.trans (congrArg (2*·) hx),spec.2⟩

end StagingStartupCandidate

end NearSquareRoot
end Computability
end OAI
