import OAI.Computability.NearSquareRoot.ScheduleGeneratorStagedPrograms
import OAI.Computability.NearSquareRoot.ScheduleStagingFallbackRoute
import OAI.Computability.NearSquareRoot.ScheduleStagingStartupCandidate

/-! # Positive generated comparisons on the common physical bank -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingComparisonPositive

open IntegerMultiplication TM Code Bits CommonAlphabet Filter Generator
open Generator.Staged (positive positiveStart fullFast)
open StagingFallback (Axes inp out)
open ChunkControl (Driver)
open ChunkTask ChunkLoop ChunkPhases

variable {I : Type} [Fintype I] [DecidableEq I] {Q : ℕ → Type}
    (d : Driver) [DecidableEq (StagingControl.Letter d)] (C : ℕ)
    (g : ∀ j, Rule Public.Letter (Q j) (Pipeline.Index I)) (e : ∀ j, Q j)

local notation "B" => StagingProtection.blank d
local notation "b" => StagingProtection.bit d
local notation "sep" => StagingSerialize.put d Ltr.sep

/-- The positive finite control starts with exactly the two bare operands. -/
noncomputable def initial (l : ℕ) (x y : Word) :=
  initialConfig (positiveStart (I:=I) (Q:=Q) d C l) (inp d I) b sep B x y

/-- A fixed coefficient pays for every positive candidate and every cutoff,
including visits to the parked schoolbook tapes. -/
noncomputable def D (d : Driver) (I : Type) (C : ℕ) :=
  Nat.card (Axes d I) * (2*(24*(C+50)+77)+3)

theorem prefix_within (l : ℕ) (x y : Word) (same : y.length = x.length) {t z}
    (hist : Trace (advance (fullFast d C g e l)) (initial (Q:=Q) d C l x y) t z)
    (i : Axes d I) :
    -((StagingStartup.budget C x.length+1 : ℕ):ℤ) ≤ (z.tape i).pos ∧
      (z.tape i).pos ≤ StagingStartup.budget C x.length+1 := by
  apply StagingFallbackRoute.positive_prefix d I (positive d C g e l) _ x y _ hist i
  intro k v run j
  exact StagingStartupCandidate.prefix_within d (IndexedRules.split l) C _ _ x y same run j

theorem visited (l : ℕ) (x y : Word) (same : y.length = x.length) (clock : ℕ) :
    VisitsAtMost (fullFast d C g e l) (initial (Q:=Q) d C l x y) clock (D d I C*(x.length+1)) := by
  classical
  let _ : Fintype (Axes d I) := Fintype.ofFinite _
  let R := StagingStartup.budget C x.length+1
  obtain ⟨cells,size,cover⟩ := visitsAtMost_of_common_fence (steps:=clock) (-(R:ℤ)) (R:ℤ)
    (fun _ _ _ run i => prefix_within d C g e l x y same run i)
  refine ⟨cells,size.trans ?_,cover⟩
  rw [← Nat.card_eq_fintype_card,show ((R:ℤ)+1-(-(R:ℤ))).toNat = 2*R+1 by omega]
  unfold D
  rw [Nat.mul_assoc]
  apply Nat.mul_le_mul_left
  dsimp [R,StagingStartup.budget]
  nlinarith

/-- An arbitrary generated positive halt publishes the full product. This
applies to all equal-width inputs and imposes no space-fit hypothesis. -/
theorem sound (l : ℕ) (m : Operands → Word) (T S : ℕ → ℕ)
    (ctl : ∀ p : ChunkTask.Input, StagingPhases.Calls d.load d.test d.prepare d.collect d.emit C m p
      ((answer m p).map Ltr.bit))
    (callee : StagingCall.Computes (g (IndexedRules.template l)) (e (IndexedRules.template l)) m T S)
    (width : StagingProduct.HasWidth m) (correct : StagingProduct.Multiplies m)
    (x y : Word) (same : y.length = x.length) {t z}
    (hist : Trace (advance (fullFast d C g e l)) (initial (Q:=Q) d C l x y) t z)
    (halt : advance (fullFast d C g e l) z = none) :
    ∃ w : Word, whole B (w.map b) (z.tape (out d I)) ∧ w.length = 2*x.length ∧
      bitValue w = bitValue x * bitValue y := by
  obtain ⟨v,tr,stop,rfl,_,_,_⟩ := StagingFallbackRoute.positive_halt d I (positive d C g e l)
    (positiveStart d C l) x y hist halt
  obtain ⟨w,hw,hl,hv⟩ := StagingStartupCandidate.sound d (IndexedRules.split l) C m _ _ T S
    ctl callee width correct x y same tr stop
  exact ⟨w,hw,hl,hv⟩

private def LocalFinishes {P : Type} (m : Rule Public.Letter P (Pipeline.Index I)) (s : P)
    (k n : ℕ) (x y : Word) (E H : ℝ) : Prop :=
  ∃ t z w, ((t+1:ℕ):ℝ) ≤ H*n*logScale n^E ∧
    Trace (advance (StagingStartupCandidate.rule d k C m s))
      (StagingStartupCandidate.initial d k C x y) t z ∧
    advance (StagingStartupCandidate.rule d k C m s) z = none ∧
    whole B (w.map b) (z.tape (.inr none)) ∧ w.length = 2*n ∧ bitValue w = bitValue x * bitValue y

private theorem reindex {j j' k k' n : ℕ} {x y : Word} {E H : ℝ} (hj : j = j') (hk : k = k')
    (h : LocalFinishes d C (g j) (e j) k n x y E H) :
    LocalFinishes d C (g j') (e j') k' n x y E H := by
  subst j' k'
  exact h

/-- The selected run retains its clock, its full literal output, a uniform
bound on every head, and a uniform count of all visited physical cells. -/
def Finishes (l n : ℕ) (x y : Word) (E H : ℝ) : Prop :=
  ∃ t z w, ((t+1:ℕ):ℝ) ≤ H*n*logScale n^E ∧
    FencedRun (fullFast d C g e l) (fun _ => -((StagingStartup.budget C n+1 : ℕ):ℤ))
      (fun _ => StagingStartup.budget C n+1)
      (initial (Q:=Q) d C l x y) t z ∧ advance (fullFast d C g e l) z = none ∧
    whole B (w.map b) (z.tape (out d I)) ∧ w.length = 2*n ∧ bitValue w = bitValue x * bitValue y ∧
    VisitsAtMost (fullFast d C g e l) (initial (Q:=Q) d C l x y) t (D d I C*(n+1))

private theorem finishes (l n : ℕ) (x y : Word) (hx : x.length = n) (hy : y.length = n) (E H : ℝ)
    (h : LocalFinishes d C (g (IndexedRules.template l)) (e (IndexedRules.template l))
      (IndexedRules.split l) n x y E H) : Finishes d C g e l n x y E H := by
  obtain ⟨t,z,w,ht,run,stop,word,width,value⟩ := h
  have same := hy.trans hx.symm
  have localRun : FencedRun (positive d C g e l) (fun _ => -((StagingStartup.budget C n+1:ℕ):ℤ))
      (fun _ => ((StagingStartup.budget C n+1:ℕ):ℤ))
      (StagingStartupCandidate.initial d (IndexedRules.split l) C x y) t z :=
    ⟨run,fun _ _ _ hz i => hx ▸ StagingStartupCandidate.prefix_within d _ C _ _ x y same hz i⟩
  obtain ⟨physical,halt,output⟩ := StagingFallbackRoute.positive_run d I (positive d C g e l)
    (positiveStart d C l) x y w localRun stop word
  exact ⟨t,_,w,ht,physical,halt,output,width,value,hx ▸ visited d C g e l x y same t⟩

/-- For the positive template numbered `j+1`, one fixed index `Nat.pair j k`
meets the indicated rate on all sufficiently large equal-width pairs. -/
theorem selected (j : ℕ) (m : Operands → Word) (T S : ℕ → ℕ)
    (ctl : ∀ p : ChunkTask.Input, StagingPhases.Calls d.load d.test d.prepare d.collect d.emit C m p
      ((answer m p).map Ltr.bit))
    (callee : StagingCall.Computes (g (j+1)) (e (j+1)) m T S)
    (width : StagingProduct.HasWidth m) (correct : StagingProduct.Multiplies m)
    (L : ℕ) (linear : ∀ᶠ u : ℕ in atTop, S u ≤ L*(u+1))
    (E A : ℝ) (hE : 0 ≤ E) (hA : 0 ≤ A)
    (time : ∀ᶠ u : ℕ in atTop, (T u : ℝ) ≤ A*u*logScale u^E) :
    ∃ k : ℕ, ∃ H : ℝ, 0 ≤ H ∧ ∀ᶠ n : ℕ in atTop, ∀ x y : Word, x.length = n → y.length = n →
      Finishes d C g e (Nat.pair j k) n x y E H := by
  obtain ⟨k,H,hH,late⟩ := StagingStartupCandidate.selected d C m _ _ T S ctl callee width correct
    L linear E A hE hA time
  refine ⟨k,H,hH,?_⟩
  filter_upwards [late] with n good
  intro x y hx hy
  apply finishes d C g e _ n x y hx hy E H
  exact reindex d C g e (IndexedRules.template_pair j k).symm (IndexedRules.split_pair j k).symm
    (good x y hx hy)

end StagingComparisonPositive

end NearSquareRoot
end Computability
end OAI
