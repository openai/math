import OAI.Computability.BorderVNP.CoverDeckPackState

/-!
# A sequence of public pack motions

The stage network reads the new candidates and the previous two banks.
Every stage retains the earlier finite-motion flags and pullback keys. One
initial false gate provides zero counts and numerators. Subsequent stages
add the cost of the stage once each.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cover.AddressCircuit

open PackedDeckCandidate
open VPVNP.VerifierNetwork (Frame)
open BinPackingGames.Foundations.Complexity.CookLevin

/-- Candidate count rows for all input packs. -/
abbrev PackTables (B : Type*) (q l m w K : ℕ) :=
  Fin K × Fin m × B × (Fin q → Deck l) × Fin w

/-- The latest banks and the finite-motion flags and pullback keys of all
already processed packs. -/
abbrev PackTracePins (B : Type*) (q l m w t : ℕ) :=
  PriorPins B q l w ⊕ (Fin t × (Fin m ⊕ Fin (keyWidth q l)))

/-- A chosen motion's ordinal and key inside a completed pack's output. -/
def motionPin {B : Type*} {q l m w : ℕ} : Fin m ⊕ Fin (keyWidth q l) → BankStatePins B q l m w :=
  Sum.elim (fun i => .inl (.inl (.inl (.inr i)))) (fun b => .inl (.inr b))

/-- Pin of the current stage input in the retained original table and prior
banks. Only the indicated pack's candidate rows are read. -/
def stagePin {B : Type*} {q l m w K : ℕ} (i : Fin K) :
    Input B (Fin q → Deck l) m w → PackTables B q l m w K ⊕ PriorPins B q l w
  | .inl (none,p) => .inr (.inl p)
  | .inl (some c,p) => .inl (i,c,p)
  | .inr p => .inr (.inr p)

/-- Assemble the current stage's actual inputs from its finite candidates
and the running physical and mean banks. -/
def stageAssignment {B : Type*} {q l m w K : ℕ} (z : PackTables B q l m w K → Bool)
    (prior : PriorPins B q l w → Bool) (i : Fin K) : Input B (Fin q → Deck l) m w → Bool :=
  Sum.elim z prior ∘ stagePin i

/-- Deterministic running banks, starting at zero. Out-of-range steps stop
reading candidate rows; the compiled run only uses the first K steps. -/
noncomputable def priorAt {B : Type*} [Fintype B] {q l m w K : ℕ}
    (step : Frame (Input B (Fin q → Deck l) m w) (BankStatePins B q l m w))
    (z : PackTables B q l m w K → Bool) : ℕ → PriorPins B q l w → Bool
  | 0 => fun _ => false
  | r+1 => if hr : r < K then step.eval (stageAssignment z (priorAt step z r) ⟨r,hr⟩) ∘ nextPriorPin
           else priorAt step z r

/-- Complete physical state computed at one of the valid pack indices. -/
noncomputable def stateAt {B : Type*} [Fintype B] {q l m w K : ℕ}
    (step : Frame (Input B (Fin q → Deck l) m w) (BankStatePins B q l m w))
    (z : PackTables B q l m w K → Bool) (i : Fin K) : BankStatePins B q l m w → Bool :=
  step.eval (stageAssignment z (priorAt step z i.val) i)

theorem priorAt_succ {B : Type*} [Fintype B] {q l m w K : ℕ}
    (step : Frame (Input B (Fin q → Deck l) m w) (BankStatePins B q l m w))
    (z : PackTables B q l m w K → Bool) (i : Fin K) :
    priorAt step z (i.val+1) = stateAt step z i ∘ nextPriorPin := by simp [priorAt,stateAt,i.isLt]

/-- Expected values of the trace ports after a specified prefix. -/
noncomputable def traceAssignment {B : Type*} [Fintype B] {q l m w K r : ℕ}
    (step : Frame (Input B (Fin q → Deck l) m w) (BankStatePins B q l m w))
    (z : PackTables B q l m w K → Bool) (hr : r ≤ K) : PackTracePins B q l m w r → Bool :=
  Sum.elim (priorAt step z r) fun p => stateAt step z (Fin.castLE hr p.1) (motionPin p.2)

/-- Compile the successive pack motions as one circuit, retaining all selected
flags and keys. The K input arrays remain shared between the layers. -/
theorem traceFrame {B : Type*} [Fintype B] {q l m w K : ℕ}
    (step : Frame (Input B (Fin q → Deck l) m w) (BankStatePins B q l m w)) (r : ℕ) (hr : r ≤ K) :
    ∃ f : Frame (PackTables B q l m w K) (PackTracePins B q l m w r),
      f.size ≤ 1 + r*step.size ∧ ∀ z, f.eval z = traceAssignment step z hr := by
  induction r with
  | zero =>
    let gate := (Frame.initial (Empty.elim : Empty → PackTables B q l m w K)).step (fun _ : Unit => .const false)
    let f : Frame (PackTables B q l m w K) (PackTracePins B q l m w 0) := gate.select (fun _ => ())
    have hs := Frame.step_size_le (Frame.initial (Empty.elim : Empty → PackTables B q l m w K))
      (fun _ : Unit => .const false) 1 (fun _ => le_rfl)
    refine ⟨f,by simpa [f,gate] using hs,?_⟩
    intro z
    funext p
    rcases p with p | ⟨i,_⟩
    · simp [f,gate,traceAssignment,priorAt,StatementCircuit.Expr.eval]
    · exact i.elim0
  | succ r ih =>
    obtain ⟨old,hsize,hold⟩ := ih (by omega)
    let i : Fin K := ⟨r,by omega⟩
    let Mid := PackTables B q l m w K ⊕ PackTracePins B q l m w r
    let feed : Frame Mid (Input B (Fin q → Deck l) m w) :=
      Frame.initial (fun p => (stagePin i p).elim Sum.inl (fun a => .inr (.inl a)))
    let run := (step.subst feed).withInput
    let route : PackTracePins B q l m w (r+1) → Mid ⊕ BankStatePins B q l m w :=
      Sum.elim (fun a => .inr (nextPriorPin a))
        (fun p => Fin.lastCases (.inr (motionPin p.2)) (fun j => .inl (.inr (.inr (j,p.2)))) p.1)
    let f := (run.select route).subst old.withInput
    refine ⟨f,?_,?_⟩
    · have hh : old.withInput.size = old.size := Frame.withInput_size old
      simpa [f,run,feed,hh,Nat.succ_mul,Nat.add_assoc] using Nat.add_le_add_right hsize step.size
    · intro z
      let mid := old.withInput.eval z
      have input : feed.eval mid = stageAssignment z (priorAt step z r) i := by
        funext p
        rcases p with ⟨_|c,p⟩ | p <;> simp [feed,mid,stageAssignment,stagePin,hold,traceAssignment]
      funext p
      rcases p with p | ⟨j,b⟩
      · change f.eval z (.inl p) = priorAt step z (r+1) p
        have hnext : priorAt step z (r+1) = stateAt step z i ∘ nextPriorPin := priorAt_succ step z i
        rw [hnext]
        simp [f,run,route,← show mid = old.withInput.eval z from rfl,input,stateAt,i]
      · induction j using Fin.lastCases with
        | last =>
          have hi : Fin.castLE hr (Fin.last r) = i := by apply Fin.ext; rfl
          simp [f,run,route,← show mid = old.withInput.eval z from rfl,input,traceAssignment,stateAt,hi]
        | cast j =>
          simp only [f,Frame.subst_eval,Frame.select_eval,run,route,Sum.elim_inr,Fin.lastCases_castSucc,
            Frame.withInput_eval_inl]
          exact (Frame.withInput_eval_inr old z (.inr (j,b))).trans (congrFun (hold z) (.inr (j,b)))

/-- The full compiled tower of pack choices and the verified one-pack
transition used at every stage. -/
theorem packSequence_frames (B : Type) [Fintype B] (q m : ℕ) (prob : Fin m → ℚ)
    (hn : ∀ i, 0 ≤ prob i) (hsum : ∑ i, prob i = 1) :
    ∃ P D p : ℕ, 0 < P ∧ ∀ K l w : ℕ, 1 ≤ l → P < 2^w →
      ∃ (step : Frame (Input B (Fin q → Deck l) m w) (BankStatePins B q l m w))
        (f : Frame (PackTables B q l m w K) (PackTracePins B q l m w K)),
        f.size ≤ 1 + K*(Fintype.card (Fin q → Deck l)*D*(l+w+1)^p) ∧
        (∀ x base N A, PackInputFits q l m w P N A x base →
          ∃ j h, BankState P prob x base (step.eval x) j h) ∧
        ∀ z, f.eval z = traceAssignment step z (le_rfl : K ≤ K) := by
  obtain ⟨P,D,p,hP,make⟩ := bankState_frames B q m prob hn hsum
  refine ⟨P,D,p,hP,?_⟩
  intro K l w hl hw
  obtain ⟨step,hs,he⟩ := make l w hl hw
  obtain ⟨f,hf,htrace⟩ := traceFrame step K le_rfl
  exact ⟨step,f,hf.trans (Nat.add_le_add_left (Nat.mul_le_mul_left K hs) _),he,htrace⟩

end Cover.AddressCircuit

end BorderVNP
end Computability
end OAI
