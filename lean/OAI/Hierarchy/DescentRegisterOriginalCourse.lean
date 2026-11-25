import OAI.Hierarchy.DescentRegisterObservedPath
import OAI.Hierarchy.DescentChronologicalHeld

namespace OAI
/-! # The selected census, saved rotations and private meter on one registered history -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler DescentKernelHistory Computability.BorderVNP.Crossing Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {d k wire hist len w : ℕ} {bits : P→ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist len bits d)
    {bn bd : ℕ} (b : Menu bn bd) (initial : Position) (c : C) (m : Memory w)
local notation "branch" => traces c
local notation "cpu" => instruction (w:=w) traces b initial
local notation "cursor" => calendar (w:=w) traces b initial
local notation "ram" => DateCode.history cpu m
variable (limit : ℕ) (valid : Prop)

structure OriginalCourse : Prop where
  advance : ∀i (e:(branch).path.Event i), advances traces b initial c m limit valid i e
  resetWords : ∀i (e:(branch).path.Event i), e.isReset=true → valid →
    e.incoming (cursor i) (ram i) → capturedWords traces b initial c m i e

/-- The counter is cumulative at an ordinary date and survives intact across a reset. -/
def privateStep (header i:ℕ) (e:(branch).path.Event i) : Prop := by
  cases e with
  | ordinary before ticket after joined=>
    exact before.Held header (ram i) → (before.ordinary ticket).Held header (ram (i+1))
  | reset before B after joined=>exact ram (i+1) header=ram i header

variable (header:ℕ)
variable (fixed:∀i (x y : RunTrace.Events traces i) (a z : Move w),
  issued (w:=w) traces b i x (calendar (w:=w) traces b initial i) a →
  issued (w:=w) traces b i y (calendar (w:=w) traces b initial i) z → a=z)
variable (seed:initial.ports.held (branch).first initial.floor m)
variable (earned:OriginalCourse traces b initial c m limit valid)
variable (meter:∀i (e:(branch).path.Event i),valid→e.incoming (cursor i) (ram i)→
  privateStep traces b initial c m header i e)

include fixed seed earned meter in
omit [Fintype P] in
theorem original_private_held (zero:m header=0) (live:valid) :
    (branch).path.Held header (ram len) := by
  have carried {U:MarkedWorld F d P bits} {i z D:ℕ} {r:Reached U G q ε S k i z D wire hist}
      (pre:Path (branch).first r) (post:Path r (branch).last)
      (joined:pre.append post=(branch).path) : pre.Held header (ram i) := by
    induction pre with
    | here=>exact Path.Held.seed header m zero
    | @ordinary _ age _ _ _ _ src prior _ he T ballot norm dst ticket ih=>
      let ev:(branch).path.Event age:=.ordinary prior ticket post joined
      let more:=(Path.here.ordinary ticket).append post
      have cut:prior.append more=(branch).path :=
        (Path.append_cut_assoc prior (Path.here.ordinary ticket) post).symm.trans joined
      have seen:=held_prefix traces b initial c m limit valid fixed seed earned.advance prior more cut (Or.inr live)
      exact meter age ev live seen (ih more cut)
    | @reset _ age _ _ _ _ _ _ _ _ _ src prior ctl B ih=>
      let ev:(branch).path.Event age:=.reset prior B post joined
      let more:=(Path.here.reset B).append post
      have cut:prior.append more=(branch).path :=
        (Path.append_cut_assoc prior (Path.here.reset B) post).symm.trans joined
      have seen:=held_prefix traces b initial c m limit valid fixed seed earned.advance prior more cut (Or.inr live)
      exact Path.Held.reset B (ih more cut) (meter age ev live seen)
  exact carried (branch).path .here rfl

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
