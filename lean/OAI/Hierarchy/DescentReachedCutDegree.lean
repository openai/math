import OAI.Hierarchy.DescentDatedBranchEvents
import OAI.Hierarchy.DescentOrdinarySlotDegree

namespace OAI
/-! The degree belongs to the reached object named by the cut. Its index starts
at three, changes with each ordinary link, and returns to three at a reset. -/
namespace Hierarchy.DescentSixParty.Chronology.RunTrace
open DescentCompiler DescentHostDegree
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final : ℕ} {q ε : ℝ}
    (t : RunTrace G q ε S k wire hist final bits d)
    (seed : t.firstDegree=3) (kinds : t.path.kinds=kindCalendar S.rounds S.height)

omit [Fintype P] in
private theorem append_assoc {I A B V : MarkedWorld F d P bits}
    {j₀ z₀ D₀ j₁ z₁ D₁ j₂ z₂ D₂ j₃ z₃ D₃ : ℕ}
    {first : Reached I G q ε S k j₀ z₀ D₀ wire hist} {one : Reached A G q ε S k j₁ z₁ D₁ wire hist}
    {two : Reached B G q ε S k j₂ z₂ D₂ wire hist} {last : Reached V G q ε S k j₃ z₃ D₃ wire hist}
    (a : Path first one) (b : Path one two) (c : Path two last) :
    (a.append b).append c = a.append (b.append c) := by
  induction c with
  | here => rfl
  | ordinary prev tick ih => exact congrArg (fun p : Path first _ => p.ordinary tick) ih
  | reset prev closed ih => exact congrArg (fun p : Path first _ => p.reset closed) ih

include seed kinds in
omit [Fintype P] in
theorem degree_before {U : MarkedWorld F d P bits} {age z D : ℕ}
    {r : Reached U G q ε S k age z D wire hist} (before : Path t.first r)
    (after : Path r t.last) (cut : before.append after=t.path) :
    D=atRound (age%(S.rounds+1)) :=by
  induction before with
  | here=>simpa only [Nat.zero_mod,atRound] using seed
  | @ordinary _ i _ _ _ _ src prev _ he T ballot norm dst link ih=>
    have joined:prev.append ((Path.here.ordinary link).append after)=t.path:=
      (append_assoc prev (Path.here.ordinary link) after).symm.trans cut
    have stamp:=link.kind_on_cut prev after cut kinds
    have next:=(ordinary_slot_degree 1 S.rounds 0 S.height i (by decide) stamp).2
    rw [next,atRound,link.nextDegree,ih _ joined]
  | @reset _ i _ _ _ _ _ _ _ _ _ src prev ctl closed ih=>
    have stamp:=reset_kind_on_cut closed prev after cut kinds
    exact (congrArg atRound (reset_slot_successor S.rounds S.height i stamp)).symm

end
end Hierarchy.DescentSixParty.Chronology.RunTrace

end OAI
