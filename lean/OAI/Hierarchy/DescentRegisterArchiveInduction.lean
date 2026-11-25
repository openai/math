import OAI.Hierarchy.DescentRegisterCutInduction
import OAI.Hierarchy.DescentRegisterPrefixClaim

namespace OAI
/-! # Carrying the complete native archive on the same memory as its stage register -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ}


namespace Path.Event
variable {t : RunTrace G q ε S k wire hist final bits d} {i : ℕ}

def previousClaim (claim : RegisterTimeline.PrefixClaim t w) (e : t.path.Event i)
    (pos : RegisterTimeline.Position) (m : Memory w) : Prop :=by
  cases e with
  | ordinary before tick after eqn=>exact claim before pos m
  | reset before b after eqn=>exact claim before pos m

def nextClaim (claim : RegisterTimeline.PrefixClaim t w) (e : t.path.Event i)
    (pos : RegisterTimeline.Position) (m : Memory w) : Prop :=by
  cases e with
  | ordinary before tick after eqn=>exact claim (before.ordinary tick) pos m
  | reset before b after eqn=>exact claim (before.reset b) pos m
end Path.Event
namespace RegisterTimeline
variable {C : Type*} (traces : C→RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position)
local notation "steps" => issued (w:=w) traces b
local notation "cursor" => calendar (w:=w) traces b initial
local notation "code" => instruction (w:=w) traces b initial
variable (c : C) (mem : Memory w)
local notation "t" => traces c
local notation "ram" => DateCode.history code mem
variable (limit : ℕ) (valid : Prop) (claim : PrefixClaim (traces c) w)

/-- A physical proof at one actual event. The successor's register receives the passed
host count and the full previous bank of signed and paid inputs on one reached memory. -/
def advancesArchive (i : ℕ) (e : (t).path.Event i) : Prop :=
  e.incoming (cursor i) (ram i) → e.previousClaim claim (cursor i) (ram i) → e.required limit valid →
    ∃move : Move w, steps i ⟨c,e⟩ (cursor i) move ∧
      ∃out,move.code.Runs (ram i) out ∧ e.outgoing move.next out ∧ e.nextClaim claim move.next out

variable (fixed : ∀i (a z : RunTrace.Events traces i) (x y : Move w),
    issued traces b i a (calendar (w:=w) traces b initial i) x →
    issued traces b i z (calendar (w:=w) traces b initial i) y → x=y)
variable (first : initial.ports.held (traces c).first initial.floor mem ∧ claim Path.here initial mem)
variable (runs : ∀i (e : (traces c).path.Event i), advancesArchive traces b initial c mem limit valid claim i e)

include fixed runs in
omit [Fintype P] in
theorem actual_archive_transition (i : ℕ) (e : (t).path.Event i) (prior : e.incoming (cursor i) (ram i) ∧ e.previousClaim claim (cursor i) (ram i))
    (needed : e.required limit valid) : e.outgoing (cursor (i+1)) (ram (i+1)) ∧ e.nextClaim claim (cursor (i+1)) (ram (i+1)) :=by
  obtain ⟨move,hit,out,native,seen⟩:=runs i e prior.1 prior.2 needed
  obtain ⟨op,next⟩:=returned traces b initial i ⟨c,e⟩ move hit (fun d x got=>fixed i d _ x move got hit)
  rw [next]
  apply DateCode.history_event code mem i (Q := fun m => e.outgoing move.next m ∧ e.nextClaim claim move.next m)
  exact ⟨out,op.symm ▸ native,seen⟩

include fixed first runs in
omit [Fintype P] in
theorem held_archive_prefix {U : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    (p : Path (t).first r) (suffix : Path r (t).last) (joined : p.append suffix=(t).path)
    (live : p.selections.length < limit ∨ valid) : (cursor i).ports.held r (cursor i).floor (ram i) ∧ claim p (cursor i) (ram i) :=by
  induction p with
  | here=>exact first
  | @ordinary _ age _ _ _ _ src prev _ he T ballot norm dst tick ih=>
    have next : prev.selections.length+1 < limit ∨ valid:=by
      simpa only [Path.selections,List.length_append,List.length_singleton] using live
    have prior:=ih ((Path.here.ordinary tick).append suffix)
      ((Path.append_cut_assoc prev (Path.here.ordinary tick) suffix).symm.trans joined)
      (next.imp_left (fun h=>(Nat.lt_succ_self _).trans h))
    let e : (t).path.Event age:=.ordinary prev tick suffix joined
    exact actual_archive_transition traces b initial c mem limit valid claim fixed runs age e prior next
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl closed ih=>
    have prior:=ih ((Path.here.reset closed).append suffix)
      ((Path.append_cut_assoc prev (Path.here.reset closed) suffix).symm.trans joined) live
    let e : (t).path.Event age:=.reset prev closed suffix joined
    exact actual_archive_transition traces b initial c mem limit valid claim fixed runs age e prior live

end RegisterTimeline
end
end Hierarchy.DescentSixParty.Chronology

end OAI
