import OAI.Hierarchy.DescentRegisteredWindow

namespace OAI
/-! # The public register at each prefix of a selected arithmetic descent -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : DescentCompiler.AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ}

namespace Path
variable {I A B V : MarkedWorld F d P bits} {j₀ z₀ D₀ j₁ z₁ D₁ j₂ z₂ D₂ j₃ z₃ D₃ : ℕ}
  {first : Reached I G q ε S k j₀ z₀ D₀ wire hist} {one : Reached A G q ε S k j₁ z₁ D₁ wire hist}
  {two : Reached B G q ε S k j₂ z₂ D₂ wire hist} {last : Reached V G q ε S k j₃ z₃ D₃ wire hist}

omit [Fintype P] in
theorem append_cut_assoc (a : Path first one) (b : Path one two) (c : Path two last) :
    (a.append b).append c=a.append (b.append c) :=by
  induction c with
  | here=>rfl
  | ordinary prev tick ih=>exact congrArg (fun p : Path first _=>p.ordinary tick) ih
  | reset prev closed ih=>exact congrArg (fun p : Path first _=>p.reset closed) ih

end Path

namespace Path.Event
variable {t : RunTrace G q ε S k wire hist final bits d} {i : ℕ}
def incoming (e : t.path.Event i) (p : RegisterTimeline.Position) (m : Memory w) : Prop :=by
  cases e with
  | @ordinary _ _ _ _ _ _ src _ _ _ _ dst before tick after eqn=>exact p.ports.held src p.floor m
  | @reset _ _ _ _ _ _ _ _ _ _ src _ before b after eqn=>exact p.ports.held src p.floor m

def outgoing (e : t.path.Event i) (p : RegisterTimeline.Position) (m : Memory w) : Prop :=by
  cases e with
  | @ordinary _ _ _ _ _ _ src _ _ _ _ dst before tick after eqn=>exact p.ports.held dst p.floor m
  | reset before b after eqn=>exact p.ports.held b.next p.floor m

def required (e : t.path.Event i) (limit : ℕ) (valid : Prop) : Prop :=by
  cases e with
  | ordinary before tick after eqn=>exact before.selections.length+1 < limit ∨ valid
  | reset before b after eqn=>exact before.selections.length < limit ∨ valid
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
variable (limit : ℕ) (valid : Prop)

/-- A physical proof at one actual event. The successor's register receives the passed
host count and the full previous bank of signed and paid inputs on one reached memory. -/
def advances (i : ℕ) (e : (t).path.Event i) : Prop :=
  e.incoming (cursor i) (ram i) → e.required limit valid →
    ∃move : Move w, steps i ⟨c,e⟩ (cursor i) move ∧
      ∃out,move.code.Runs (ram i) out ∧ e.outgoing move.next out

variable (fixed : ∀i (a z : RunTrace.Events traces i) (x y : Move w),
    issued traces b i a (calendar (w:=w) traces b initial i) x →
    issued traces b i z (calendar (w:=w) traces b initial i) y → x=y)
variable (first : initial.ports.held (traces c).first initial.floor mem)
variable (runs : ∀i (e : (traces c).path.Event i), advances traces b initial c mem limit valid i e)

include fixed runs in
omit [Fintype P] in
theorem actual_transition (i : ℕ) (e : (t).path.Event i) (prior : e.incoming (cursor i) (ram i))
    (needed : e.required limit valid) : e.outgoing (cursor (i+1)) (ram (i+1)) :=by
  obtain ⟨move,hit,out,native,seen⟩:=runs i e prior needed
  obtain ⟨op,next⟩:=returned traces b initial i ⟨c,e⟩ move hit (fun d x got=>fixed i d _ x move got hit)
  rw [next]
  apply DateCode.history_event
  exact ⟨out,op.symm ▸ native,seen⟩

include fixed first runs in
omit [Fintype P] in
theorem held_prefix {U : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    (p : Path (t).first r) (suffix : Path r (t).last) (joined : p.append suffix=(t).path)
    (live : p.selections.length < limit ∨ valid) : (cursor i).ports.held r (cursor i).floor (ram i) :=by
  induction p with
  | here=>exact first
  | @ordinary _ age _ _ _ _ src prev _ he T ballot norm dst tick ih=>
    have next : prev.selections.length+1 < limit ∨ valid:=by
      simpa only [Path.selections,List.length_append,List.length_singleton] using live
    have prior:=ih ((Path.here.ordinary tick).append suffix)
      ((Path.append_cut_assoc prev (Path.here.ordinary tick) suffix).symm.trans joined)
      (next.imp_left (fun h=>(Nat.lt_succ_self _).trans h))
    let e : (t).path.Event age:=.ordinary prev tick suffix joined
    exact actual_transition traces b initial c mem limit valid fixed runs age e prior next
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl closed ih=>
    have prior:=ih ((Path.here.reset closed).append suffix)
      ((Path.append_cut_assoc prev (Path.here.reset closed) suffix).symm.trans joined) live
    let e : (t).path.Event age:=.reset prev closed suffix joined
    exact actual_transition traces b initial c mem limit valid fixed runs age e prior live

include fixed first runs in
omit [Fintype P] in
theorem held_floor {U : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    (p : Path (t).first r) (suffix : Path r (t).last) (joined : p.append suffix=(t).path)
    (live : p.selections.length < limit ∨ valid) :
    (cursor i).ports.held r (DescentDatedAddressBook.floor initial.floor (span steps initial) i) (ram i) ∧
      Fintype.card r.V≤(cursor i).ports.venue.hosts :=by
  have h:=held_prefix traces b initial c mem limit valid fixed first runs p suffix joined live
  exact ⟨by rwa [←position_floor steps initial i],h.choose⟩

end RegisterTimeline
end
end Hierarchy.DescentSixParty.Chronology

end OAI
