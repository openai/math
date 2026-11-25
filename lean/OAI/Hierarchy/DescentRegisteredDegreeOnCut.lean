import OAI.Hierarchy.DescentRegisteredVenueDegree

namespace OAI
/-! At a numbered cut the currently carried degree uses only strictly earlier placements. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler DescentDatedAddressBook Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree) (initial : Position)
local notation "cursor" => calendar (w:=w) traces b initial
local notation "steps" => issued (w:=w) traces b
local notation "geo" i:arg => Geometry G S b k w i (cursor i)
variable (tags : ∀c,(traces c).path.kinds=kindCalendar S.rounds S.height)
    (seedDegree : initial.ports.venue.degree=3) (c : C)
local notation "trace" => traces c

include tags seedDegree in
omit [Fintype P] in
/-- The minimal degree receipt, valid even before the current move has been placed. -/
theorem degree_on_cut {U : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    (before : Path (trace).first r) (tail : Path r (trace).last) (cut : before.append tail=(trace).path)
    (previous : ∀j < i,∀e:RunTrace.Events traces j,∃m,steps j e (cursor j) m) :
    (cursor i).ports.venue.degree=atRound (i%(S.rounds+1)):=by
  cases before with
  | here=>change initial.ports.venue.degree=atRound (0 % (S.rounds+1)); simpa only [Nat.zero_mod,atRound] using seedDegree
  | @ordinary _ age _ _ _ _ src prev _ he T ballot norm dst ticket=>
    let e : RunTrace.Events traces age:=⟨c,.ordinary prev ticket tail cut⟩
    obtain ⟨m,hit⟩:=previous age (Nat.lt_succ_self age) e
    exact degree_after_issue traces b tags initial age e m hit
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl closed=>
    let e : RunTrace.Events traces age:=⟨c,.reset prev closed tail cut⟩
    obtain ⟨m,hit⟩:=previous age (Nat.lt_succ_self age) e
    exact degree_after_issue traces b tags initial age e m hit

variable (fixed : ∀i (a z : RunTrace.Events traces i) x y,
  issued (w:=w) traces b i a (calendar (w:=w) traces b initial i) x→
  issued (w:=w) traces b i z (calendar (w:=w) traces b initial i) y→x=y)
variable (caps : ∀c,(traces c).path.capFactors=capCalendar G.b S.rounds b.gain S.height)
variable (seed : Geometry G S b k w 0 initial)

include tags fixed caps in
omit [Fintype P] in
private theorem next_of_current (age : ℕ) (e : RunTrace.Events traces age) (prior : geo age)
    (fit : fitsAt traces b initial (w:=w) age e) :
    geo (age+1) ∧ (cursor (age+1)).ports.venue.degree=atRound ((age+1)%(S.rounds+1)):=by
  obtain ⟨m,hit,roof,short⟩:=fit prior
  refine ⟨?_,degree_after_issue traces b tags initial age e m hit⟩
  have n:=(returned traces b initial age e m hit (fun j t hj=>fixed age j e t m hj hit)).2
  rw [n]
  exact ⟨output_archive traces b age e _ m hit prior.format,
    issued_register_room traces b age e _ m hit prior.room roof short,
    step_venue_format traces b age e _ m hit prior.format,
    by simpa only [Nat.succ_ne_zero,ite_false] using issued_arguments traces b age e _ m prior.room.args hit,
    issued_degree traces b tags age e _ m hit, issued_cap traces b caps tags age e _ m hit⟩

include tags seedDegree fixed caps seed in
omit [Fintype P] in
theorem geometry_degree_on_fitted_cut {U : MarkedWorld F d P bits} {i z D : ℕ}
    {r : Reached U G q ε S k i z D wire hist}
    (path : Path (trace).first r) (tail : Path r (trace).last) (cut : path.append tail=(trace).path)
    (previous : ∀j < i,∀e:RunTrace.Events traces j,fitsAt traces b initial (w:=w) j e) :
    geo i ∧ (cursor i).ports.venue.degree=atRound (i%(S.rounds+1)):=by
  induction path with
  | here => exact ⟨seed,by change initial.ports.venue.degree=atRound (0 % (S.rounds+1)); simpa only [Nat.zero_mod,atRound] using seedDegree⟩
  | @ordinary _ age _ _ _ _ src prev _ he T ballot norm dst link ih=>
    let e : RunTrace.Events traces age:=⟨c,.ordinary prev link tail cut⟩
    have old:=ih ((Path.here.ordinary link).append tail)
      ((Path.append_cut_assoc prev (Path.here.ordinary link) tail).symm.trans cut)
      (fun j hj=>previous j (Nat.lt_succ_of_lt hj))
    exact next_of_current traces b initial tags fixed caps age e old.1 (previous age (Nat.lt_succ_self age) e)
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl closed ih=>
    let e : RunTrace.Events traces age:=⟨c,.reset prev closed tail cut⟩
    have old:=ih ((Path.here.reset closed).append tail)
      ((Path.append_cut_assoc prev (Path.here.reset closed) tail).symm.trans cut)
      (fun j hj=>previous j (Nat.lt_succ_of_lt hj))
    exact next_of_current traces b initial tags fixed caps age e old.1 (previous age (Nat.lt_succ_self age) e)

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
