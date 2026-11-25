import OAI.Hierarchy.DescentRegisterCutInduction
import OAI.Hierarchy.DescentChronologicalFinalEvent

namespace OAI
/-! # The public register and physical instruction at the final issued reset -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F P : Type} [Field F] [Fintype P] {d k wire hist len : ℕ} {bits : P→ℕ}
  {G : PoweredGadget F} {S : AtomSchedule} {q ε : ℝ}
  {t : RunTrace G q ε S k wire hist len bits d}

omit [Fintype P] in
/-- Extract an original named event from the chronological prefix of a full trace. -/
theorem RunTrace.cut_in_prefix {U : MarkedWorld F d P bits} {i z D : ℕ}
    {r : Reached U G q ε S k i z D wire hist} (p : Path t.first r)
    (after_ : Path r t.last) (eqn : p.append after_=t.path) (j : ℕ) (prior:j< i) :
    Nonempty (t.path.Event j) :=by
  induction p with
  | here=>omega
  | @ordinary _ age _ _ _ _ src prev _ he T choice norm dst tick ih=>
    by_cases last : j=age
    · subst j
      exact ⟨.ordinary prev tick after_ eqn⟩
    · exact ih ((Path.here.ordinary tick).append after_)
        ((Path.append_cut_assoc prev (Path.here.ordinary tick) after_).symm.trans eqn) (by omega)
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl closed ih=>
    by_cases last : j=age
    · subst j
      exact ⟨.reset prev closed after_ eqn⟩
    · exact ih ((Path.here.reset closed).append after_)
        ((Path.append_cut_assoc prev (Path.here.reset closed) after_).symm.trans eqn) (by omega)

namespace RegisterTimeline
variable {C : Type*} {w n degree : ℕ} (traces : C→RunTrace G q ε S k wire hist len bits d)
  (b : Menu n degree) (initial : Position) (c : C)
local notation "t" => traces c
local notation "cursor" => calendar (w:=w) traces b initial
local notation "codes" => instruction (w:=w) traces b initial
local notation "steps" => issued (w:=w) traces b
local notation "family" => RunTrace.machine traces (fun i _=>codes i)

include c in
omit [Fintype P] in
/-- Replacing the shared instruction by its finite-choice presentation leaves
the history of every reached date exactly the same, including its scratch cells. -/
theorem history_from_cuts (mem:Memory w) (i:ℕ) (hi:i≤len) :
    DateCode.history family mem i=DateCode.history codes mem i :=by
  induction i with
  | zero=>rfl
  | succ i ih=>
    have earlier:i<len:=by omega
    obtain ⟨e⟩:=(t).cut_in_prefix (t).path .here rfl i earlier
    have dateEq : family i=codes i:=RunTrace.on_branch traces (fun i _=>codes i)
      (fun _ _ _=>rfl) c i e
    simp only [DateCode.history,dateEq,ih (Nat.le_of_lt earlier)]

omit [Fintype P] in
/-- The registered reset's actual predecessor, authentic return register and
instruction coincide with the last cut of this particular paid path. -/
theorem final_move {p : ℕ} (end_ : Path.FinalReset p (t).path)
    (fixed : ∀i (a z : RunTrace.Events traces i) x y,
      steps i a (cursor i) x → steps i z (cursor i) y → x=y)
    (present : ∃m,steps (len-1) ⟨c,end_.event⟩ (cursor (len-1)) m) :
    let i:=len-1
    let a:=cursor i
    ∃cap room,
      let move:=resetMove (G:=G) (S:=S) b k i w a cap room
      codes i=move.code ∧ family i=move.code ∧ cursor len=move.next :=by
  let i:=len-1
  let a:=cursor i
  let e : RunTrace.Events traces i:=⟨c,end_.event⟩
  obtain ⟨m,hit⟩:=present
  have confirmed:=(returned traces b initial i e m hit (fun x z got=>fixed i x e z m got hit))
  have lastCode : family i=codes i:=RunTrace.on_branch traces (fun i _=>codes i) (fun _ _ _=>rfl) c i end_.event
  have resetCase (ev : RunTrace.Events traces i) (kind : ev.2.isReset=true) (selected : steps i ev a m) :
      ∃cap room,m=resetMove (G:=G) (S:=S) b k i w a cap room :=by
    rcases ev with ⟨ballot,event⟩
    cases event with
    | ordinary prior ticket suffix path=>cases kind
    | reset prior B suffix path=>exact selected
  obtain ⟨cap,space,move⟩:=resetCase e end_.is_reset hit
  refine ⟨cap,space,confirmed.1.trans (congrArg Move.code move),
    lastCode.trans (confirmed.1.trans (congrArg Move.code move)),?_⟩
  exact (congrArg (fun j => cursor j) end_.succ_age).symm.trans
    (confirmed.2.trans (congrArg Move.next move))

end RegisterTimeline
end
end Hierarchy.DescentSixParty.Chronology

end OAI
