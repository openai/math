import OAI.Hierarchy.DescentRegisteredWindow
import OAI.Hierarchy.DescentCalendarCapacityStep
import OAI.Hierarchy.DescentOrdinaryPublicDegree
import OAI.Hierarchy.DescentDateArgumentSlots

namespace OAI
/-! # The stored reserve at the output of each actual scheduled instruction -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler DescentPacking.PackedMatch.Local.Stage
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d)

variable {n degree : ℕ} (b : Menu n degree)

set_option quotPrecheck false
local notation "calendar" => capCalendar G.b S.rounds b.gain S.height

omit [Fintype P] in
theorem issued_cap (factors : ∀c,(traces c).path.capFactors=calendar)
    (kinds : ∀c,(traces c).path.kinds=kindCalendar S.rounds S.height)
    (i : ℕ) (e : RunTrace.Events traces i) (a : Position) (move : Move w)
    (issuedAt : issued traces b i e a move) :
    move.next.ports.venue.cap=((calendar).take (i+1)).prod*256 :=by
  obtain ⟨c,e⟩:=e
  have kind:=e.shown
  rw [kinds c] at kind
  cases e with
  | @ordinary _ _ _ _ _ _ src _ _ _ _ dst before t after atDate=>
    obtain ⟨pos,room,rfl⟩:=issuedAt
    have real : ((before.ordinary t).append after).capFactors=calendar :=by rw [atDate];exact factors c
    have slot : ((calendar).drop i).head?=some t.factor:=by simpa only [Nat.sub_zero] using t.factor_at before after calendar real
    have degrees : OrdinaryLink.publicDegree S.rounds G.b (((calendar).drop i).head?.getD 0)=src.placement.degree:=by
      simpa only [Nat.sub_zero] using t.public_degree_at before after calendar real
    change (2^(DescentHostDegree.gainExponent 20 (OrdinaryLink.publicDegree S.rounds G.b
      (((calendar).drop i).head?.getD 0)))*G.b)*(((calendar).take i).prod*256)=_
    rw [degrees,src.branch]
    exact next_cap_product calendar i t.factor slot
  | reset before t after atDate=>
    obtain ⟨cap,room,rfl⟩:=issuedAt
    change 2^b.gain*(((calendar).take i).prod*256)=_
    exact next_cap_product calendar i (2^b.gain) (reset_cap_slot G.b S.rounds b.gain S.height i kind)

omit [Fintype P] in
/-- The original ordinary resolver takes the maximum of the previous and
planned operand counts. The scheduled bound on previous counts makes every
successor use the same declared allocation. -/
theorem issued_arguments (i : ℕ) (e : RunTrace.Events traces i) (a : Position) (move : Move w)
    (old : DatePorts.ArgumentSlots G S a.ports b.drift) (issuedAt : issued traces b i e a move) :
    move.next.ports.argumentsPerNode=S.retainedArgumentsAt G b.drift :=by
  obtain ⟨_,e⟩:=e
  cases e with
  | ordinary before t after eqn=>
    obtain ⟨pos,room,rfl⟩:=issuedAt
    exact max_eq_right old
  | reset before t after eqn=>
    obtain ⟨cap,room,rfl⟩:=issuedAt
    rfl

theorem initial_arguments {cp nP p : ℕ} (X : Catalyst.Approximation F cp nP)
    (R h k tail gain drift degree f quota base field wire hist H groups : ℕ) :
    let l:=DescentDatedSeedStartup.selectedLayout G S h k tail gain p drift degree f quota base field wire hist
    (DatePorts.initial G b.op X R l k H groups h (S.grainAt G.b p 0)).argumentsPerNode=
      3*(S.firstWidth G.b p/p) :=rfl

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
