import OAI.Hierarchy.DescentRegisteredGeometry
import OAI.Hierarchy.DescentRegisteredDegreeStep

namespace OAI
/-! The degree stored by the chosen physical date registers. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
open scoped BigOperators Classical
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P → ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C → RunTrace G q ε S k wire hist final bits d)
    {n degree : ℕ} (b : Menu n degree)
variable (tags : ∀ c, (traces c).path.kinds = kindCalendar S.rounds S.height)

variable (initial : Position)
local notation "cursor" => calendar (w:=w) traces b initial
local notation "steps" => issued (w:=w) traces b

include tags in
omit [Fintype P] in
/-- This inequality can be used to establish room for a date before selecting its move. -/
theorem calendar_degree_le (seed : initial.ports.venue.degree ≤ maximumDegree (S.rounds+1)) (i : ℕ) :
    (cursor i).ports.venue.degree ≤ maximumDegree (S.rounds+1) := by
  induction i with
  | zero => exact seed
  | succ i ih =>
    change (selected steps i (cursor i)).next.ports.venue.degree ≤ _
    unfold selected
    split
    · rename_i found
      obtain ⟨e, posted⟩ := found.choose_spec.1
      rw [issued_degree traces b tags i e _ found.choose posted]
      exact round_degree_le S.rounds (i+1)
    · exact ih

include tags in
omit [Fintype P] in
theorem calendar_degree_room (seed : initial.ports.venue.degree = 3)
    (word : maximumDegree (S.rounds+1)+1 < 2^w) (i : ℕ) :
    (cursor i).ports.venue.degree+1 < 2^w := by
  have first : initial.ports.venue.degree ≤ maximumDegree (S.rounds+1) := by
    simpa only [seed, Nat.zero_mod, atRound] using round_degree_le S.rounds 0
  exact (Nat.succ_le_succ (calendar_degree_le traces b tags initial first i)).trans_lt word

include tags in
omit [Fintype P] in
theorem degree_after_issue (i : ℕ) (e : RunTrace.Events traces i) (m : Move w)
    (posted : steps i e (cursor i) m) :
    (cursor (i+1)).ports.venue.degree = atRound ((i+1) % (S.rounds+1)) := by
  change (selected steps i (cursor i)).next.ports.venue.degree = _
  unfold selected
  split
  · rename_i found
    obtain ⟨j, chosen⟩ := found.choose_spec.1
    exact issued_degree traces b tags i j _ found.choose chosen
  · rename_i absent
    exact (absent ⟨m, ⟨e, posted⟩, forward traces b i e _ m posted⟩).elim

variable (fixed : ∀ i (a z : RunTrace.Events traces i) x y,
  issued (w:=w) traces b i a (calendar (w:=w) traces b initial i) x →
    issued (w:=w) traces b i z (calendar (w:=w) traces b initial i) y → x=y)
variable (caps : ∀ c, (traces c).path.capFactors = capCalendar G.b S.rounds b.gain S.height)
variable (seed : Geometry G S b k w 0 initial)
    (placed : ∀ i (e : RunTrace.Events traces i), fitsAt traces b initial (w:=w) i e)
    (seedDegree : initial.ports.venue.degree=3) (c : C)
local notation "t" => traces c

include fixed caps tags seed placed seedDegree in
omit seedDegree [Fintype P] in
theorem degree_prefix {U : MarkedWorld F d P bits} {i z D : ℕ} {r : Reached U G q ε S k i z D wire hist}
    (p : Path (t).first r) (suffix : Path r (t).last) (joined : p.append suffix=(t).path) :
    (cursor i).ports.venue.degree = atRound (i % (S.rounds+1)) :=
  (geometry_prefix traces b initial fixed caps tags seed placed c p suffix joined).degree

include fixed caps tags seed placed seedDegree in
omit seedDegree [Fintype P] in
theorem degree_at_reset (i : ℕ) (e : (t).path.Event i) (isReset : e.isReset=true) :
    (cursor i).ports.venue.degree = atRound S.rounds := by
  have since := e.shown
  rw [tags c, isReset] at since
  have slot := reset_slot_index S.rounds S.height i since
  exact (geometry_on_event traces b initial fixed caps tags seed placed c i e).degree.trans
    (congrArg atRound slot)

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
