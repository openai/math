import OAI.Hierarchy.DescentRegisteredResetFits
import OAI.Hierarchy.DescentRegisteredProfileMenu
import OAI.Hierarchy.DescentScheduledResetDegrees

namespace OAI
/-! Widths of the calendar receiver on each actually carried input register. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentDatedAddressBook DescentDatedAddressBook.PhysicalReset DescentCompiler
open DescentCompiler.TerminalScale DescentPacking.PackedMatch.Local.Stage
open DescentTerminalEpochChart ProtocolRAM Filter Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n degree : ℕ}
  (board : NonlinearExpanders.Graph n degree) (op : RotorSpec) (t f g reset τ drift bound B h : ℕ)
local notation "J" => Nat.log 2 h / (2*B)
local notation "tb" => tail τ J
local notation "sched" sites:arg => stageNumbers G t J f g reset sites tb
local notation "cell" => groupBits t J (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "topDegree" => maximumDegree (t+1)
local notation "exponent" => degreeRate G board op t f g reset topDegree

structure ReceiverCalendar : Prop where
  degreeWord : ∀ w : ℕ, h ≤ w → topDegree+1 < 2^w
  measured : ∀ (sites i p q : ℕ) (b : Menu n degree) (old : DatePorts),
    b.board=board → b.op=op → b.gain=g → b.tail=tb → b.p=p → b.f=f → b.drift=drift →
    b.degreeLimit=q → b.payload=h → p ≤ h → q ≤ bound → old.venue.degree ≤ topDegree →
    old.venue.cap=((capCalendar G.b t g J).take i).prod*256 → old.venue.paidBits=(sched sites).censusBits p →
    8*b.receiverWidth G (sched sites) cell i old ≤ h ∧
      b.receiverWidth G (sched sites) cell i old ≤ scale J exponent

theorem receiver_calendar (den : 0 < B) (paid : 2*exponent ≤ B) (branch : G.b ≤ 2^(capRate G t g)) :
    ∀ᶠ h : ℕ in atTop, ReceiverCalendar G board op t f g reset τ drift bound B h := by
  have rate (D : Fin (topDegree+1)) : ResetOutput.receiverRate G board op t f g reset D.val ≤ exponent :=
    Finset.le_sup (f := fun j : Fin (topDegree+1) => ResetOutput.receiverRate G board op t f g reset j.val)
      (Finset.mem_univ D)
  filter_upwards [Filter.eventually_all.mpr (fun D : Fin (topDegree+1) =>
    scheduled_short G board op t f g reset τ D.val drift B den
      ((Nat.mul_le_mul_left 2 (rate D)).trans paid) branch bound),
    Filter.eventually_all.mpr (fun D : Fin (topDegree+1) =>
      scheduled_scale G board op t f g reset τ D.val drift B den branch bound),
    eventually_ge_atTop (topDegree+1)] with h short small degreeBound
  refine ⟨fun w hw => (degreeBound.trans hw).trans_lt Nat.lt_two_pow_self, ?_⟩
  intro sites i p q b old rotor spec gain tailAt precision fieldWidth wander degreeAt payload input coeff degreeRoom cap paidBits
  cases b with
  | mk board' op' g' tail' p' f' drift' q' h' seats ordinary profile header =>
    dsimp only at rotor spec gain tailAt precision fieldWidth wander degreeAt payload
    subst board'; subst op'; subst g'; subst tail'; subst p'; subst f'; subst drift'; subst q'; subst h'
    let D : Fin (topDegree+1) := ⟨old.venue.degree, Nat.lt_succ_of_le degreeRoom⟩
    have lo := short D sites i p q ordinary old.venue old.operandLanes old.roleLanes 0
      old.io.wire old.io.roster input coeff rfl cap paidBits
    have hi := small D sites i p q ordinary old.venue old.operandLanes old.roleLanes 0
      old.io.wire old.io.roster input coeff rfl cap paidBits
    let height := Nat.log 2 h / (2*B)
    let tailSize := tail τ height
    let schedule₀ := stageNumbers G t height f g reset sites tailSize
    let cell₀ := groupBits t height (hostRate t reset) (capRate G t g) (cutRate t f g)
    let menu₀ : Menu n degree := ⟨board,op,g,tailSize,p,f,drift,q,h,seats,ordinary,profile,header⟩
    have measuredWidth := menu₀.receiverWidth_at G schedule₀ cell₀ i old 0
    exact ⟨(Nat.mul_le_mul_left 8 measuredWidth.ge).trans lo,
      measuredWidth.ge.trans (hi.trans (Nat.pow_le_pow_right (by decide : 0 < (2:ℕ))
        (Nat.mul_le_mul_right _ (rate D))))⟩


variable {A P : Type} [Fintype P] {d wire hist final w : ℕ} {bits : P → ℕ} {charge ε : ℝ} {C : Type*}
  (sites p q lo header : ℕ) (shelves : List (Source A))
local notation "b" => fromProfiles G (sched sites) board op cell tb p f g drift q h lo header shelves
variable (traces : C → RunTrace G charge ε (stageNumbers G t (Nat.log 2 h / (2*B)) f g reset sites (tail τ (Nat.log 2 h / (2*B)))) (groupBits t (Nat.log 2 h / (2*B)) (hostRate t reset) (capRate G t g) (cutRate t f g)) wire hist final bits d)
  (initial : Position)
local notation "cursor" => calendar (w:=w) traces b initial

/-- The recorded degree, paid precision and capacity suffice at any registered position. -/
theorem receiver_on_position (grant : ReceiverCalendar G board op t f g reset τ drift bound B h)
    (input : p ≤ h) (coeff : q ≤ bound) (i : ℕ) (pos : Position)
    (geometry : Geometry G (sched sites) b cell w i pos) :
    8*(b).receiverWidth G (sched sites) cell i pos.ports ≤ h ∧
      (b).receiverWidth G (sched sites) cell i pos.ports ≤ scale J exponent := by
  exact grant.measured sites i p q b pos.ports rfl rfl rfl rfl rfl rfl rfl rfl rfl
    input coeff (geometry.degree.le.trans (round_degree_le t i)) geometry.capacity geometry.format.paid

omit [Fintype P] in
theorem receiver_on_calendar (grant : ReceiverCalendar G board op t f g reset τ drift bound B h)
    (tags : ∀ c, (traces c).path.kinds=kindCalendar t J)
    (seed : initial.ports.venue.degree=3) (input : p ≤ h) (coeff : q ≤ bound)
    (i : ℕ) (geometry : Geometry G (sched sites) b cell w i (cursor i)) :
    8*(b).receiverWidth G (sched sites) cell i (cursor i).ports ≤ h ∧
      (b).receiverWidth G (sched sites) cell i (cursor i).ports ≤ scale J exponent := by
  have first : initial.ports.venue.degree ≤ topDegree := by
    simpa only [seed, Nat.zero_mod, atRound] using round_degree_le t 0
  have degreeAt := calendar_degree_le (w:=w) traces b tags initial first i
  exact grant.measured sites i p q b (cursor i).ports rfl rfl rfl rfl rfl rfl rfl rfl rfl
    input coeff degreeAt geometry.capacity geometry.format.paid

local notation "outer" age:arg => scheduledAtPorts G (sched sites) board cell tb age p f g drift q h
  (b).ordinary op ((sched sites).firstWidth G.b p) ((sched sites).grainAt G.b p 0)
  (cursor age).ports (cursor age).floor

omit [Fintype P] in
/-- All local admission bounds use only the incoming position. -/
theorem reset_fits_on_position (grant : ReceiverCalendar G board op t f g reset τ drift bound B h)
    (tags : ∀ c, (traces c).path.kinds=kindCalendar t J)
    (input : p ≤ h) (coeff : q ≤ bound) (bus : h ≤ w)
    (i : ℕ) (e : RunTrace.Events traces i) (resetAt : e.2.isReset=true)
    (top : Geometry G (sched sites) b cell w i (cursor i) → (outer i).fullEnd < 2^w) :
    fitsAt traces b initial (w:=w) i e := by
  intro geom
  have width:=receiver_on_position G board op t f g reset τ drift bound B h sites p q lo header shelves
    grant input coeff i (cursor i) geom
  exact reset_fitsAt traces b initial tags i e resetAt width.1 bus
    (fun step => (Nat.succ_le_succ (step.degree.le.trans (round_degree_le t i))).trans_lt
      (grant.degreeWord w bus)) (top geom) geom

omit [Fintype P] in
/-- The receiver width and the degree sentinel both fit the actual registered reset. -/
theorem reset_fits_receiver (grant : ReceiverCalendar G board op t f g reset τ drift bound B h)
    (tags : ∀ c, (traces c).path.kinds=kindCalendar t J)
    (seed : initial.ports.venue.degree=3) (input : p ≤ h) (coeff : q ≤ bound) (bus : h ≤ w)
    (i : ℕ) (e : RunTrace.Events traces i) (resetAt : e.2.isReset=true)
    (top : Geometry G (sched sites) b cell w i (cursor i) → (outer i).fullEnd < 2^w) :
    fitsAt traces b initial (w:=w) i e := by
  intro geom
  have width := receiver_on_calendar G board op t f g reset τ drift bound B h sites p q lo header shelves
    traces initial grant tags seed input coeff i geom
  exact reset_fits traces b initial tags i e resetAt width.1 bus seed (grant.degreeWord w bus) (top geom) geom

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
