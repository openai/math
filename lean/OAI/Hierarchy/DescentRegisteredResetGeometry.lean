import OAI.Hierarchy.DescentRegisteredResetSample
import OAI.Hierarchy.DescentRegisteredGeometry
import OAI.Hierarchy.DescentScheduledResetFromPorts
import OAI.Hierarchy.DescentDatePortArchivePitchRoom

namespace OAI
/-! Recover the tariff inputs from the authentic chronology, including the
exact funded-count read expression and original solver address domain. -/
namespace Hierarchy.DescentSixParty.RegisteredReset.Sample
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset Chronology Chronology.RegisterTimeline
open DescentPacking.PackedMatch.Local.Stage NativePitch DescentPrimitivePalette DescentHostDegree
open DescentSIMDLookup ProtocolRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] {G : PoweredGadget F} {n d : ℕ} {board : NonlinearExpanders.Graph n d}
  {op : RotorSpec} {K : Parameters} {τ B h : ℕ} (a : Sample G board op K τ B h)
local notation "J" => Nat.log 2 h/(2*B)
local notation "tb" => tail τ J
local notation "S" => stageNumbers G K.t J K.f K.g K.reset a.copies tb
local notation "k" => groupBits K.t J (hostRate K.t K.reset) (capRate G K.t K.g) (cutRate K.t K.f K.g)
local notation "p" => a.position.ports
local notation "start" => (p).priorStart k a.position.floor
local notation "post" => (p).afterPad k a.position.floor
local notation "s" => (S).firstWidth G.b a.p
local notation "Z" => (S).grainAt G.b a.p 0
local notation "nextM" => incoming S k tb a.p K.f h a.ordinary (a.age+1)

theorem of_cursor (seats profile : ℕ→ℕ) (header : ℕ)
    (cursor : RegisterTimeline.Geometry G S (a.menu seats profile header) k a.w a.age a.position)
    (live : a.age < (S).length) (reset : a.age%((S).rounds+1)=(S).rounds) (degree : atRound K.t=K.degree)
    (limit : a.degreeLimit ≤ K.bound) (input : a.p ≤ h) (ambient : 2^h ≤ a.copies) (ratio : a.w ≤ K.ratio*h)
    (hardware : h ≤ a.w) (degreeWord : (p).venue.degree+1 < 2^a.w)
    (ordinaryAt : ∀i<(S).length,i%((S).rounds+1)≠(S).rounds→(a.ordinary i).payload=h ∧
      (a.ordinary i).unit=(DonorDate.atDate G S K.g k i a.p).amount)
    (next : 0 < nextM) (density : (p).ArchiveDensity ((S).groupCount a.age) h (scale J K.archive) (scale J K.archive))
    (root : 8*a.hardware.inner.successor.groupWidth ≤ h)
    (size : a.hardware.inner.successor.groupWidth ≤ scale J K.receiver) (roof : a.hardware.fullEnd < 2^a.w) :
    a.Geometry :=by
  let cut:=resetCut S k tb a.p K.f h a.age
  let e:=receiverCut G S board k tb a.age a.p K.f K.g K.drift a.degreeLimit h cut nextM op.C op.w
    (p).operandLanes (p).roleLanes (printedBits G s Z op) (p).venue
  have livePitch:=(cursor.format.pitch live)
  have pitch : (p).venue.lanes=2^cut:=by
    simpa only [menu,incoming,ite_eq_left live,ite_eq_left reset] using livePitch
  have before:=a.hardware.stages.1
  have prior:=(cursor.room.header.mono before)
  have postHeader:(post).HeaderRoom a.w start:=
    ⟨prior.count,prior.roster,prior.peers,prior.hubs,prior.hosts⟩
  have entry:=scheduled_port_entry G S board k tb a.age a.p K.f K.g K.drift a.degreeLimit h a.ordinary op
    s Z (p).operandLanes (p).roleLanes post start a.w cursor.room.hosts cursor.format.width a.cap
    cursor.room.population.groups pitch rfl rfl postHeader (cursor.room.wires.mono before) root hardware degreeWord roof
  have solver:=named_prime_room G S board k tb a.age a.p K.f K.g K.drift a.degreeLimit h e cut (2^e) nextM op.C
    op.w (p).operandLanes (p).roleLanes (printedBits G s Z op) (p).venue (p).io start (post).archive.count
    a.w ((S).group_power («k»:=k) (tail:=tb) rfl rfl a.age) entry.low entry.lookup entry.word entry.smooth
    entry.count entry.roster entry.rosterRows entry.ceiling
  have hpos : 0 < h := by
    have sb:=a.hardware.inner.successor.groupWidth_pos
    omega
  have gpos:0 < (S).groupCount a.age:=by rw [←(S).group_power («k»:=k) (tail:=tb) rfl rfl a.age];exact Nat.two_pow_pos _
  have apertures:=density.pitch_room cursor.room.archive hpos gpos
  have deg:(p).venue.degree=K.degree:=(cursor.degree.trans (congrArg atRound reset)).trans degree
  exact ⟨live,reset,input,ambient,ratio,deg,limit,cursor.room.hosts,cursor.room.population.groups,cursor.format.width,
    cursor.format.paid,livePitch,ordinaryAt,apertures.operandPos,apertures.rolePos,
    (by rw [pitch];exact Nat.two_pow_pos _),next,cursor.room.archive,cursor.room.args,density,
    fun x=>by rw [cursor.room.paid.issued.row];exact le_rfl,entry.lookup,root,size,roof,solver⟩

/-- Serialize the actual historical reset source, including its original capacity.
The leading and trailing pieces are the two pieces of the named path at the cut. -/
def reached_of_path {P : Type} {d₀ : ℕ} {bits : P→ℕ} {W W₀ W₁ : MarkedWorld F d₀ P bits}
    {q ε : ℝ} {z D₀ D₁ z₀ z₁ age₁ wire hist D : ℕ}
    {first : Reached W₀ G q ε S k 0 z₀ D₀ wire hist}
    (r : Reached W G q ε S k a.age z D wire hist)
    {last : Reached W₁ G q ε S k age₁ z₁ D₁ wire hist}
    (before : Chronology.Path first r) (after : Chronology.Path r last)
    (deg : D=K.degree) (seed : first.placement.cap=256)
    (bought : (before.append after).capFactors=capCalendar G.b K.t K.g J) :
    a.ReachedAt :=by
  subst D
  refine ⟨P,d₀,bits,W,q,ε,z,wire,hist,r,?_⟩
  simpa only [Nat.sub_zero,seed] using before.capacity_prefix after _ bought

end
end Hierarchy.DescentSixParty.RegisteredReset.Sample

end OAI
