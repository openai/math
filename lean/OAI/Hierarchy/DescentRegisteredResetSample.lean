import OAI.Hierarchy.DescentPaddedResetCharges
import OAI.Hierarchy.DescentRegisteredWindow
import OAI.Hierarchy.DescentClosedReset
import OAI.Hierarchy.DescentDatePortArchiveDensity
import OAI.Hierarchy.DescentDatedArchiveWidths

namespace OAI
/-! The physical inputs of a dated reset bound. The world and port register may both
depend on the input height and on the choices made on earlier dates. -/
namespace Hierarchy.DescentSixParty.RegisteredReset
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset Chronology Chronology.RegisterTimeline
open DescentPacking.PackedMatch.Local.Stage DescentPrimitivePalette NativePitch ProtocolRAM Filter
noncomputable section
set_option quotPrecheck false

structure Parameters where
  t : ℕ
  f : ℕ
  g : ℕ
  reset : ℕ
  degree : ℕ
  rate : ℕ
  ratio : ℕ
  receiver : ℕ
  drift : ℕ
  bound : ℕ
  archive : ℕ

variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (op : RotorSpec) (K : Parameters) (τ B h : ℕ)

local notation "J" => Nat.log 2 h/(2*B)
local notation "tb" => tail τ J
local notation "sched" x => stageNumbers G K.t J K.f K.g K.reset x tb
local notation "cell" => groupBits K.t J (hostRate K.t K.reset) (capRate G K.t K.g) (cutRate K.t K.f K.g)

structure Sample where
  copies : ℕ
  age : ℕ
  p : ℕ
  w : ℕ
  degreeLimit : ℕ
  position : Position
  ordinary : ℕ→Dated.Ordinary
  rates : ResetRates G (sched copies) cell K.degree n d op.C K.f K.g K.rate tb
  boardAt : rates.board=board
  space : ScheduledCodeRoom G (sched copies) board cell tb age p K.f K.g K.drift degreeLimit h ordinary op
    ((sched copies).firstWidth G.b p) ((sched copies).grainAt G.b p 0) position.ports.operandLanes
    position.ports.roleLanes position.ports.venue position.ports.io (position.ports.priorStart cell position.floor)
    w (position.ports.afterPad cell position.floor).archive
  cap : position.ports.venue.cap=((capCalendar G.b K.t K.g J).take age).prod*256

namespace Sample
variable {G board op K τ B h} (a : Sample G board op K τ B h)
local notation "S" => sched a.copies
local notation "prev" => a.position.ports
local notation "floor₀" => a.position.floor
local notation "start" => (prev).priorStart cell floor₀
local notation "post" => (prev).afterPad cell floor₀
local notation "first" => (S).firstWidth G.b a.p
local notation "grain" => (S).grainAt G.b a.p 0

def hardware := scheduledAtPorts G S board cell tb a.age a.p K.f K.g K.drift a.degreeLimit h
  a.ordinary op first grain prev floor₀
def inputs := DatePorts.innerResetInputs G S board cell tb a.age a.p K.f K.g K.drift a.degreeLimit h
  a.ordinary op first grain post start a.w a.space
def charges := DatePorts.resetCharges G S board cell tb a.age a.p K.f K.g K.drift a.degreeLimit h
  a.ordinary op first grain post start a.w a.space
def «prefix» := DatePorts.archiveCharge G S board cell tb a.age a.p K.f K.g K.drift a.degreeLimit h
  a.ordinary op first grain prev floor₀ a.w
def code := DatePorts.resetDate G S board cell tb a.age a.p K.f K.g K.drift a.degreeLimit h
  a.ordinary op first grain prev floor₀ a.w a.cap a.space
def hostWork := (S).hostSize a.age*h
def groupWork := (S).hostSize a.age*((S).groupCount a.age*(S).radix)

structure Geometry : Prop where
  live : a.age < (S).length
  boundary : a.age%((S).rounds+1)=(S).rounds
  input : a.p ≤ h
  ambient : 2^h ≤ a.copies
  bus : a.w ≤ K.ratio*h
  degreeAt : (prev).venue.degree=K.degree
  limit : a.degreeLimit ≤ K.bound
  hosts : (prev).venue.hosts=(S).hostSize a.age
  groups : (prev).venue.groups=(S).groupCount a.age
  blocks : (prev).venue.k=cell
  precision : (prev).venue.paidBits=(S).censusBits a.p
  pitch : (prev).venue.lanes=incoming S cell tb a.p K.f h a.ordinary a.age
  ordinaryAt : ∀i<(S).length,i%((S).rounds+1)≠(S).rounds→(a.ordinary i).payload=h ∧
    (a.ordinary i).unit=(DonorDate.atDate G S K.g cell i a.p).amount
  argPositive : 0 < (prev).operandLanes
  rolePositive : 0 < (prev).roleLanes
  oldPositive : 0 < (prev).venue.lanes
  nextPositive : 0 < incoming S cell tb a.p K.f h a.ordinary (a.age+1)
  archiveWidths : DatePorts.ArchiveWidths G S op prev cell tb a.p K.drift a.degreeLimit h a.age
  argSlots : (prev).argumentsPerNode ≤ (S).retainedArgumentsAt G K.drift
  archiveDensity : (prev).ArchiveDensity ((S).groupCount a.age) h (scale J K.archive) (scale J K.archive)
  atomWork : ∀x:Fin (2^cell),((prev).io.atoms x.val).work ≤ 7
  walsh : 8*(S).localWalshBits a.p ((S).groupWidth cell tb a.age+cell) K.f (quota K.t) ≤ h
  root : 8*a.hardware.inner.successor.groupWidth ≤ h
  width : a.hardware.inner.successor.groupWidth ≤ scale J K.receiver
  roof : a.hardware.fullEnd < 2^a.w
  prime : a.hardware.inner.PrimeRoom (a.hardware.inner.stageStart start) a.inputs.src a.inputs.count
    a.inputs.sourceRows a.inputs.oldDegree a.w

structure ReachedAt where
  parties : Type
  degree : ℕ
  bits : parties→ℕ
  world : MarkedWorld F degree parties bits
  q : ℝ
  ε : ℝ
  state : ℕ
  wire : ℕ
  hist : ℕ
  reached : Reached world G q ε (sched a.copies) cell a.age state K.degree wire hist
  capacity : reached.placement.cap=((capCalendar G.b K.t K.g J).take a.age).prod*256

theorem code_paid (r : a.Geometry) : a.code.tariff ≤ a.prefix+a.charges.total :=
  DatePorts.reset_padded_charge G S board cell tb a.age a.p K.f K.g K.drift a.degreeLimit h
    a.ordinary op first grain prev floor₀ a.w a.cap a.space r.oldPositive r.rolePositive r.nextPositive r.roof

def menu (seats profile : ℕ→ℕ) (header : ℕ) : Menu n d :=
  ⟨board,op,K.g,tb,a.p,K.f,K.drift,a.degreeLimit,h,seats,a.ordinary,profile,header⟩

theorem reset_move (seats profile : ℕ→ℕ) (header : ℕ) :
    (resetMove (G:=G) («S»:=S) (a.menu seats profile header) cell a.age a.w a.position a.cap a.space).code=a.code := rfl

end Sample
end
end Hierarchy.DescentSixParty.RegisteredReset

end OAI
