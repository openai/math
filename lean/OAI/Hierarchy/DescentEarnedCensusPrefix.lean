import OAI.Hierarchy.DescentProfiledEarlyEnd
import OAI.Hierarchy.DescentUniformReplaySpace
import OAI.Hierarchy.DescentDatedSliceShelfRate
import OAI.Hierarchy.DescentNamedEarnedPreflightRates
import OAI.Hierarchy.DescentCalendarHostLimit
import OAI.Hierarchy.DescentNamedReplayCalendar
import OAI.Hierarchy.DescentTerminalRoleTables
import OAI.Hierarchy.DescentTerminalFundedPreflight

namespace OAI
/-! # The actual early reel, operand projection, packet replay and census headers -/
namespace Hierarchy.DescentSixParty.SeedNamed
open DescentCompiler DescentCompiler.TerminalScale DescentInitialHost DescentDatedAddressBook Catalyst
open DescentMixedRouter DescentResetInvoice ThreeFlat.Routing
open DescentTerminalCompiledPrefix DescentTerminalPreflightSpace DescentTerminalLocalPortBook ProtocolRAM
open AddressPlan DescentTerminalVertexFields DescentExteriorMatrixUpdate DescentExteriorShelf DescentExteriorReplay
open Filter
noncomputable section
set_option quotPrecheck false

/-- The original public shelves and the terminal operand projection. All locations
and literal memories are numerical data of the published program. -/
structure CensusReplay (k : ℕ) where
  cursor : ℕ
  compact : ℕ
  seedFloor : ℕ
  j : ℕ
  rest : ℕ
  lanes : ℕ
  slots : ℕ
  width : ℕ
  snapshots : Snapshots k
  roleBankBits : Fin 6→ℕ

variable {F : Type} [Field F] (G : PoweredGadget F) (t f g reset τ B n depth C : ℕ)
  (op : RotorSpec) (drift : ℕ)
local notation "J_" h:arg => Nat.log 2 h/(2*B)
local notation "S_" h:arg x:arg =>stageNumbers G t (J_ h) f g reset (ShellSource.sites x) (tail τ (J_ h))
local notation "k_" h:arg => groupBits t (J_ h) (hostRate t reset) (capRate G t g) (cutRate t f g)
local notation "pins" x:arg => Fintype.card (Port (ShellSource.ports x) (ShellSource.X x).width)
local notation "pre" h:arg x:arg => earnedPreflight G t f g reset τ B n depth C op drift (h:=h) x
local notation "sheet" z:arg x:arg => DescentExteriorShelf.span (z).j (z).rest (z).lanes (pins x)
def CensusReplay.roleBase {h:ℕ} (x:ShellSource F h) (z:CensusReplay (k_ h)) :=
  replayBase z.cursor z.compact (sheet z x)
def CensusReplay.replayStart {h:ℕ} (x:ShellSource F h) (z:CensusReplay (k_ h)) :=
  z.roleBase G t f g reset B x+DescentTerminalRoleTables.count z.roleBankBits
local notation "first" h:arg x:arg z:arg => Calendar.earlyEnd (S_ h x) (k_ h) (tail τ (J_ h))
  ((z).replayStart G t f g reset B x) (z).j (z).rest (z).lanes (pins x)
local notation "cal" h:arg x:arg z:arg => Branch.replayCalendar (ShellSource.X x) (S_ h x) (k_ h)
  (tail τ (J_ h)) (z).j (z).rest (z).snapshots
local notation "scanQ" h:arg x:arg => PreflightCalendar.publicSlots G (S_ h x)

def censusReplayUsage {h:ℕ} (x:ShellSource F h) (z:CensusReplay (k_ h)) : ReplayUsage :=
  let c:=cal h x z
  let base:=first h x z
  let cut:=sliceStop base z.slots z.width (2^(k_ h)) c.hosts
  ⟨base,z.slots,z.width,2^(k_ h),c.hosts,c.age,c.cohorts,c.packets,(pre h x).controlBytes,
    (pre h x).paidRows,c.scratch cut⟩

def censusScanBase {h:ℕ} (x:ShellSource F h) (z:CensusReplay (k_ h)) :=
  let c:=cal h x z
  let a:=sliceStop (first h x z) z.slots z.width (2^(k_ h)) c.hosts
  ((pre h x).scanPages (c.packetEnd a) (scanQ h x)).stop

set_option maxHeartbeats 1600000 in
theorem census_scan_original {h:ℕ} (x:ShellSource F h) (z:CensusReplay (k_ h)) :
    censusScanBase G t f g reset τ B n depth C op drift x z=
    (censusReplayUsage G t f g reset τ B n depth C op drift x z).sources :=rfl

/-- Every physical preprocessing source starts beyond the mounted six-field role dictionary. -/
theorem CensusReplay.scan_after_role {h:ℕ} (x:ShellSource F h) (z:CensusReplay (k_ h)) :
    z.replayStart G t f g reset B x≤censusScanBase G t f g reset τ B n depth C op drift x z :=by
  let U:=censusReplayUsage G t f g reset τ B n depth C op drift x z
  have clock : z.replayStart G t f g reset B x≤U.start:=by
    change _≤Calendar.earlyEnd _ _ _ _ _ _ _ _
    simp only [Calendar.earlyEnd,Calendar.earlyAt,Calendar.stop,Calendar.tableAt]
    omega
  have body : U.start≤U.slice :=by
    change _≤U.start+_+_+_
    exact (Nat.le_add_right ..).trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))
  have snapshots : U.slice≤U.scratch:=z.snapshots.start_mono U.slice _ (Nat.zero_le (S_ h x).length)
  have storage : U.scratch≤U.sources:=by
    unfold ReplayUsage.sources ReplayUsage.fresh
    omega
  rw [census_scan_original]
  exact clock.trans (body.trans (snapshots.trans storage))

/-- The terminal controls are placed after all date archives and the entire input shelf. -/
theorem CensusReplay.scan_after_cursor {h:ℕ} (x:ShellSource F h) (z:CensusReplay (k_ h)) :
    max z.cursor (z.compact+17*(sheet z x))≤censusScanBase G t f g reset τ B n depth C op drift x z :=by
  have start_ : max z.cursor (z.compact+17*(sheet z x))≤z.roleBase G t f g reset B x:=
    max_le_max le_rfl (by omega)
  exact start_.trans ((Nat.le_add_right ..).trans (z.scan_after_role G t f g reset τ B n depth C op drift x))

variable (headRate : ℕ)
def CensusReplay.ReadyAt {h:ℕ} (x:ShellSource F h) (z:CensusReplay (k_ h)) : Prop :=
  z.cursor≤2^(headRate*h) ∧ z.seedFloor≤2^(headRate*h) ∧ z.compact+17*(sheet z x)≤z.seedFloor ∧
    z.snapshots.hosts=(S_ h x).hostSize ∧
    DescentTerminalPointerFrame.size (2+3*z.slots) z.width≤2*2^(h/2) ∧
    DescentTerminalRoleTables.count z.roleBankBits≤2^(h/2)

/-- One fixed exponent, before either calendar parameter is selected, includes all
four physical intervals from the last emitted register to the first mask scan. -/
theorem earned_scan_uniform (branch:G.b≤2^(capRate G t g)) :
    ∃R:ℕ,∀τ B,20≤B→2*(6*PreflightCalendar.fieldExponent G t f g reset τ+11)≤B→
    ∀ᶠ h:ℕ in atTop,∀(x:ShellSource F h) (z:CensusReplay ((groupBits t (Nat.log 2 h/(2*B)) (hostRate t reset) (capRate G t g) (cutRate t f g)))),
      IssuedPreflightAt G t f g reset τ B n depth C drift x→z.ReadyAt G t f g reset τ B headRate x→
      censusScanBase G t f g reset τ B n depth C op drift x z≤2^(R*h) :=by
  obtain ⟨ctl,controls⟩:=earned_control_uniform G t f g reset n depth C op drift branch
  let R:=max (max 3 (headRate+5)) ctl
  obtain ⟨K,ledger⟩:=uniform_replay_space R
  refine ⟨K,?_⟩
  intro τ B big budget
  have positive : 0<B:=by omega
  have hostRoom:=scheduled_host_limit G t f g reset τ B
    (fun h (x:ShellSource F h)=>x.sites) (fun h x=>(stageNumbers G t (Nat.log 2 h/(2*B)) f g reset (ShellSource.sites x) (tail τ (Nat.log 2 h/(2*B)))).length)
    (fun _ x=>x.upper) (fun _ _=>Nat.le_succ _)
  filter_upwards [ledger,controls τ B positive budget,early_matrix_words G t f g reset τ B big,
    stage_hop_literal_tariff G t f g reset τ B (by omega),hostRoom,eventually_ge_atTop 1] with h allowed ctrl reel hop heights hpos
  intro x z branch_ purchased
  obtain ⟨last,head,initial,snap,lookup,roles⟩:=purchased
  let S₀:=stageNumbers G t (Nat.log 2 h/(2*B)) f g reset (ShellSource.sites x) (tail τ (Nat.log 2 h/(2*B)))
  let b:=(groupBits t (Nat.log 2 h/(2*B)) (hostRate t reset) (capRate G t g) (cutRate t f g))
  let H:=S₀.hostSize S₀.length
  let E:=pins x
  let Z:=censusReplayUsage G t f g reset τ B n depth C op drift x z
  let W:=max 1 headRate
  let Q:=2^(W*h)
  have exponent {u v:ℕ} (le:u≤v) : 2^(u*h)≤2^(v*h):=Nat.pow_le_pow_right (by decide)
    (Nat.mul_le_mul_right _ le)
  have cheap : 2^h≤Q:=by simpa only [one_mul] using exponent (Nat.le_max_left 1 headRate)
  have header : z.seedFloor≤Q:=head.trans (exponent (Nat.le_max_right ..))
  have latest : z.cursor≤Q:=last.trans (exponent (Nat.le_max_right ..))
  have pages:=reel x.sites
  have short : 2^(h/2)≤Q:=(Nat.pow_le_pow_right (by decide) (Nat.div_le_self ..)).trans cheap
  have budget16 : 16*Q≤2^(R*h):=by
    change 2^4*2^(W*h)≤_
    rw [←Nat.pow_add]
    apply Nat.pow_le_pow_right (by decide)
    have price : W+4≤R:=by dsimp [R,W];omega
    have eq:=Nat.mul_le_mul_right h price
    have spare:=Nat.mul_le_mul_left 4 hpos
    rw [Nat.add_mul] at eq
    omega
  have cheapR : 2^h≤2^(R*h):=cheap.trans ((Nat.le_mul_of_pos_left _ (by decide:0<16)).trans budget16)
  have dim := pages.2.2
  have axis : b*S₀.length≤h ∧ b≤h:=by
    change 4*((S₀.groupWidth b (tail τ ((Nat.log 2 h/(2*B)))) 0+b)*(S₀.groupWidth b (tail τ ((Nat.log 2 h/(2*B)))) 0+b)+
      (S₀.groupWidth b (tail τ ((Nat.log 2 h/(2*B)))) 0+b)+1)≤h at dim
    simp only [AtomSchedule.groupWidth,Nat.sub_zero] at dim
    constructor <;> omega
  have rows : E*2^(z.j+z.rest)≤z.seedFloor:=by
    have w:=row_room z.j z.rest z.lanes E
    change E*2^(z.j+z.rest)≤ sheet z x at w
    omega
  have pinsPaid : E≤z.seedFloor:=(Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)).trans rows
  have coarse : E*2^(b*S₀.length)≤2^(R*h):=by
    have z₁:=Nat.mul_le_mul (pinsPaid.trans head) (Nat.pow_le_pow_right (by decide : 0<2) axis.1)
    have enough : headRate+1≤R:=by dsimp [R];omega
    exact z₁.trans (by simpa only [←Nat.pow_add,Nat.add_mul,one_mul] using exponent enough)
  have roster:=ctrl x branch_
  have scope : Z.Room h R:=by
    constructor
    · have firstPaid:=early_bound_after_roles S₀ b (tail τ ((Nat.log 2 h/(2*B)))) z.cursor z.compact z.j z.rest z.lanes E z.seedFloor (DescentTerminalRoleTables.count z.roleBankBits) initial
      have bound : S₀.length*Calendar.stride S₀ b (tail τ ((Nat.log 2 h/(2*B))))≤Q:=pages.1.trans short
      have length:S₀.length≤Q:=pages.2.1.trans short
      exact firstPaid.trans ((show z.cursor+4*z.seedFloor+S₀.length*Calendar.stride S₀ b (tail τ ((Nat.log 2 h/(2*B))))+S₀.length+1+DescentTerminalRoleTables.count z.roleBankBits≤16*Q by
        have rolePaid:=roles.trans short
        have nz:0<Q:=Nat.two_pow_pos _
        omega).trans budget16)
    · exact (Nat.pow_le_pow_right (by decide) axis.2).trans cheapR
    · exact (heights x).trans (exponent ((Nat.le_max_left 3 _).trans (Nat.le_max_left ..)))
    · exact pages.2.1.trans ((Nat.pow_le_pow_right (by decide) (Nat.div_le_self ..)).trans cheapR)
    · exact coarse
    · exact rows.trans (head.trans (exponent (by dsimp [R];omega)))
    · exact roster.1.trans (exponent (Nat.le_max_right ..))
    · exact roster.2.trans (exponent (Nat.le_max_right ..))
    · exact lookup
    · exact hop x.sites Z.slice z.snapshots snap
  rw [census_scan_original]
  exact allowed Z scope

end
end Hierarchy.DescentSixParty.SeedNamed

end OAI
