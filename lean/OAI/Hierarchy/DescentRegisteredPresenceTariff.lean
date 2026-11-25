import OAI.Hierarchy.DescentRegisteredResetSum
import OAI.Hierarchy.DescentRegisteredArchiveTariff
import OAI.Hierarchy.DescentPriorNodePresenceVolume
import OAI.Hierarchy.DescentPriorNodePresenceRate
import OAI.Hierarchy.DescentDatePortArchivePitchRoom
import OAI.Hierarchy.DescentNamedSliceOpenInvoice

namespace OAI
/-! Pay the native host padding and the original-role-based presence publisher
on the exact physical two pitches, including nonempty participants with no paid jobs. -/
namespace Hierarchy.DescentSixParty.RegisteredReset
open DescentCompiler TerminalScale DescentDatedAddressBook PhysicalReset Chronology NativePitch DescentPrimitivePalette
open DescentSIMDLookup DescentStaticWordColumn Filter
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) {n d : ℕ} (board : NonlinearExpanders.Graph n d)
  (op : RotorSpec) (K : Parameters) (saving : ℕ)

theorem archive : Region G board op K 0 saving :=by
  let α:=1+operandExponent G (stageNumbers G K.t 0 K.f K.g K.reset 0 0)
  let β:=groupRate G K.t K.f K.g K.reset
  let r:=α+β+K.archive
  let C:=540672*(K.ratio+1)
  refine ⟨C,3*r,1,0,?_⟩
  intro τ B _ den _ _
  filter_upwards [DescentPriorNodePresence.Chart.cofinal_area K.ratio r saving,
    eventually_late (K.drift+1) B den,Filter.eventually_ge_atTop 1] with h charged late hpos
  intro a g _ J
  let S:=stageNumbers G K.t J K.f K.g K.reset a.copies (tail τ J)
  let k:=groupBits K.t J S.hostGain S.capGain (cutRate K.t K.f K.g)
  let p:=a.position.ports
  let floor:=a.position.floor
  let pad:=p.resetPad k
  let tok:=p.presence k
  let Z:=S.grainAt G.b a.p 0
  let s:=S.firstWidth G.b a.p
  let U:=scale J K.archive
  let work:=scale J r
  let host:=S.hostSize a.age
  let group:=S.groupCount a.age
  let high:=a.copies/(2^J)^saving
  have mono {a b : ℕ} (ab : a ≤ b) : scale J a ≤ scale J b:=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ ab)
  have u:U ≤ work:=mono (by dsimp [r];omega)
  have period:2^k ≤ work:= (Nat.pow_le_pow_right (by decide : 0<2) (groupBits_linear ..) :
    2^k ≤ scale J β).trans (mono (by dsimp [r];omega))
  have drift : K.drift+1 ≤ scale J 1 := (late.trans (Nat.lt_two_pow_self (n:=J)).le).trans
    (Nat.pow_le_pow_right (by decide : 0<2) (show J ≤ 1*(J+1) by omega))
  have argLimit:S.retainedArgumentsAt G K.drift ≤ scale J α:=(S.capacities_at_scale G K.drift 1 drift).2
  have argCount:p.argumentsPerNode ≤ scale J r:=g.argSlots.trans (argLimit.trans (mono (by dsimp [r];omega)))
  have hostPositive:0 < host:=by
    have copies:0 < a.copies:=(Nat.two_pow_pos h).trans_le g.ambient
    change 0 < a.copies*(2^(hostRate K.t K.reset)*2^k)^a.age
    positivity
  have groupPositive:0 < group:=by
    rw [show group=2^(S.groupWidth k (tail τ J) a.age) from (S.group_power (k:=k) (tail:=tail τ J) rfl rfl _).symm]
    exact Nat.two_pow_pos _
  have pitch:=g.archiveDensity.pitch_room g.archiveWidths hpos groupPositive
  have geometry:=g.archiveWidths
  have record:0 < p.operandBits:=by
    rw [geometry.digits]
    exact (Nat.succ_pos _).trans_le (Nat.le_max_right ..)
  have token:0 < p.tokenBits:=by
    rw [geometry.token]
    apply Nat.clog_pos (by decide : 1<2)
    unfold colors
    omega
  have roleKey:p.tokenBits*p.nodes*p.roleLanes ≤ h/2:=by
    rw [geometry.token]
    exact geometry.roles
  have maskKey:p.nodes*p.roleLanes ≤ h/2:=
    (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ token)).trans roleKey
  have operandKey:p.nodes*p.operandLanes ≤ h/2:=
    (Nat.mul_le_mul_right _ (Nat.le_mul_of_pos_left _ record)).trans geometry.operands
  have prevHost:0 < p.venue.hosts:=by rw [g.hosts]; exact hostPositive
  have radix:0 < S.radix:=Nat.two_pow_pos k
  have from_ : p.venue.groups ≤ p.roleLanes ∨ h ≤ p.roleLanes*U:=by
    rw [g.groups];exact pitch.roles
  have to_ : p.venue.groups ≤ p.operandLanes ∨ h ≤ p.operandLanes*U:=by
    rw [g.groups];exact pitch.operands
  have physical:=charged tok J a.copies a.w U S.radix prevHost radix period u g.rolePositive g.argPositive
    (pitch.roleHalf.trans (Nat.div_le_self ..)) (pitch.operandHalf.trans (Nat.div_le_self ..))
    roleKey maskKey operandKey from_ to_ (Nat.div_le_self ..) g.ambient g.bus
  let roles:=pad.roleBank floor
  let arities:=p.paddedArity k floor
  let pub:=tok.phase (pad.endAddress floor) roles arities a.w
  have publisher:(pub.ticks+7*names pub.program)*a.w ≤ tok.areaFee*a.w:=
    Nat.mul_le_mul_right a.w (tok.tariff _ roles arities a.w g.rolePositive g.argPositive)
  let raw:=previousArchiveLayout G S board k (tail τ J) a.age a.p K.f K.g K.drift a.degreeLimit h
    a.ordinary op s Z p floor
  let move:=pad.phase floor (p.archive.prior raw) (fun x=>p.archive.roles.bank x.val) a.w
  have rectangles:=DatePorts.archive_rectangles G S board k (tail τ J) a.age a.p K.f K.g K.drift a.degreeLimit h
    a.ordinary op s Z p floor a.w J r K.ratio U U g.argPositive g.rolePositive prevHost radix to_ from_ g.bus argCount period u u
  let A:=16384*(K.ratio+1)*scale J (3*r)
  let D:=524288*(K.ratio+1)*scale J (2*r)
  have first : (move.ticks+7*names move.program)*a.w ≤ p.venue.hosts*h*A+p.venue.hosts*(p.venue.groups*S.radix)*A:=rectangles
  have second : (pub.ticks+7*names pub.program)*a.w ≤ p.venue.hosts*h*D+p.venue.hosts*(p.venue.groups*S.radix)*D+high:=
    publisher.trans physical
  rw [g.hosts,g.groups] at first second
  have coefficients:A+D ≤ C*scale J (3*r):=by
    have rate:=mono (show 2*r ≤ 3*r by omega)
    dsimp only [A,D,C]
    nlinarith only [Nat.mul_le_mul_left (524288*(K.ratio+1)) rate]
  change ((move.ticks+pub.ticks)+7*names (move.program.seq pub.program))*a.w ≤ _
  rw [names_seq]
  have sum:=Nat.add_le_add first second
  change _ ≤ host*h*(C*scale J (3*r))+host*(group*S.radix)*(C*scale J (3*r))+1*high
  nlinarith only [sum,Nat.mul_le_mul_left (host*h) coefficients,Nat.mul_le_mul_left (host*(group*S.radix)) coefficients]

end
end Hierarchy.DescentSixParty.RegisteredReset

end OAI
