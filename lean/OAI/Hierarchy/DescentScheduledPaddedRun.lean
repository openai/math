import OAI.Hierarchy.DescentScheduledPaddedDate
import OAI.Hierarchy.DescentScheduledResetFromPorts

namespace OAI
/-! The actual old archive and its measured height suffice on every previous date. -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentPacking.PackedMatch.Local.Stage DescentPackedWalsh
open DescentSixParty.Chronology DescentSIMDLookup DescentWalshPrecision DescentSixParty.PackedFlow.Padded ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
set_option quotPrecheck false
variable {F : Type} [Field F] (G : PoweredGadget F) (S : AtomSchedule) {n d : ℕ}
    (board : NonlinearExpanders.Graph n d) (k tail age p f gain drift degree h : ℕ)
    (ordinary : ℕ→Dated.Ordinary) (op : RotorSpec) (s Z : ℕ)
    (ports : Chronology.DatePorts)
local notation "old" => ports.venue
local notation "io" => ports.io

local notation "a" => scheduledAtPorts G S board k tail age p f gain drift degree h ordinary op s Z ports
variable (floor w : ℕ)
local notation "ap" => (a) floor
local notation "post" => ports.afterPad k floor
local notation "next" => ports.priorStart k floor
local notation "pack" => ports.resetPad k
local notation "L" => (ap).inner.successor.setup.retained
local notation "cap" => ((capCalendar G.b S.rounds gain S.height).take age).prod*256
local notation "support" => ScheduledCodeRoom G S board k tail age p f gain drift degree h ordinary op s Z
  ports.operandLanes ports.roleLanes old io next w (post).archive

local notation "raw" => previousArchiveLayout G S board k tail age p f gain drift degree h ordinary op s Z ports floor
local notation "publisher" => priorArchivePhase G S board k tail age p f gain drift degree h ordinary op s Z ports floor w
local notation "oldExp" => NativePitch.resetCut S k tail p f h age

private theorem padded_shape (homes : (old).hosts=S.hostSize age) (groupsOld : (old).groups=S.groupCount age)
    (args : (L).previousArgs=ports.argumentsPerNode) : (L).inputShape ports=pack :=by
  have gr : (L).groups=(old).groups :=groupsOld.symm
  have hosts : (L).hosts=(old).hosts:=homes.symm
  simp only [DescentResetRetainedSetup.Layout.inputShape,DatePorts.resetPad,hosts,gr,args]
  rfl

theorem scheduled_padded_any (homes : (old).hosts=S.hostSize age) (blocks : (old).k=k)
    (capacity : (old).cap=cap) (groupsOld : (old).groups=S.groupCount age) (lanesOld : (old).lanes=2^oldExp)
    (groups : S.baseGroups=2^tail) (radix : S.radix=2^k) (within : age<S.length)
    (header : ports.HeaderRoom w floor) (wires : ports.WireRoom w floor) (paid : ports.PaidRoom w floor)
    (short : 8*(ap).inner.successor.groupWidth≤h) (bus : h≤w) (degreeRoom : (old).degree+1<2^w)
    (top : (ap).fullEnd<2^w) (native : ports.archive.Fits raw floor)
    (blocksBefore : 2^k≤ports.archive.roles.blocks) (roleEnd : ports.archive.roles.endAddress≤floor)
    («arguments» : (L).previousArgs=ports.argumentsPerNode) :
    ∃res : support, ∀m : Memory w,∃out,
      (scheduledPadded G S board k tail age p f gain drift degree h ordinary op s Z ports floor w capacity res).Runs m out ∧
      (scheduledPadded G S board k tail age p f gain drift degree h ordinary op s Z ports floor w capacity res).cheap ∧
      ∀z,z<floor ∨ (ap).fullEnd≤z → out z=m z :=by
  have shape:=padded_shape G S board k tail age p f gain drift degree h ordinary op s Z ports floor
    homes groupsOld «arguments»
  have cuts:=(ap).stages
  have afterFit:next<2^w:=cuts.2.trans_lt top
  have originalFit:floor<2^w:=cuts.1.trans_lt afterFit
  have pages:∀j,((ports.archive.prior raw) j).Fits w floor :=
    (raw).prior_registers ports.archive.seed ports.archive.nodeBase ports.archive.arguments floor w native.1 native.2 originalFit
  have role : ∀x : Fin (2^k),(ports.archive.roles.bank x.val).Fits w floor:=
    fun x=>ports.archive.roles.fits w floor x.val (x.isLt.trans_le blocksBefore) roleEnd originalFit
  have postHeader : (post).HeaderRoom w next:=
    ⟨(header.mono cuts.1).count,(header.mono cuts.1).roster,header.peers,(header.mono cuts.1).hubs,header.hosts⟩
  have postWires : (post).WireRoom w next:=wires.mono cuts.1
  have postPaid : (post).PaidRoom w next:=⟨paid.issued,(paid.mono cuts.1).stock⟩
  have norm:=(L).normalized_limits ports floor
  rw [shape] at norm
  have sweep : (pack).endAddress floor≤next:=(ports.pad_order k floor).2
  have retained : (post).archive.Fits (L) next:=by
    constructor
    · change (L).previousChart.seedEnd ((ports.presence k).out ((pack).endAddress floor))≤next
      have rr : (L).previousChart.rows=(ports.presence k).rows:=by
        change ((L).inputShape ports).dataRect.rows = _
        rw [shape]
        rfl
      change (ports.presence k).out ((pack).endAddress floor)+(2*(2^k))*(L).previousChart.rows+
        2^Nat.clog 2 ((L).previousChart.rows+1)≤next
      rw [rr]
      exact le_rfl
    · exact norm.2.trans sweep
  have roleStop : (post).archive.roles.endAddress≤next:=by
    apply le_trans _ sweep
    change (pack).roleStart floor+(pack).blocks*(pack).roleRect.rows+2^(Nat.clog 2 ((pack).roleRect.rows+1))≤
      (pack).roleStart floor+((pack).blocks+1)*(pack).roleRect.rows+2^(Nat.clog 2 ((pack).roleRect.rows+1))
    simp only [Nat.add_mul,one_mul]
    omega
  obtain ⟨res,run⟩:=scheduled_port_code G S board k tail age p f gain drift degree h ordinary op s Z
    ports.operandLanes ports.roleLanes post next w homes blocks capacity groupsOld lanesOld groups radix within
    postHeader postWires short bus degreeRoom top retained postPaid (Nat.le_refl _) roleStop
  refine ⟨res,?_⟩
  intro m
  obtain ⟨pstep,frame⟩:=ports.full_pad_any k floor (ports.archive.prior raw) (fun x=>ports.archive.roles.bank x.val)
    m pages role afterFit
  exact DateCode.prior_archive_any publisher _ floor next (ap).fullEnd cuts.1 cuts.2 m
    pstep frame (run ((publisher).image m))

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
