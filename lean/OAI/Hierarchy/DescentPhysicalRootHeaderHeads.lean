import OAI.Hierarchy.DescentRecordedRootHeads
import OAI.Hierarchy.DescentPhysicalResetAtlas
import OAI.Hierarchy.DescentResetMiddleCalendar

namespace OAI
/-! # The reset root reads its host ordinal from the preceding physical stencil -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentSixParty.ResetInput.SourceFrame DescentPackedColony
open DescentPlainTerminal.Suffix DescentFallbackPeriod DescentResetGates DescentContacts DescentSIMDLookup
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} (z : a.Atlas) (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ) (roots : a.RootInputs)
local notation "phase" => a.stencilPhase sh floor count hub g Y
local notation "head" => (phase).S.header (phase).base
local notation "rc" w => a.rootPhase sh floor count hub g Y roots w
local notation "src₀" w => (rc w).issuedSources (a.estimator floor) (phase).S (phase).X (phase).base (phase).bank g
  z.directions z.hostIndex (.lit (a.c/2)) a.depthCut a.classBound a.fullBudget (phase).S.total a.ports

/-- A host ordinal is emitted for every packed input row of each dated root. -/
def stencilHost (a : PhysicalReset) (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ) : Bank :=
  let previous := a.stencilPhase sh floor count hub g Y
  (previous.S.header previous.base).pos

theorem atlas_heads {w : ℕ} (room : (phase).Room w)
    (whichHost : z.hostIndex = a.stencilHost sh floor count hub g Y)
    (top : (rc w).headerEnd (atlasBook z sh floor count hub g Y roots w) < 2^w) :
    (src₀ w).priorCap.Fits w ((rc w).headerEnd (atlasBook z sh floor count hub g Y roots w)) ∧
    (src₀ w).relativeDepth.Fits w ((rc w).headerEnd (atlasBook z sh floor count hub g Y roots w)) := by
  have bank := ((phase).S.banks (phase).X (phase).base (phase).bank room.operands).1
  have «until» := (phase).S.header_before_output (phase).base
  have fits : z.hostIndex.Fits w (rc w).origin := by
    rw [whichHost]
    exact ⟨bank.1,bank.2.1,bank.2.2.trans «until»⟩
  let code : DescentResetHostSize.Code a.successor.middle.rootDepth :=
    ⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le _) (by decide)⟩
  let page : RootPage a.successor.middle.rootDepth (2^a.successor.middle.rotorBits) := (false,.inr (code,none))
  exact (rc w).issuedHeads_fit (a.estimator floor) (phase).S (phase).X (phase).base (phase).bank g
    z.directions z.hostIndex (.lit (a.c/2)) a.depthCut a.classBound a.fullBudget (phase).S.total a.ports
    z.board z.packet z.C z.groupDigits z.batches z.layerBits z.factor z.primitive page
    room.operands le_rfl fits trivial top

private theorem recorded_host {w H G M bound : ℕ} (L : PortLevels.AddressBook) (m : Memory w)
    (hh : L.hosts = H) (hg : L.groups = G) (hm : L.batch = M)
    (resident : L.chart.Resident m) (fit : L.pos.Fits w bound) (p : Row H G M) :
    L.host.eval m ((row H G M p).val : Word w) = (p.1.val : Word w) := by
  subst H G M
  exact L.host_word m bound resident fit p

/-- The row number used by the prepared root selects the host entry published by the
earlier scalar header. This includes all packed groups of every padded host row. -/
theorem issued_host_word {w : ℕ} (room : (phase).Room w)
    (whichHost : z.hostIndex = a.stencilHost sh floor count hub g Y)
    (hosts : (phase).S.hosts = a.successor.middle.signedHosts)
    (lanes : (phase).S.M = a.successor.middle.signedLanes)
    (m : Memory w) (resident : (head).chart.Resident m)
    (p : Row a.successor.middle.signedHosts (2^(phase).S.c) a.successor.middle.signedLanes) :
    (Expr.lookup z.hostIndex .row).eval m ((row _ _ _ p).val : Word w) = (p.1.val : Word w) := by
  rw [whichHost]
  exact recorded_host (head) m hosts rfl lanes resident
    (((phase).S.banks (phase).X (phase).base (phase).bank room.operands).1) p

/-- The scalar chart remains resident after installing the actual reset roots. -/
theorem stencil_header_prepared {w : ℕ} (room : (phase).Room w)
    (space : (rc w).PreparedFits (atlasBook z sh floor count hub g Y roots w))
    (m : Memory w) (resident : (head).chart.Resident m) :
    (head).chart.Resident ((rc w).preparedMid (atlasBook z sh floor count hub g Y roots w) space m) := by
  obtain ⟨_,_,lead,_⟩ := (phase).S.banks (phase).X (phase).base (phase).bank room.operands
  have before : (head).stop ≤ (rc w).origin :=
    lead.2.2.trans ((phase).S.header_before_output (phase).base)
  intro x lower upper
  exact ((rc w).prepared_lower (atlasBook z sh floor count hub g Y roots w) space m x
    (lt_of_lt_of_le upper before)).trans (resident x lower upper)

/-- The original stencil execution supplies this certificate on its reached memory. -/
theorem issued_host_from_order {w dimension common : ℕ} {basis : DescentGL.Layout dimension}
    (room : (phase).Room w) (whichHost : z.hostIndex = a.stencilHost sh floor count hub g Y)
    (hosts : (phase).S.hosts = a.successor.middle.signedHosts)
    (lanes : (phase).S.M = a.successor.middle.signedLanes)
    (space : (rc w).PreparedFits (atlasBook z sh floor count hub g Y roots w))
    (m : Memory w) (order : (phase).S.OldOrder (phase).X (phase).base (phase).bank g common basis m)
    (p : Row a.successor.middle.signedHosts (2^(phase).S.c) a.successor.middle.signedLanes) :
    (Expr.lookup z.hostIndex .row).eval ((rc w).preparedMid (atlasBook z sh floor count hub g Y roots w) space m)
      ((row _ _ _ p).val : Word w) = (p.1.val : Word w) :=
  issued_host_word z sh floor count hub g Y room whichHost hosts lanes _
    (stencil_header_prepared z sh floor count hub g Y roots room space m order.resident) p

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

namespace Hierarchy.DescentDatedAddressBook.ResetMiddle
open DescentCompiler DescentSixParty DescentSixParty.Chronology
/-- The earlier stencil and the signed root rows have the same packing at each reset date. -/
theorem calendar_head_shape (S : AtomSchedule) (k tail age p f D payload e previous n Ht : ℕ) (calendar : List ℕ) :
    let v := fromCalendar S k tail age p f D payload e previous n Ht calendar
    v.stencil.hosts = v.signedHosts ∧ v.stencil.M = v.signedLanes := ⟨rfl,rfl⟩
end Hierarchy.DescentDatedAddressBook.ResetMiddle

end OAI
