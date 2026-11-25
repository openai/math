import OAI.Hierarchy.DescentResetAtlasRoom
import OAI.Hierarchy.DescentIssuedPacketAddresses

namespace OAI
/-! # Certified original root-packet bank extents in a named atlas -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentSixParty.Chronology DescentFallbackPeriod DescentPackedColony
open DescentPlainTerminal.Suffix DescentSIMDLookup DescentPackedWalsh
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {a : PhysicalReset} (z : a.Atlas) (sh : a.StencilShape) (floor : ℕ) (count hub : Bank) (g Y : ℕ) (roots : a.RootInputs)
local notation "phase" => a.stencilPhase sh floor count hub g Y
local notation "rc" w:arg => a.rootPhase sh floor count hub g Y roots w
local notation "Bk" w:arg => atlasBook z sh floor count hub g Y roots w
local notation "shelf" w:arg => (rc w).headerEnd (Bk w)
local notation "d₀" => a.successor.middle
local notation "page₀" => RootPage (d₀).rootDepth (2^(d₀).rotorBits)
local notation "ly₀" => (phase).S.chosen (phase).base (phase).bank (phase).X.roster

local notation "src" w:arg => atlasSender z sh floor count hub g Y roots w
local notation "H" => (d₀).signedHosts
local notation "coarse₀" => (phase).S.c
local notation "M" => (d₀).signedLanes
local notation "area" w:arg => RootTemplates.arena (shelf w) H (2^coarse₀) M (d₀).rootDepth (d₀).rotorBits a.ports
theorem atlas_packet_addresses {w : ℕ} (room : (phase).Room w) (estimator : (a.estimator floor).Fits w)
    (prior : (rc w).PrefixFits) (last : (rc w).preparedEnd (Bk w)<2^w)
    (degree : (phase).S.degree=a.ports)
    (direction : z.directions=Atlas.directionsOf a sh floor count hub g Y degree)
    (whichHost : z.hostIndex=a.stencilHost sh floor count hub g Y)
    (hosts : (phase).S.hosts=(d₀).signedHosts) (lanes : (phase).S.M=(d₀).signedLanes)
    (packed : ∀p : page₀,(d₀).signedLanes*max (((Bk w).table p).2.field*((Bk w).table p).1)
      ((Bk w).table p).2.outputBits ≤ w/2) :
    (∀x,Accessible z.directions ((src w).tagged x) H (2^coarse₀) M w (shelf w)) ∧
    Accessible z.directions z.hostIndex H (2^coarse₀) M w (shelf w) ∧
    (∀x,((src w).here x).Fits w (shelf w) ∧ H*chunks (2^coarse₀) M≤((src w).here x).size) ∧
    (∀x j,((src w).signed x j).Fits w (shelf w) ∧ H*chunks (2^coarse₀) M≤((src w).signed x j).size) ∧
    ∀(page : page₀) j,(((Bk w).table page).2.reads j).Fits w
      ((area w).middle (rootIndex (d₀).rootDepth (2^(d₀).rotorBits) page).val):=by
  let code : DescentResetHostSize.Code (d₀).rootDepth :=
    ⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le _) (by decide)⟩
  let page : page₀ := (false,.inr (code,none))
  have top : shelf w < 2^w := (Nat.le_add_right ..).trans_lt last
  have lim := (Bk w).limits (rc w).projectionEnd (d₀).signedHosts (2^(phase).S.c) (d₀).signedLanes
  have before : (phase).endAddress ≤ shelf w :=
    (rc w).origin_le_projection.trans (lim.1.trans (lim.2.1.trans lim.2.2))
  have num := (phase).S.banks (phase).X (phase).base (phase).bank room.operands
  obtain ⟨idFit,_,_,_,_,_,ports,_,start⟩ := num
  have pre : (phase).S.afterHeader (phase).base ≤ shelf w :=
    ((phase).S.header_before_output _).trans before
  have lift {b : Bank} {lo : ℕ} (fit : b.Fits w lo) (later : lo≤ shelf w) : b.Fits w (shelf w) :=
    ⟨fit.1,fit.2.1,fit.2.2.trans later⟩
  have hostFit : z.hostIndex.Fits w (shelf w) := by
    rw [whichHost]
    exact lift idFit pre
  have checked:=(atlas_geometry z sh floor count hub g Y roots room estimator prior last degree direction whichHost
    hosts lanes packed).2
  have rows : H*chunks (2^coarse₀) M≤z.hostIndex.size:=by
    rw [whichHost,←hosts,←lanes]
    exact Nat.le_pow_clog (by decide) _
  have read:=(rc w).packet_addresses (a.estimator floor) (phase).S (phase).X (phase).base (phase).bank g
    z.directions z.hostIndex (.lit (a.c/2)) a.depthCut a.classBound a.fullBudget (phase).S.total a.ports
    z.board z.packet z.C z.groupDigits z.batches z.layerBits z.factor z.primitive page checked hostFit rows
  refine ⟨read.1,read.2.1,read.2.2.1,read.2.2.2,?_⟩
  exact (rc w).packet_operand_fit (a.estimator floor) (phase).S (phase).X (phase).base (phase).bank g
    z.directions z.hostIndex (.lit (a.c/2)) a.depthCut a.classBound a.fullBudget (phase).S.total a.ports
    z.board z.packet z.C z.groupDigits z.batches z.layerBits z.factor z.primitive page last checked

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
