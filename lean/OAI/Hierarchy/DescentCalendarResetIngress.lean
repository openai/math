import OAI.Hierarchy.DescentPhysicalResetReceipt
import OAI.Hierarchy.DescentResetCanvasIngressRead

namespace OAI
/-! # Identification of the printed reset intake on the dated cap tape -/
namespace Hierarchy.DescentDatedAddressBook.PhysicalReset
open DescentSixParty DescentCompiler DescentSIMDLookup DescentWalshPrecision DescentPackedWalsh
open ProtocolRAM
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bs : P→ℕ} {W : MarkedWorld F d P bs} {G : PoweredGadget F}
  {price ε : ℝ} {S : AtomSchedule} {k i z D wire hist : ℕ}
  (r : Reached W G price ε S k i z D wire hist)
variable (tail p f h e n t : ℕ) (calendar : List ℕ) (addr : ℕ→ℕ→Bank) (roster : Bank) (out : ResetOutput)
local notation "a₀" => fromCalendar S k tail i G.b p f D h e n t calendar addr roster out

theorem calendar_ingress (base : S.baseGroups=2^tail) (radix : S.radix=2^k)
    (cap : r.placement.cap=(calendar.take i).prod*256) (grain : z=S.grainAt G.b p (i+1))
    (wireFee : wire=S.epochPower^S.priceExponent) (history : hist=S.firstWidth G.b p) :
    (a₀).ingress=DescentResetCanvasIngress.datedLayout r (S.hostSize i) out.funded.oldLanes (a₀).lanes
      (a₀).short out.funded.precision (a₀).bits := by
  simp only [fromCalendar,DescentResetCanvasIngress.datedLayout,DescentResetSignedTokens.datedLayout,
    S.group_power base radix i,r.branch,cap,r.grain,r.edges,r.atoms,grain,wireFee,history]

/-- The same original paid-load bound covers both sides of the width conversion. -/
theorem calendar_ingress_precision (positive : 0<S.height) (alive : i≤S.length)
    (grain : z=S.grainAt G.b p (i+1)) (wireFee : wire=S.epochPower^S.priceExponent)
    (branch : G.b≤2^S.capGain) (oldBits : out.funded.precision=S.censusBits p) :
    r.placement.wire*(r.placement.z*G.b)*r.placement.cap<2^(a₀).ingress.oldBits ∧
    r.placement.wire*(r.placement.z*G.b)*r.placement.cap<2^(a₀).ingress.bits := by
  have bound:=(r.placement.census_caps_at S r.valid positive alive (r.grain.trans grain) (r.edges.trans wireFee) branch).2
  constructor
  · simpa only [fromCalendar,oldBits] using bound
  · apply bound.trans_le (Nat.pow_le_pow_right (by decide) ?_)
    change S.censusBits p≤S.localWalshBits p _ f _
    dsimp only [AtomSchedule.localWalshBits,DescentWalshPrecision.bits]
    omega

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
