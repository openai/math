import OAI.Hierarchy.DescentResetAtlasDirections
import OAI.Hierarchy.DescentPhysicalRootHeaderHeads
import OAI.Hierarchy.DescentPhysicalRootSpectra
import OAI.Hierarchy.DescentResetOldOrderRoom
import OAI.Hierarchy.DescentIssuedRootRoom
import OAI.Hierarchy.DescentResetRootWord

namespace OAI
/-! # Date-local numeric legality of every instruction in the authentic reset atlas -/
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

theorem atlas_lane_room {w : ℕ}
    (layers : z.layerBits=DescentRecordedRotorLayers.width a.depthCut (a.c/2))
    (input : (d₀).signedLanes*(roots.field*Projected.Receiver.arityLimit a.ports (2^(d₀).rootDepth)
      (a.c/2) (d₀).rotorBits (d₀).rootDepth) ≤ w/2)
    (output : (d₀).signedLanes*ResetMiddle.rootWord z.board (d₀).rootDepth roots.Ht a.depthCut (a.c/2)
      z.C z.packet z.instructionBits z.batches ≤ w/2) (p : page₀) :
    (d₀).signedLanes*max (((Bk w).table p).2.field*((Bk w).table p).1) ((Bk w).table p).2.outputBits ≤ w/2 := by
  let code : DescentResetHostSize.Code (d₀).rootDepth :=
    ⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le _) (by decide)⟩
  let page : page₀ := (false,.inr (code,none))
  have args := (rc w).issued_arity (a.estimator floor) (phase).S (phase).X (phase).base (phase).bank g
    z.directions z.hostIndex (.lit (a.c/2)) a.depthCut a.classBound a.fullBudget (phase).S.total a.ports
    z.board z.packet z.C z.groupDigits z.batches z.layerBits z.factor z.primitive page p
  have outs := (rc w).issued_output (a.estimator floor) (phase).S (phase).X (phase).base (phase).bank g
    z.directions z.hostIndex (.lit (a.c/2)) a.depthCut a.classBound a.fullBudget (phase).S.total a.ports
    z.board z.packet z.C z.groupDigits z.batches z.layerBits z.factor z.primitive page p
  have old : ((Bk w).table p).2.field=roots.field := args.2
  have span : ((Bk w).table p).2.outputBits ≤ ResetMiddle.rootWord z.board (d₀).rootDepth roots.Ht
      a.depthCut (a.c/2) z.C z.packet z.instructionBits z.batches := by
    simpa only [atlasBook,ResetMiddle.rootWord,layers] using outs
  rw [old,←Nat.mul_max_mul_left]
  exact max_le ((Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ args.1)).trans input)
    ((Nat.mul_le_mul_left _ span).trans output)

private theorem morePorts {n H G M w lo hi : ℕ} {P : Ports n} {v : Bank}
    (s : Accessible P v H G M w lo) (order : lo≤hi) : Accessible P v H G M w hi := by
  have up {b : Bank} (old : b.Fits w lo) : b.Fits w hi :=
    ⟨old.1,old.2.1,old.2.2.trans order⟩
  exact ⟨fun j=>up (s.ids j),s.idsRoom,up s.roster,s.rosterRoom,up s.offsets,s.offRoom,
    up s.chunks,s.chunkRoom,up s.source,s.srcRoom⟩

/-- Original sender columns with the actual cast and reservation pages of this atlas. -/
def atlasSender (w : ℕ) :=
  let code : DescentResetHostSize.Code (d₀).rootDepth:=
    ⟨(0,0),DescentHostDirectory.mem_codes (Nat.zero_le _) (by decide)⟩
  let page : page₀ := (false,.inr (code,none))
  (rc w).atlasSources (a.estimator floor) (phase).S (phase).X (phase).base (phase).bank g
    z.directions z.hostIndex (.lit (a.c/2)) a.depthCut a.classBound a.fullBudget (phase).S.total a.ports
    z.board z.packet z.C z.groupDigits z.batches z.layerBits z.factor z.primitive page

/-- This room proof is independent of the initial memory and of the measured matrix. -/
theorem atlas_geometry {w : ℕ} (room : (phase).Room w) (estimator : (a.estimator floor).Fits w)
    (prior : (rc w).PrefixFits) (last : (rc w).preparedEnd (Bk w)<2^w)
    (degree : (phase).S.degree=a.ports)
    (direction : z.directions=Atlas.directionsOf a sh floor count hub g Y degree)
    (whichHost : z.hostIndex=a.stencilHost sh floor count hub g Y)
    (hosts : (phase).S.hosts=(d₀).signedHosts) (lanes : (phase).S.M=(d₀).signedLanes)
    (packed : ∀p : page₀,(d₀).signedLanes*max (((Bk w).table p).2.field*((Bk w).table p).1)
      ((Bk w).table p).2.outputBits ≤ w/2) : (rc w).PreparedFits (Bk w) ∧
    (atlasSender z sh floor count hub g Y roots w).OperandRoom (d₀).signedHosts (2^(phase).S.c) (d₀).signedLanes w (shelf w) := by
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
  have port : Accessible z.directions ((ly₀).source (phase).S.r)
      (d₀).signedHosts (2^(phase).S.c) (d₀).signedLanes w (shelf w) := by
    rw [direction]
    exact (congrArg₂ (fun H M => Accessible (Atlas.directionsOf a sh floor count hub g Y degree)
      ((ly₀).source (phase).S.r) H (2^(phase).S.c) M w (shelf w)) hosts lanes).mp
      (morePorts (Atlas.accessible_sameDegree degree _ _ ports) pre)
  have hostFit : z.hostIndex.Fits w (shelf w) := by
    rw [whichHost]
    exact lift idFit pre
  have measures := a.root_spectra_fit sh floor count hub g Y estimator (shelf w) before
  constructor
  · apply (rc w).issued_book_fits (a.estimator floor) (phase).S (phase).X (phase).base (phase).bank g
      z.directions z.hostIndex (.lit (a.c/2)) a.depthCut a.classBound a.fullBudget (phase).S.total a.ports
      z.board z.packet z.C z.groupDigits z.batches z.layerBits z.factor z.primitive page prior last
      (lift room.operands.old.roster (start.trans pre)) (lift room.operands.old.hubs (start.trans pre))
      ((ly₀).source (phase).S.r) port hostFit measures.1 measures.2 _ (atlas_heads z sh floor count hub g Y roots room whichHost top) packed
    intro x y
    exact ProtocolRAMGeneratedWrite.fits_mono _ before ((phase).order_fit room x.val y.val)

  · apply (rc w).issued_operand_room (a.estimator floor) (phase).S (phase).X (phase).base (phase).bank g
      z.directions z.hostIndex (.lit (a.c/2)) a.depthCut a.classBound a.fullBudget (phase).S.total a.ports
      z.board z.packet z.C z.groupDigits z.batches z.layerBits z.factor z.primitive page last
      ((ly₀).source (phase).S.r) port hostFit measures.1 measures.2 _ (atlas_heads z sh floor count hub g Y roots room whichHost top) le_rfl
    intro x y
    exact ProtocolRAMGeneratedWrite.fits_mono _ before ((phase).order_fit room x.val y.val)

theorem atlas_prepared_fits {w : ℕ} (room : (phase).Room w) (estimator : (a.estimator floor).Fits w)
    (prior : (rc w).PrefixFits) (last : (rc w).preparedEnd (Bk w)<2^w)
    (degree : (phase).S.degree=a.ports)
    (direction : z.directions=Atlas.directionsOf a sh floor count hub g Y degree)
    (whichHost : z.hostIndex=a.stencilHost sh floor count hub g Y)
    (hosts : (phase).S.hosts=(d₀).signedHosts) (lanes : (phase).S.M=(d₀).signedLanes)
    (packed : ∀p : page₀,(d₀).signedLanes*max (((Bk w).table p).2.field*((Bk w).table p).1)
      ((Bk w).table p).2.outputBits ≤ w/2) : (rc w).PreparedFits (Bk w) :=
  (atlas_geometry z sh floor count hub g Y roots room estimator prior last degree direction whichHost hosts lanes packed).1

end
end Hierarchy.DescentDatedAddressBook.PhysicalReset

end OAI
