import OAI.Hierarchy.TaggedWideDatedLedger
import OAI.Hierarchy.ProbeFixedWideDated
import OAI.Hierarchy.ProbeFixedWidePacketRates
import OAI.Hierarchy.ProbeFixedMarketRows
import OAI.Hierarchy.TaggedWideSiteNumber
import OAI.Hierarchy.TaggedWireLinearRoleRoom
import OAI.Hierarchy.TaggedWirePacketMiddleColumns

namespace OAI
/-! # The genuine slot, owner and party counts on each chronological sheet -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard StripChart
open HistoryRoles RoleProgram WideCPU
open scoped Classical
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "D" => 2^v.W
local notation "P" => v.widePlacement
local notation "U" => v.widePacketDegree
local notation "pc" => treeRowsFactor D k v.sampler.degree v.depth
local notation "sc" => siteFactor D k

def datedArity :=
  1+Fintype.card (ColumnSite (PayloadStrip.Columns (publicStages v.W)) k)+
    Fintype.card (ColumnSite (ChainStrip.Columns v.depth) k)+
    (v.menu.alphabet+2+(v.packetRowsRate*3*5+(U+U)))+
    WireTelescope.PacketTurns.middleColumns v.packetRowsRate+SiteControls.fieldCount U

theorem wide_sheet_shapes (h width : ℕ) (e : Event) :
    let b:=v.widePacketShape h width e
    b.candidates≤pc*2^h ∧ b.parties≤v.datedArity ∧ b.columns≤v.datedArity := by
  cases e with
  | feed b=>exact ⟨Nat.zero_le _,Nat.zero_le _,Nat.zero_le _⟩
  | attempt a=>
    let fmt:=v.nativeFormats (P h width) h width a
    have rows : fmt.market.failures.rows=fmt.market.rows := by cases a <;> rfl
    have candidates : fmt.market.rows≤pc*2^h := by
      rw [←rows]
      exact (v.discrepancy_scan_rows (P h width) h width a).le
    refine ⟨candidates,?_,?_⟩
    · change v.wideBallotParties h a≤v.datedArity
      cases a <;> simp only [wideBallotParties,fixed_stage_count,datedArity] <;> omega
    · change (catalogue F (v.configured (v.seed (P h width) h width)) v.cost).alphabet+2+
        ((v.widePacketRoles h*3)*5+(U+U))+v.wideBallotParties h a+
        WireTelescope.PacketTurns.middleColumns (v.widePacketRoles h)≤v.datedArity
      rw [(v.catalogue_words (v.seed (P h width) h width) width).1,v.packetRows_eq]
      cases a <;> simp only [wideBallotParties,fixed_stage_count,datedArity] <;> omega

def datedCapacity :=
  1+sc+sc*U+RoleRoom.oldFactor D k v.rowFactor+v.rowFactor+
    pc*(v.datedArity*v.datedArity)+sc*v.datedArity

theorem wide_dated_dimensions (h width ell unitCost : ℕ) :
    (v.wideDated h width ell unitCost).Dimensions (v.datedCapacity*2^h) := by
  let a:=v.datedArity
  let n:=2^h
  let E:=(P h width).catalogue.rows
  let real:=v.wideDated h width ell unitCost
  have lift (x K : ℕ) (cap : x≤K*n) (fee : K≤v.datedCapacity) :
      x≤v.datedCapacity*n := cap.trans (Nat.mul_le_mul_right n fee)
  have edges : E≤v.rowFactor*n := v.wideCatalogueRows h width
  have sites := site_count h D k (Nat.two_pow_pos _)
  have phys := RoleRoom.old_bound (W:=v.W) (k:=k) edges
  have degree : real.roleWords≤(sc*U)*n := by
    change (siteLast h D k+1)*U≤_
    simpa only [n,Nat.mul_right_comm] using Nat.mul_le_mul_right U sites
  have cCol : SiteControls.fieldCount U≤a := by dsimp only [a,datedArity];omega
  have widths (C : ℕ) (cw : C≤a) : (siteLast h D k+1)*C≤ sc*a*n := by
    exact (Nat.mul_le_mul sites cw).trans_eq (by dsimp only [n];ring)
  refine ⟨lift 1 1 (by simpa only [n,one_mul] using Nat.succ_le_of_lt (Nat.two_pow_pos h)) (by unfold datedCapacity;omega),
    lift _ sc sites (by unfold datedCapacity;omega),
    lift _ sc (SiteDirectory.words h D k (Nat.two_pow_pos _)) (by unfold datedCapacity;omega),
    lift _ _ phys (by unfold datedCapacity;omega),lift _ _ degree (by unfold datedCapacity;omega),
    lift _ _ edges (by unfold datedCapacity;omega),?_,?_⟩
  · intro j
    let b:=v.widePacketShape h width ((events v.mesh).get j)
    obtain ⟨cc,pp,ww⟩:=v.wide_sheet_shapes h width ((events v.mesh).get j)
    have runs : b.count≤(pc*(a*a))*n :=
      (Nat.mul_le_mul cc (Nat.mul_le_mul pp ww)).trans_eq (by dsimp only [n];ring)
    exact ⟨lift _ _ runs (by dsimp only [a,datedCapacity];omega),
      lift _ _ (widths b.columns ww) (by dsimp only [a,datedCapacity];omega)⟩
  · intro j
    have one:=lift _ _ (widths (SiteControls.fieldCount U) cCol) (by dsimp only [a,datedCapacity];omega)
    exact ⟨by simpa only [Dated.control,Shape.count,wideDated,widePacketDegree,n,one_mul] using one,one⟩

theorem wide_dated_arities (h width ell unitCost : ℕ) :
    let real:=v.wideDated h width ell unitCost
    ∀j,(real.ballot j).parties≤v.datedArity ∧ (real.ballot j).columns≤v.datedArity ∧
      (real.control j).parties≤v.datedArity ∧ (real.control j).columns≤v.datedArity := by
  intro real j
  have s:=v.wide_sheet_shapes h width ((events v.mesh).get j)
  exact ⟨s.2.1,s.2.2,show 1≤v.datedArity by unfold datedArity;omega,
    show SiteControls.fieldCount U≤v.datedArity by unfold datedArity;omega⟩

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
