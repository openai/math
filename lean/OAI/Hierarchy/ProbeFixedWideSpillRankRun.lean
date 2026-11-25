import OAI.Hierarchy.ProbeFixedWideSpillMiddleBounds
import OAI.Hierarchy.ProtocolRAMDateSpillRankRun
import OAI.Hierarchy.TaggedWirePhysicalTerm

namespace OAI
/-! # The actual fixed number of original, funded spill-page executions -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe WireTelescope ProbeStage CoreBoard ReportSockets
open LinearAlgebra.SpectralBooks ChordGraph SiteTensor
open ThreeFlat.RAM PhysicalProcedure
open HistoryRoles RoleProgram CoreRoute CatalystArchive
open scoped Classical Fin.CommRing

variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
  (h width bits first : ℕ)
local notation "P" => v.widePlacement h width
local notation "D" => 2^v.W
local notation "N" => Stages h D
local notation "edges" => (P).catalogue.rows
local notation "n" => Fintype.card (Old h v.W k edges)
local notation "rows" => Fintype.card (Slots h D k)
local notation "stock" => v.fixedTerminalStock P h width
local notation "slices" => v.widePaidSlices h width bits
local notation "s" => v.wideSignedPage h width stock
local notation "old" => TerminalLayout.settlement s stock
local notation "rank" => v.wideSpillRanks h width bits first
local notation "o" => wideRouteOrder h D k
local notation "K" => siteLast h D k+1
local notation "w" => Native.wordBits h D Native.copies
local notation "dates" => (events v.mesh).length
local notation "heap" => (v.privateArena P h width).endAddress v.mesh+ProtocolRAMPurchaseSampler.span (PurchaseInventory.footprint h N k)
local notation "dir" => WideMemory.dir h v.W k v.wideJobs
local notation "hi" => v.wideRoleStart h width stock slices
local notation "z" => RoleRoom.shape (R:=WideMemory.R v.sampler h v.W k) v.sampler dir edges

theorem wide_spill_rank_run (π : Equiv.Perm (Fin (2^h)))
    (B : Mount (S:=v.sampler) π (siteNumber h D k) edges)
    (m : Memory w) (traversal : ∃cj : Columns h D×Fin k→ℕ,
      RouteSettlement.Directory old m (CoreRoute.enum B o) PurchaseInventory.slot cj)
    (arch : heap≤first) (header : 6*2^s≤first)
    (inventory : v.wideRoleSize h width stock slices≤first)
    (room : v.wideSpillRankEnd h width bits first<2^w) (wide : 2<2^w) :
    ∃out,(v.wideSpillRankProgram h width bits first).Exec m out (v.wideSpillRankTicks h width bits first) ∧
      (∀a<first,out a=m a) ∧ (∀e : Fin edges,out ((rank).zero.base+e.val)=0) ∧
      ∀j<dates,DateSpill.RankTape.Observation rank B o j m out := by
  have floor : first≤v.wideSpillRankEnd h width bits first := by
    change first≤first+(rank).zero.size+dates*(rank).stride
    omega
  have safe {b : Bank} (last : b.base+b.size≤first) : b.Fits w first :=
    ⟨Nat.two_pow_pos _,by have := floor.trans_lt room;omega,last⟩
  have metaRoom := RoleRoom.stock_room (R:=WideMemory.R v.sampler h v.W k) v.sampler dir edges hi
  change (z).stop hi+n+(RoleROM.bank ((z).stop hi+n) n).size≤v.wideRoleSize h width stock slices at metaRoom
  have before : (RoleROM.bank ((z).stop hi) n).size=(RoleROM.bank ((z).stop hi+n) n).size := rfl
  apply DateSpill.RankTape.execute rank B o (siteNumber h D k).injective (publicChord h D k) dates m
  refine ⟨rfl,traversal,safe ?_,safe ?_,⟨safe ?_,trivial⟩,⟨safe ?_,trivial⟩,?_,room,wide⟩
  · change 5*2^s+2^s≤first
    omega
  · change 4*2^s+2^s≤first
    omega
  · change (z).stop hi+(RoleROM.bank ((z).stop hi) n).size≤first
    omega
  · exact metaRoom.trans inventory
  · intro j hj
    exact safe (v.wide_spill_page_floor h width bits first ⟨j,hj⟩ arch)

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
