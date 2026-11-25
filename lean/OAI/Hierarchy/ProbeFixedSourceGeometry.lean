import OAI.Hierarchy.ProbeFixedOriginalSockets
import OAI.Hierarchy.ProbeFixedCatalystBirth
import OAI.Hierarchy.ProtocolRAMJoinedCatalogueFits

namespace OAI
/-! # Terminal geometry operands from the original dated outer archives -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard BoughtSockets StripChart PurchaseFrozen
open scoped Classical Fin.CommRing

variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
variable (z width K G H R idBase : ℕ) (b : JointHeader.Board)
local notation "n" => (v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel
local notation "D" => 2^v.W
local notation "bits" => CoreCatalogue.pointBits z v.W
local notation "dir" => v.originalSockets z width K G H R bits idBase b
local notation "cat" => v.publicBoard z width K G H R bits idBase b
local notation "P" => v.catalystPlacement z K G H R b cat dir
local notation "A" => v.privateArena P z width
local notation "s" => v.nativeBoards P z width
local notation "w" => Native.wordBits z D Native.copies
local notation "cap" => ProtocolRAMPurchaseSampler.span (count z D k*paths z v.sampler.degree v.depth)

/-- Each flat purchased index is the actual pair of a calendar phase and an
outer trial. This works also when either date count is zero. -/
theorem dated_outer_occurs (c : Mesh) (phase : Fin (c.inject+c.cool)) (trial : Fin c.outerFuel) :
    Event.attempt (.outer phase.val trial.val)∈events c :=
  List.mem_flatMap.mpr ⟨phase.val,List.mem_range.mpr phase.isLt,List.mem_append_left _
    (List.mem_flatMap.mpr ⟨trial.val,List.mem_range.mpr trial.isLt,List.mem_cons_self ..⟩)⟩

theorem public_sources_of_dates (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
    (core : CoreRoute.stop v.sampler z v.W k n v.depth K G H R≤b.initial) (word : (A).endAddress v.mesh<2^w)
    (dates : ∀(phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel),
      let a:=Attempt.outer phase.val trial.val
      let f:=v.nativeFormats P z width a
      ((s).outer phase.val trial.val).market.shelf.firstBase+count z D k*PurchaseFrozen.blockSize z D v.sampler.degree v.depth≤(A).endAddress v.mesh ∧
        f.board.purchaseOut+cap≤(A).endAddress v.mesh ∧ f.board.boughtFields 6+cap≤(A).endAddress v.mesh)
    : (cat).core.All (Expr.Fits w ((A).endAddress v.mesh)) ∧ (cat).bought.All (Expr.Fits w ((A).endAddress v.mesh)) := by
  have low : Public.endAddress v.sampler (CoreCatalogue.top z v.W K G H R) z v.W k n v.depth≤(A).endAddress v.mesh :=
    (show CoreRoute.directoryBase v.sampler z v.W k n v.depth K G H R≤CoreRoute.stop v.sampler z v.W k n v.depth K G H R
      from Nat.le_add_right ..).trans (core.trans ((v.catalyst_initial_le_first P z width).trans (Nat.le_add_right ..)))
  have actual (j : Fin n) :
      ((dir).shelf j).firstBase+count z D k*PurchaseFrozen.blockSize z D v.sampler.degree v.depth≤(A).endAddress v.mesh ∧
        (dir).flagBase j+cap≤(A).endAddress v.mesh ∧ (dir).menuBase j+cap≤(A).endAddress v.mesh := by
    let coord : Fin (v.mesh.inject+v.mesh.cool)×Fin v.mesh.outerFuel≃Fin n:=finProdFinEquiv
    obtain ⟨⟨phase,trial⟩,rfl⟩ := coord.surjective j
    have seen:=v.sourcePair_uses z width K G H R bits idBase b r banks src tab dst owners phase trial
    have placed:=dates phase trial
    change _ ∧ _ ∧ _ at seen
    change _ ∧ _ ∧ _ at placed
    change ((dir).shelf (finProdFinEquiv (phase,trial))).firstBase+_≤_ ∧
      (dir).flagBase (finProdFinEquiv (phase,trial))+_≤_ ∧ (dir).menuBase (finProdFinEquiv (phase,trial))+_≤_
    rw [seen.1,seen.2.1,seen.2.2]
    exact placed
  exact Public.joined_sources dir v.sampler low (fun j=>(actual j).1)
    (fun j=>(actual j).2.1) (fun j=>(actual j).2.2) word

theorem public_geometry_of_dates (r : ℕ) (banks : RouteSettlement.Banks) (src tab dst : ℕ) (owners : Bank)
    (core : CoreRoute.stop v.sampler z v.W k n v.depth K G H R≤b.initial) (word : (A).endAddress v.mesh<2^w)
    (dates : ∀(phase : Fin (v.mesh.inject+v.mesh.cool)) (trial : Fin v.mesh.outerFuel),
      let a:=Attempt.outer phase.val trial.val
      let f:=v.nativeFormats P z width a
      ((s).outer phase.val trial.val).market.shelf.firstBase+count z D k*PurchaseFrozen.blockSize z D v.sampler.degree v.depth≤(A).endAddress v.mesh ∧
        f.board.purchaseOut+cap≤(A).endAddress v.mesh ∧ f.board.boughtFields 6+cap≤(A).endAddress v.mesh)
    (i : Fin 7) : ((cat).geometry i).Fits w ((A).endAddress v.mesh) := by
  obtain ⟨coreFits,boughtFits⟩:=v.public_sources_of_dates z width K G H R idBase b r banks src tab dst owners core word dates
  exact (cat).geometry_fits i coreFits boughtFits


end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end
end OAI
