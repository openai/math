import OAI.Hierarchy.ProbeFixedTermBudget
import OAI.Hierarchy.ProtocolRAMCalendarOpeningChronology

namespace OAI
/-! # Charged live core and bought-edge catalogue on each actual terminal selector -/

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native ReportSockets
open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ)
variable {z w choices dim arity goods r lines : ℕ}
local notation "N" => CoreBoard.Stages z (2^v.W)
local notation "I" => Commodity (Fin (2^z)) N k
local notation "J" => CoreBoard.Columns z (2^v.W) × Fin k

/-- Unbought dummy archive slots never pay opening charges. The summation type
enumerates the core plus exactly the genuine photographed links, indexed by their
outer activation times. Every retained bit follows its real physical walk. -/
theorem catalogueBudget (C : Chart w choices dim) (mem : Memory w) (clock : C.mesh=v.mesh) (arena : Arena)
    (f : Attempt→Format z (2^v.W) k arity goods) (start payload : ℕ) (bills : Event→WordRows)
    (empty : ∀i : I,mem (start+PurchaseInventory.slot i)=0) (wide : v.widthFloor≤payload)
    (feeds : Boundary→List CommodityColumn) (sink : Sink r lines) (idBase : ℕ) (role : Attempt→Expr)
    (ids : Attempt→Fin goods→Expr) (tree spill : Attempt→Traversals) (feed : Boundary → CommodityColumn→Traversals)
    (maxBits : ℕ) (π : Equiv.Perm (Fin (2^z))) (marks : Marks z v.W k ((v.mesh.inject+v.mesh.cool)*v.mesh.outerFuel))
    (ord : CoreBoard.Catalogue v.sampler π v.depth marks ↪ Fin lines)
    (length : Fin lines→ℝ) (reserved used : J→ℕ) (charges : Event→Charges)
    (nn : ∀j,0≤length j) (printed : ∀e,length (ord e)=CoreBoard.lenCode v.sampler π v.depth marks v.radius e)
    (funded : ∀j,used j≤reserved j) :
    let A := v.account arena f start payload bills
    let finalMem := run C (events C.mesh) mem
    let final := A.read (.outer (C.mesh.inject+C.mesh.cool) 0) finalMem
    let slices := paidSlices v.mesh f feeds sink idBase role ids tree spill feed maxBits
    let stock := fun i=>final.bits i
    let core := fun i : I=>(CoreBoard.commodityWalk (S:=v.sampler) π i).map (Sum.inl (β:=Bought v.sampler π v.depth marks))
    let center := fun j : J=>(CoreBoard.catalystWalk (S:=v.sampler) j).map (Sum.inl (β:=Bought v.sampler π v.depth marks))
    CalendarReadbacks A C mem (2^z) v.mesh.inject v.actualK v.limit v.finish ((dyadicScale v.W)^8) ((v.W:ℝ)⁻¹^2)
      v.loss v.menu.margin (probeDensity k v.W) (purchaseReward k v.W) →
    (∀ev∈events v.mesh,(bills ev).bill payload finalMem=(charges ev).net v.radius payload) →
    (∀ev∈events v.mesh,((eventSlices f feeds sink idBase role ids tree spill feed maxBits ev).map
        (fun s=>s.toll finalMem length payload)).sum≤(charges ev).install) →
    (∀u a j b,(charges (.attempt (.inner u a j b))).opening=0) →
    (∀b,(charges (.feed b)).opening=0) →
    (∀(u : Fin (v.mesh.inject+v.mesh.cool)) (a : Fin v.mesh.outerFuel),
      (charges (.attempt (.outer u.val a.val))).opening=
        (Fintype.card (LiveChains v.sampler π v.depth (marks (finProdFinEquiv (u,a)))):ℝ)*(Λ*(dyadicScale v.W)^p)) →
    ((events v.mesh).map (fun e=>(charges e).releasedBits)).sum=∑j,used j →
    TermBudget p q Q Λ (2^z) payload v.radius (∑j,reserved j) (CoreBoard.scaleOf v.sampler π v.depth marks)
      (fun e=>(CoreBoard.lenCode v.sampler π v.depth marks v.radius e:ℝ))
      (fun e=>((PaidWidths.total slices finalMem (ord e)+routeLoad core stock e+
          routeLoad center (fun j=>reserved j-used j) e:ℕ):ℝ)/payload) := by
  dsimp only
  intro readback bill entry inner feedsIdle bought released
  let embed : CoreBoard.Edges v.sampler z (2^v.W) k ↪ CoreBoard.Catalogue v.sampler π v.depth marks :=
    ⟨Sum.inl,Sum.inl_injective⟩
  have mapped (e) : length (ord (embed e))=coreLength (CoreBoard.freeLength v.radius) e :=
    (printed (embed e)).trans (CoreBoard.coreCode_read v.sampler v.radius e)
  have capacityBill:=openings_from_calendar v.mesh v.sampler π v.depth v.radius p q Q Λ marks charges inner feedsIdle bought
  have seed : (v.account arena f start payload bills).initialCharge =
      coreDebit v.sampler z (2^v.W) k p q Q Λ (dyadicScale v.W) v.radius := rfl
  have opening : (∑e,Λ*capacity p q Q (CoreBoard.scaleOf v.sampler π v.depth marks e) (length (ord e)))≤
      (v.account arena f start payload bills).initialCharge+((events v.mesh).map (fun e=>(charges e).opening)).sum := by
    rw [seed]
    apply le_of_eq
    simpa only [printed] using capacityBill
  have charged:=v.termBudget C mem clock arena f start payload bills empty wide feeds sink idBase role ids tree spill feed
    maxBits π ord embed length (CoreBoard.scaleOf v.sampler π v.depth marks) reserved used charges nn mapped funded
    readback bill entry opening released
  simp only [embed, Function.Embedding.coeFn_mk, printed] at charged
  convert charged using 1


end
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end OAI
