import OAI.Hierarchy.ProbeFixedTerminalCash
import OAI.Hierarchy.ProtocolRAMCalendarPaidLedger

namespace OAI
/-! # TermBudget for the charged physical rows of the selected public format -/

namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native
open scoped BigOperators Classical
noncomputable section
variable {F : Type*} [Field F] {k : ℕ} {p q Q σ Λ : ℝ}
  (v : FixedProtocolFormat F k p q Q σ Λ)
variable {z w claims dims arity goods r lines : ℕ} {E : Type*} [Fintype E] [DecidableEq E]
local notation "stages" => CoreBoard.Stages z (2^v.W)
local notation "InventoryType" => Commodity (Fin (2^z)) stages k
local notation "Catalysts" => CoreBoard.Columns z (2^v.W) × Fin k
local notation "Core" => CoreBoard.Edges v.sampler z (2^v.W) k

/-- A real chronological budget prices the earlier installed slices, the two
actual returned-radius hops per unused catalyst bit, and every scarce bought
or fixed opening once. Only physical receipt equations remain as inputs. -/
theorem termBudget (C : Chart w claims dims) (mem : Memory w) (clock : C.mesh=v.mesh) (arena : Arena)
    (f : Attempt→Format z (2^v.W) k arity goods) (start payload : ℕ) (bills : Event→WordRows)
    (empty : ∀i : InventoryType,mem (start+PurchaseInventory.slot i)=0) (wide : v.widthFloor≤payload)
    (feeds : Boundary→List CommodityColumn) (sink : Sink r lines) (idBase : ℕ) (role : Attempt→Expr)
    (ids : Attempt→Fin goods→Expr) (tree spill : Attempt→Traversals) (feed : Boundary → CommodityColumn→Traversals)
    (maxBits : ℕ) (π : Equiv.Perm (Fin (2^z))) (ord : E ↪ Fin lines) (label : Core ↪ E)
    (length : Fin lines→ℝ) (t : E→ℝ) (reserved used : Catalysts→ℕ) (charges : Event→Charges)
    (nn : ∀j,0≤length j) (onCore : ∀e,length (ord (label e))=coreLength (CoreBoard.freeLength v.radius) e)
    (funded : ∀j,used j≤reserved j) :
    let A := v.account arena f start payload bills
    let finalMem := run C (events C.mesh) mem
    let final := A.read (.outer (C.mesh.inject+C.mesh.cool) 0) finalMem
    let slices := paidSlices v.mesh f feeds sink idBase role ids tree spill feed maxBits
    let installed := fun e=>PaidWidths.total slices finalMem (ord e)
    let stock := fun i=>final.bits i
    let core := fun i : InventoryType=>(CoreBoard.commodityWalk (S:=v.sampler) π i).map label
    let center := fun j : Catalysts=>(CoreBoard.catalystWalk (S:=v.sampler) j).map label
    CalendarReadbacks A C mem (2^z) v.mesh.inject v.actualK v.limit v.finish ((dyadicScale v.W)^8) ((v.W:ℝ)⁻¹^2)
      v.loss v.menu.margin (probeDensity k v.W) (purchaseReward k v.W) →
    (∀ev∈events v.mesh,(bills ev).bill payload finalMem=(charges ev).net v.radius payload) →
    (∀ev∈events v.mesh,((eventSlices f feeds sink idBase role ids tree spill feed maxBits ev).map
        (fun s=>s.toll finalMem length payload)).sum≤(charges ev).install) →
    (∑e,Λ*capacity p q Q (t e) (length (ord e)))≤ A.initialCharge+((events v.mesh).map (fun e=>(charges e).opening)).sum →
    ((events v.mesh).map (fun e=>(charges e).releasedBits)).sum=∑j,used j →
    TermBudget p q Q Λ (2^z) payload v.radius (∑j,reserved j) t (fun e=>length (ord e))
      (fun e=>((installed e+routeLoad core stock e+routeLoad center (fun j=>reserved j-used j) e:ℕ):ℝ)/payload) := by
  intro A finalMem final slices installed stock core center readback bill entry opening released
  have net := v.terminal arena f start payload bills C clock mem empty wide readback
  have paid := prepaid_calendar A v.mesh bills f feeds sink idBase role ids tree spill feed maxBits v.radius
    finalMem ord length t used p q Q Λ nn charges bill entry opening released
  change (∑e,(length (ord e)*((installed e:ℝ)/payload)+Λ*capacity p q Q (t e) (length (ord e))))≤
    (A.read (.outer (v.mesh.inject+v.mesh.cool) 0) finalMem).paid+2*v.radius*(∑j,(used j:ℝ))/payload at paid
  have stop : v.mesh.inject+v.mesh.cool=C.mesh.inject+C.mesh.cool := by rw [clock]
  rw [stop] at paid
  have payable : 0<payload := v.clock.inject_pos.trans_le (v.clock.inject_width.trans wide)
  have ordinary (i : InventoryType) : ((core i).map (fun e=>length (ord e))).sum≤A.box i := by
    have trueCost := native_account_route v.mesh arena f start payload bills
      (coreDebit v.sampler z (2^v.W) k p q Q Λ (dyadicScale v.W) v.radius) v.a v.radius (probeBonus v.W)
      v.sampler π (fun _=> (0:Fin 1)) i
    change ((CoreBoard.commodityWalk (S:=v.sampler) π i).map
      (coreLength (CoreBoard.freeLength (v.radius:ℝ)))).sum=A.box i at trueCost
    apply le_of_eq
    calc
      _ = ((CoreBoard.commodityWalk (S:=v.sampler) π i).map
          (coreLength (CoreBoard.freeLength (v.radius:ℝ)))).sum := by
        simp only [core,List.map_map,Function.comp_def,onCore]
      _ = A.box i := trueCost
  have returns (j : Catalysts) : ((center j).map (fun e=>length (ord e))).sum≤2*v.radius := by
    have trueCost := (CoreBoard.catalyst_walk (S:=v.sampler) π (fun _=>(0:Fin 1)) (v.radius:ℝ) j).2
    simpa only [center,List.map_map,Function.comp_def,onCore] using trueCost.le
  exact settle_installed_routes p q Q Λ (2^z) payload v.radius (by positivity) payable t (fun e=>length (ord e))
    installed final.paid A.box core stock center reserved used funded ordinary returns paid net


end
end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat

end OAI
