import OAI.Hierarchy.DescentDatedOriginPlan
import OAI.Hierarchy.DescentDatedGrainBank
import OAI.Hierarchy.DescentPackedColumnHardware
import OAI.Hierarchy.DescentPackedChunkWork
import OAI.Hierarchy.DescentDyadicSpan

namespace OAI
/-! # The public grain scan and all eight actual source-expression rasters -/
namespace Hierarchy
open DescentDatedPriorOperand DescentSIMDLookup DescentDatedSeedStartup ProtocolRAM DescentStaticWordColumn
open Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section

namespace DescentDatedPublicGrain
theorem word_bill (l : Layout) (w base h unit ratio : ℕ) (grain : Cell (l.size+2))
    (fill : h≤l.lanes*unit) (bus : w≤ratio*h) :
    (ticks l+7*names (program l w base grain))*w ≤ 512*ratio*(h+l.hosts*h+l.hosts*l.groups*unit) :=by
  have rows:=chunk_work l.hosts l.groups l.lanes h unit fill
  have count : l.span≤2*l.rows+1 := DescentDyadicSpan.span_le l.rows
  have cost : ticks l+7*names (program l w base grain)≤512*(1+l.rows) :=by
    unfold program ticks
    rw [names_mount]
    omega
  calc
    _ ≤ (512*(1+l.rows))*(ratio*h) :=Nat.mul_le_mul cost bus
    _ = 512*ratio*(h+l.rows*h) :=by ring
    _ ≤ _ := by
      rw [Nat.add_assoc h]
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_left rows h)
end DescentDatedPublicGrain

namespace DescentDatedPriorOperand.OriginPlan
theorem word_bill {l : Layout} (o : OriginPlan l) (src : Fin l.jobs→Fin 8→Expr)
    (base w h unit ratio lim : ℕ) (work : ∀j f,(src j f).work≤lim) (fill : h≤l.lanes*unit)
    (bus : w≤ratio*h) :
    let ps:=o.outputs src base
    (clock ps+7*names (ProtocolRAM.program w ps))*w ≤
      128*ratio*(l.jobs*8+1)*(lim+1)*(h+l.hosts*h+l.hosts*l.groups*unit) :=by
  let n:=l.jobs*8
  have cost (j : ℕ) (ok : j<n) : (expression src j).work≤lim :=by
    change j < l.jobs*8 at ok
    rw [expression, dite_eq_left ok]
    exact work
      (finProdFinEquiv.symm (⟨j,ok⟩:Fin (l.jobs*8))).1 (finProdFinEquiv.symm (⟨j,ok⟩:Fin (l.jobs*8))).2
  have time:=DescentPackedFlowBatch.tariff (o.outputBase base) l.rows l.span n (expression src) lim cost
  have text:=DescentOperandVectorArena.names_passes (o.outputBase base) l.rows l.span w lim
    (expression src) 0 n (fun j _ ok=>cost j (by omega))
  have cap : clock (o.outputs src base)+7*names (ProtocolRAM.program w (o.outputs src base)) ≤
      128*(n+1)*(lim+1)*(1+l.rows) :=by
    refine (Nat.add_le_add time (Nat.mul_le_mul_left 7 text)).trans ?_
    ring_nf
    omega
  have rows:=chunk_work l.hosts l.groups l.lanes h unit fill
  calc
    _ ≤ (128*(n+1)*(lim+1)*(1+l.rows))*(ratio*h) :=Nat.mul_le_mul cap bus
    _ = 128*ratio*(n+1)*(lim+1)*(h+l.rows*h) :=by ring
    _ ≤ _ := by
      rw [Nat.add_assoc h]
      exact Nat.mul_le_mul_left _ (Nat.add_le_add_left rows h)
end DescentDatedPriorOperand.OriginPlan
end
end Hierarchy

end OAI
