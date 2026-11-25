import OAI.Hierarchy.ProtocolRAMStockCommitPortSources
import OAI.Hierarchy.ProtocolRAMStockCommitDebit
import OAI.Hierarchy.ProtocolRAMRowChoice

namespace OAI
/-! # Label addressing and the write interval of the actual priced stock commit -/

namespace Hierarchy.ProtocolRAM.Calendar.StockCommit
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing BigOperators
noncomputable section
variable {w q d : ℕ}

/-- In a named physical link range, a strip port resolves the common identifier
through its actual role table. Its row ordinal is obtained by removing the range base. -/
def LabelSource.fromPorts (out commonBase : ℕ) (geometry : Fin 7 → Expr) (role : Expr) (common : Fin d → Expr) : LabelSource :=
  ⟨out,.op .sub (chooseField d 0 common role) (.lit commonBase),geometry⟩

structure Area.Order (a : Area) : Prop where
  goods : a.goods<a.pad
  seed : a.start+a.pad=a.direct
  fees : a.direct+a.occurrences+a.occurrences=a.broadcast
  flags : a.broadcast+a.rows=a.src
  tape : a.src+2*a.occurrences=a.clip
  cap : a.clip+a.goods=a.excess
  capOut : a.excess+a.pad=a.output
  final : a.output+3*a.goods=a.stop

theorem Area.order (a : Area) : a.Order :=
  ⟨ProtocolRAMPurchaseSampler.lt_span _,rfl,by simp [broadcast,two_mul,Nat.add_assoc],rfl,rfl,rfl,rfl,rfl⟩

theorem fresh_keeps (a : Area) (s : Sources) (b : Batch q d) (x : ℕ) (away : x<a.start ∨ a.stop≤x) :
    (freshSegment a s w b).keeps x := by
  have pad := ProtocolRAMPurchaseSampler.lt_span a.goods
  simp only [freshSegment,fresh,StockCommit.native,StockCommit.charges,RepairHistogram.commit_keeps,
    RepairHistogram.directColumns,Area.plan,Area.bank,List.mem_append,List.mem_cons,List.not_mem_nil,or_false]
  dsimp only [Area.stop,Area.output,Area.excess,Area.clip,Area.src,Area.broadcast,Area.direct,Area.pad] at *
  refine ⟨by omega,⟨by omega,by omega,by omega,by omega⟩,?_⟩
  intro p hp
  rcases hp with (rfl | rfl) | rfl <;> dsimp <;> omega

theorem priced_keeps (a : Area) (s : Sources) (g : LabelSource) (b : Batch q d) (x : ℕ)
    (order : g.out+a.occurrences≤a.start) (away : x<g.out ∨ a.stop≤x) : (pricedSegment a s g w b).keeps x := by
  obtain ⟨goods,seed,fees,flags,tape,cap,capOut,last⟩ := a.order
  exact ⟨by omega,fresh_keeps a s b x (by omega)⟩

end
end Hierarchy.ProtocolRAM.Calendar.StockCommit

end OAI
