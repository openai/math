import OAI.Hierarchy.ProbeFixedWidePrefixProgram
import OAI.Hierarchy.ProtocolRAMCalendarBill
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueCost
import OAI.Hierarchy.ProtocolRAMCatalogueRowBounds
import OAI.Hierarchy.ProtocolRAMCatalystArchiveGrowth

namespace OAI
/-! # Uniform text and clock for the final directed-link reporter -/
noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage CoreBoard CoreRoute ReportSockets
open CatalystArchive StripChart CatalogueRows ColumnWires
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {F : Type} [Field F] {k : ℕ} {p q Q σ Λ : ℝ} (v : FixedProtocolFormat F k p q Q σ Λ)
local notation "D" => 2^v.W
local notation "P" h:arg width:arg => v.widePlacement h width

/-- The sink selected by the chronological settlement emitter. -/
def wideSink (h width : ℕ) :=
  let b:=v.widePlacement h width
  let stock:=v.fixedTerminalStock b h width
  let page:=v.wideSignedPage h width stock
  let r:=Fintype.card (Slots h D k)
  let s:=v.nativeBoards b h width
  let A:=v.privateArena b h width
  let cnt:=rowOnlyCount v.mesh (declaredRows v.mesh (ownerLedger s v.mesh b.catalogue b.routes F A))
  b.catalogue.sink r (TerminalLayout.settlement page stock) (TerminalLayout.source page)
    (TerminalLayout.table page) (TerminalLayout.destination page)
    (sinkBank (v.catalystStaticStart b h width) cnt r b.catalogue.rows)

private def sinkSourceWork :=
  (246+26*copies k v.wideJobs)+BoughtSockets.wordWork D k v.wideJobs

private theorem geometry_work (h width : ℕ) (j : Fin 7) :
    ((P h width).catalogue.geometry j).work≤32*(v.sinkSourceWork+1) := by
  let K:=WideMemory.K h v.W
  let H:=WideMemory.H h v.W k v.wideJobs
  let G:=(WideMemory.dir h v.W k v.wideJobs).groups
  let R:=WideMemory.R v.sampler h v.W k
  let c:=CoreCatalogue.sourceAt h v.W k v.wideJobs R K G H (CoreCatalogue.pointBits h v.W)
  have total : c.group.work+c.left.work+c.right.work+c.lengthCode.work+c.menu.work=246+26*copies k v.wideJobs :=
    CoreCatalogue.source_work ..
  let d:=(P h width).routes.directory
  have ⟨g,l,r,flag,menu⟩:=d.source_work v.sampler h v.W k v.depth K G H
  apply Board.geometry_work
  · change c.group.work≤_ ∧ c.left.work≤_ ∧ c.right.work≤_ ∧ c.lengthCode.work≤_ ∧ c.menu.work≤_
    unfold sinkSourceWork
    exact ⟨by omega,by omega,by omega,by omega,by omega⟩
  · change (d.source v.sampler h v.W k v.depth K G H).All _
    unfold BoughtSource.All sinkSourceWork
    exact ⟨g.trans (Nat.le_add_left ..),l.trans (Nat.le_add_left ..),r.trans (Nat.le_add_left ..),
      flag.trans (Nat.le_add_left ..),menu.trans (Nat.le_add_left ..)⟩

private def sinkPackedWork :=
  1+7*(4+(max 7 (32*(v.sinkSourceWork+1)))*8+2)

private theorem packed_work (h width : ℕ) :
    let s:=v.wideSink h width
    (packed s.owners (RouteSettlement.fields s.banks s.geometry)).work≤v.sinkPackedWork := by
  let s:=v.wideSink h width
  let B:=max 7 (32*(v.sinkSourceWork+1))
  have fields (j : Fin 7) : (RouteSettlement.fields s.banks s.geometry j).work≤B := by
    by_cases same : j=4
    · subst j
      simpa only [RouteSettlement.fields,Function.update_self,Expr.work] using (le_max_left 7 (32*(v.sinkSourceWork+1)))
    · rw [RouteSettlement.fields,Function.update_of_ne same]
      exact (v.geometry_work h width j).trans (le_max_right ..)
  have price (j : Fin 7) :
      ((RouteSettlement.fields s.banks s.geometry j).atRow (.lookup s.owners .row)).work≤B*8 :=
    (substitute_work _ _).trans (Nat.mul_le_mul_right _ (fields j))
  exact BoughtSockets.choose_work_bound 7 0 (B*8) _ _ price

/-- For every real height and population width, the actual reporter has a
linear clock and a common program-text bound at every physical word width. -/
theorem wideSinkBill :
    ∃K : ℕ,∀h width,(v.wideSink h width).clock≤K*2^h ∧
      ∀W,ProbeStage.Native.text ((v.wideSink h width).native W)≤K := by
  let u:=max (CatalystArchive.slotFactor D k) v.rowFactor
  let clockCap:=42+276*u+(4+(8*u)*(2*v.sinkPackedWork+4))+117*u
  let textCap:=11+4*64+22+15+(11+4*v.sinkPackedWork)+9*(15+6+3)
  refine ⟨max clockCap textCap,?_⟩
  intro h width
  let s:=v.wideSink h width
  have rowCount : Fintype.card (Slots h D k)≤2^h*u := by
    calc
      _ ≤ CatalystArchive.slotFactor D k*2^h := slot_count h D k (Nat.two_pow_pos _)
      _ ≤ u*2^h := Nat.mul_le_mul_right _ (le_max_left ..)
      _ = _ := Nat.mul_comm ..
  have edgeCount : (P h width).catalogue.rows≤2^h*u := by
    calc
      _ ≤ v.rowFactor*2^h := v.wideCatalogueRows h width
      _ ≤ u*2^h := Nat.mul_le_mul_right _ (le_max_right ..)
      _ = _ := Nat.mul_comm ..
  have packedBound : (packed s.owners (RouteSettlement.fields s.banks s.geometry)).work≤v.sinkPackedWork :=
    v.packed_work h width
  have price:=sink_bill s (2^h) u (Nat.two_pow_pos _) rowCount edgeCount
  constructor
  · have factor : passFactor (8*u) (report s.table (P h width).catalogue.rows s.owners
        (RouteSettlement.fields s.banks s.geometry))≤4+(8*u)*(2*v.sinkPackedWork+4) :=
      Nat.add_le_add_left (Nat.mul_le_mul_left _ (Nat.add_le_add_right (Nat.mul_le_mul_left 2 packedBound) _)) _
    calc
      _ ≤ 2^h*(42+276*u+passFactor (8*u) (report s.table _ s.owners (RouteSettlement.fields s.banks s.geometry))+117*u) := price
      _ ≤ 2^h*clockCap := Nat.mul_le_mul_left _ (by dsimp [clockCap]; omega)
      _ = clockCap*2^h := Nat.mul_comm ..
      _ ≤ _ := Nat.mul_le_mul_right _ (le_max_left ..)
  · intro W
    rw [text_sink]
    apply le_trans _ (le_max_right clockCap textCap)
    change sinkText s≤textCap
    simp only [sinkText,rowText,RouteSettlement.words_work,textCap]
    omega

end Hierarchy.ProtocolRAM.Calendar.FixedProtocolFormat
end

end OAI
