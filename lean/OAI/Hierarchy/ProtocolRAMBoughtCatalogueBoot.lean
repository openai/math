import OAI.Hierarchy.ProtocolRAMBoughtCatalogueImage
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueROM
import OAI.Hierarchy.ProtocolRAMColumnRawRead
import OAI.Hierarchy.ProtocolRAMCoreCatalogueBoot

namespace OAI
/-! # Actual bought and core route readers share the priced boot image -/
noncomputable section
namespace Hierarchy.ProtocolRAM.BoughtSockets.Public
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets Calendar
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
variable {h W k attempts R K H jobs tables phases : ℕ} {S : PurchaseSampler}

theorem core_above (order : Fin R≃Edges S h (2^W) k) (M : ℕ) (groups : Fin K≃AllGroups h (2^W))
    (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h W (copies k attempts)) H)
    (m : Boot.Tape h (2^W)) (a : ℕ) (above : CoreCatalogue.top h W K packed.groups H R≤ a) :
    CoreCatalogue.initial order M groups packed m a=m a := by
  have header : CoreCatalogue.headBase h W K packed.groups H+CoreCatalogue.headerWords R≤ a :=
    (le_max_left ..).trans ((le_max_right ..).trans above)
  have first : CoreCatalogue.groupStart h W+ReportGroupROM.words h (2^W)=CoreCatalogue.superStart h W := rfl
  have tail : CoreCatalogue.superStart h W≤ CoreCatalogue.headBase h W K packed.groups H := by
    dsimp only [CoreCatalogue.headBase,SiteROM.endAddress];omega
  unfold CoreCatalogue.initial
  rw [CoreCatalogue.mountHeader_outside _ _ _ _ _ _ _ (.inr header),SiteROM.image_frame _ _ _ _ _ (.inr (by
    change CoreCatalogue.headBase h W K packed.groups H≤ a;omega)),
    ReportGroupROM.frame _ _ _ _ _ (.inr (by omega))]

def words (order : Fin R≃Edges S h (2^W) k) (M : ℕ) (groups : Fin K≃AllGroups h (2^W))
    (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h W (copies k attempts)) H)
    (joint : JointHeader.Board) (ports : PortROM.Table tables) (N depth : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^h))) (stock : ℕ→ℕ) (rest : Boot.Tape h (2^W)) :=
  CoreCatalogue.masterWords order M groups packed joint ports N phase π stock
    (load S (CoreCatalogue.top h W K packed.groups H R) h W k attempts depth rest)

structure Readback (order : Fin R≃Edges S h (2^W) k) (M : ℕ) (groups : Fin K≃AllGroups h (2^W))
    (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h W (copies k attempts)) H)
    (v : Directory attempts) (depth : ℕ) (π : Equiv.Perm (Fin (2^h))) (m : Boot.Tape h (2^W)) : Prop where
  rows : CoreCatalogue.Rows (CoreCatalogue.sourceAt h W k attempts R K packed.groups H (CoreCatalogue.pointBits h W))
    order packed π M m
  rom : (join v S h W k depth K packed.groups H R).ROM S depth groups packed m
  columns : ColumnROM.Tables h W k attempts (CoreCatalogue.top h W K packed.groups H R)
    (CoreCatalogue.groupStart h W) (CoreCatalogue.siteBase h W K) (CoreCatalogue.superStart h W) groups packed π m
  input : Native.Resident (Native.initialOutput h) m (fun i : Fin (2^h)=>(π i).val)

theorem start (order : Fin R≃Edges S h (2^W) k) (M : ℕ) (groups : Fin K≃AllGroups h (2^W))
    (packed : TaggedShorterSupergroups.Directory (TaggedShorterSupergroups.reserved h W (copies k attempts)) H)
    (joint : JointHeader.Board) (ports : PortROM.Table tables) (N depth : ℕ) (phase : Fin phases→PhasePrice)
    (π : Equiv.Perm (Fin (2^h))) (stock : ℕ→ℕ) (rest : Boot.Tape h (2^W))
    (markets : Fin jobs→Market h (2^W) k) {size : ℕ} (layout : Boot.Layout markets size) (v : Directory attempts)
    (space : let endAt := endAddress S (CoreCatalogue.top h W K packed.groups H R) h W k attempts depth
      endAt≤ joint.initial ∧ endAt≤ ports.base ∧ endAt≤ size ∧ endAt<2^Native.wordBits h (2^W) Native.copies ∧
      ∀j,endAt≤ Boot.low (markets j)) :
    let initial := words order M groups packed joint ports N depth phase π stock rest
    let mid := Boot.booted markets size initial
    (Native.subdivisionProgram h (2^W)).Exec (Boot.initial markets size initial) mid (Native.subdivisionConstant (2^W)*2^h) ∧
      Boot.Receipt markets π (Computability.VPVNP.RAMMemory.initialMemory size initial) mid ∧ Readback order M groups packed v depth π mid := by
  let base := CoreCatalogue.top h W K packed.groups H R
  let endAt := endAddress S base h W k attempts depth
  let raw := load S base h W k attempts depth rest
  let init := words order M groups packed joint ports N depth phase π stock rest
  let mid := Boot.booted markets size init
  obtain ⟨jointLo,portLo,memLo,width,marketLo⟩ := space
  have ⟨afterCols,afterKeys⟩ := borders S base h W k attempts depth
  have cap : base≤ endAt := (Nat.le_add_right ..).trans (afterCols.trans afterKeys)
  have coreEnd : CoreCatalogue.headBase h W K packed.groups H+CoreCatalogue.headerWords R≤ base :=
    (le_max_left ..).trans (le_max_right ..)
  have origin : CoreCatalogue.groupStart h W≤ base := by
    unfold CoreCatalogue.headBase SiteROM.endAddress CoreCatalogue.superStart at coreEnd
    omega
  have piLo : 2^h≤ CoreCatalogue.groupStart h W := le_max_right ..
  have heapLo : Native.heapEnd h (2^W) Native.copies≤ CoreCatalogue.groupStart h W := le_max_left ..
  have auth := JointHeader.authentic (N:=N) (k:=k) joint phase π stock (ports.words (CoreCatalogue.initial order M groups packed raw))
    ((piLo.trans origin).trans (cap.trans jointLo))
  have geom := CoreCatalogue.boot_geometry markets layout (Nat.two_pow_pos _) π init auth
  obtain ⟨exec,receipt,rows⟩ := CoreCatalogue.master_boot order M groups packed joint ports N phase π stock raw markets layout
    ⟨cap.trans jointLo,cap.trans portLo,cap.trans memLo,cap.trans_lt width,fun i=>cap.trans (marketLo i)⟩
  have keep (a : ℕ) (lo : CoreCatalogue.groupStart h W≤ a) (hi : a< endAt) : mid a=CoreCatalogue.initial order M groups packed raw a := by
    have orig := receipt.kept a (heapLo.trans lo) (fun j hit=>Nat.not_lt_of_ge hit.1 (hi.trans_le (marketLo j)))
    rw [Computability.VPVNP.RAMMemory.initialMemory,ite_eq_left (hi.trans_le memLo)] at orig
    exact orig.trans (CoreCatalogue.master_retains order M groups packed joint ports N phase π stock raw a (piLo.trans lo)
      (hi.trans_le jointLo) (hi.trans_le portLo))
  have ⟨_,kFits,gFits,sFits,strideFits,_,_⟩ := CoreCatalogue.rooms_of_top
    (by rw [CoreCatalogue.total_stages];omega) (cap.trans_lt width)
  have shared := CoreCatalogue.publicTables order M groups packed raw mid (fun a lo hi=>keep a lo ((hi.trans_le coreEnd).trans_le cap))
    kFits strideFits
  have nFit := (Native.height_extent h (2^W)).trans (Native.extent_word h (2^W) Native.copies).le
  have archive := (resident S base h W k attempts depth rest nFit (by unfold Native.wordBits;omega) width).frame
    (fun a lo hi=>(keep a (origin.trans lo) hi).trans (core_above order M groups packed raw a lo))
  exact ⟨exec,receipt,rows,⟨shared.names,archive.outer,archive.keys,shared.sites,shared.tables⟩,
    ⟨archive.columns,shared.sites,shared.names,geom,shared.tables,gFits,sFits⟩,ColumnROM.boot_raw markets layout (Nat.two_pow_pos _) π init auth⟩

end Hierarchy.ProtocolRAM.BoughtSockets.Public
end

end OAI
