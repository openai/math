import OAI.ThreeFlat.Diagonal.NativeWarmSources
import OAI.Hierarchy.TraceReceiverOriginalOperands
import OAI.Hierarchy.TraceReceiverSeedOffset
import OAI.ThreeFlat.Diagonal.PhysicalTypedAdmission

namespace OAI
/-! # Original seed operands recovered from the emitted interval and chronological rows -/

noncomputable section
namespace Hierarchy.TraceReceiverOriginal
open ThreeFlat Diagonal NavigationPass RAM PhysicalStage HistoryContraction
open RAM.HistoryPartyBatchExec RAM.HistoryInitialSeed RAM.HistoryStageBody.Physical RAM.NavigationNodeRows
open TickWorkspace Computability.VPVNP.BurstRAM PrivateRAM GridThrough FactorPinIntervals
open RAM.HistoryStageSetup TraceReceiverSeedWords
open scoped Classical Fin.CommRing

/-- The head of the genuine archive has the original seed's layer, for empty
and nonempty compressor histories. -/
theorem head_layer {F : Type} [Field F] {d l : ℕ} {A : State d l} (r : Run F A)
    (h : r.plan.History) (C : r.Charges) (O : A.ArchiveSites) (p : r.ArchivePath h C O)
    (initial : LayerData O.layer) :
    ∃ row∈r.archiveList h C O p initial,row.layer=O.layer := by
  cases r with
  | done=>exact ⟨_,List.mem_cons_self,rfl⟩
  | step=>exact ⟨_,List.mem_cons_self,rfl⟩

/-- The values of the initial node's lane, stage, and absolute S44 ordinal
follow from its actual cursor enumeration in the selector journal. -/
theorem cursor_fields {F : Type} [Field F] (a : NavigationPass.Archive) (B : Block F) {k : ℕ}
    (hk : 2≤k) (low off slots : ℕ) (ax : k=a.axes) (lanes : a.remainingLanes=2^k)
    (v : (B.cursorState hk low off slots).Site) (ext : ℕ) :
    let O:=a.cursorSeedSites B hk low off slots ax lanes
    let z:=HistorySelectedSeed.archivedSite a (O.ord v) ext
    z.index=O.id v ∧ z.lane=(finFunctionFinEquiv v.2).val ∧ z.stage=v.1.val := by
  have id:=a.cursorSeedSites_ord B hk low off slots ax lanes v
  refine ⟨rfl,?_,?_⟩
  · change ((a.cursorSeedSites B hk low off slots ax lanes).ord v).val%a.remainingLanes=_
    rw [id,lanes]
    exact B.cursorOrdinal_mod hk low off slots v.1 v.2
  · change ((a.cursorSeedSites B hk low off slots ax lanes).ord v).val/a.remainingLanes=_
    rw [id,lanes]
    exact B.cursorOrdinal_div hk low off slots v.1 v.2

/-- The five physical seed fields remain available after registration and
during receiver-local setup. Only the initial record interval is read. -/
theorem kernel_words {W : ℕ} (a : NavigationPass.Archive) (origin mid registered warm : Memory W)
    (words : ∀ j : Fin a.initialSites,∀ c : Fin 5,origin (a.initialRecords+5*j.val+c.val)=
      ((![(a.seed),j.val,0,j.val%a.remainingLanes,j.val/a.remainingLanes] : Fin 5→ℕ) c : Word W))
    (replay : ∀z,a.initialRecords≤z→z<a.metadataEnd→ mid z=origin z)
    (registrar : ∀z,a.initialRecords≤z→z<a.metadataEnd→ registered z=mid z)
    (setup : ∀z,a.initialRecords≤z→z<a.metadataEnd→warm z=registered z)
    (fits : a.initialRecords+5*a.initialSites≤a.metadataEnd) :
    ∀ j : Fin a.initialSites,∀ c : Fin 5,warm (a.initialRecords+5*j.val+c.val)=
      ((![(a.seed),j.val,0,j.val%a.remainingLanes,j.val/a.remainingLanes] : Fin 5→ℕ) c : Word W) := by
  intro j c
  have lo : a.initialRecords≤a.initialRecords+5*j.val+c.val := by omega
  have hi : a.initialRecords+5*j.val+c.val<a.metadataEnd := by omega
  rw [setup _ lo hi,registrar _ lo hi,replay _ lo hi,words]

/-- All per-site S43 and S44 premises are projections of the recovered history
and both genuine acts of publication. In particular every seed has kind zero. -/
theorem archive_row {F : Type} [Field F] {W u k : ℕ}
    (a : NavigationPass.Archive) (B : Block F) (hk : 2≤k) (low off slots : ℕ)
    (ax : k=a.axes) (lanes : a.remainingLanes=2^k) (v : (B.cursorState hk low off slots).Site)
    (r : Run F (B.cursorState hk low off slots)) (h : r.plan.History) (C : r.Charges)
    (p : r.ArchivePath h C (a.cursorSeedSites B hk low off slots ax lanes))
    (b : Banks) (mid issued warm : Memory W) (work pairs : (B.cursorState hk low off slots).Site→ℕ)
    (stored : (a.cursorSeedSites B hk low off slots ax lanes).Charged b (numeric issued) work pairs)
    (warmData : NativeNavigation.WarmSources u b
      (r.archiveList h C (a.cursorSeedSites B hk low off slots ax lanes) p a.seedData) mid issued warm)
    (baseCharge : b.charges=TickWorkspace.base u 43)
    (within : 2*((a.cursorSeedSites B hk low off slots ax lanes).id v)+2≤ TickWorkspace.stride u) :
    let O:=a.cursorSeedSites B hk low off slots ax lanes
    let j:=O.id v
    DirectoryRow b a.seedLayer (O.ord v) warm ∧ warm (b.nodes+8*j)=0 ∧
      warm (b.charges+2*j+1)=(pairs v:Word W) ∧ archiveColumn b (numeric issued) j 0=b.unitWork*work v := by
  let O:=a.cursorSeedSites B hk low off slots ax lanes
  change 2*(O.id v)+2 ≤ TickWorkspace.stride u at within
  obtain ⟨row,occurs,layer⟩:=head_layer r h C O p a.seedData
  change row.layer=a.seedLayer at layer
  have dir:=warmData.directory row occurs
  have kind:=warmData.kind row occurs
  rw [layer] at dir kind
  obtain ⟨bill,value⟩:=stored v
  have fits:=apart (u:=u) (by decide : 43<45)
  have copy:=warmData.published (b.charges+2*(O.id v)+1) (by rw [baseCharge];omega)
    (by rw [baseCharge];omega)
  refine ⟨dir (O.ord v),kind (O.ord v),?_,bill⟩
  change (issued (b.charges+2*(O.id v)+1)).val=pairs v at value
  rw [copy,←value,Fin.cast_val_eq_self]

/-- The genuine charged source and the archive's uniform cap imply the local
four-work reservation without any further per-leaf bound. -/
theorem work_room {F Pins E : Type} [Field F] {b : Banks} {mem : ℕ→ℕ} {K height cap idx work u : ℕ}
    {node : Run.SelectedNode F Pins E} (priced : Run.PricedAt b mem K height cap idx node)
    (unit : 0<b.unitWork) (bill : archiveColumn b mem idx 0=b.unitWork*work)
    (small : 4*cap≤volume u) : 4*work≤volume u := by
  obtain ⟨_,a,_,read,paid,_,_⟩:=priced
  have wk : work≤b.unitWork*work:=Nat.le_mul_of_pos_left _ unit
  rw [←bill,read] at wk
  exact (Nat.mul_le_mul_left 4 (wk.trans paid)).trans small

end Hierarchy.TraceReceiverOriginal
end

end OAI
