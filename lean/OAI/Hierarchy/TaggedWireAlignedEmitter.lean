import OAI.Hierarchy.TaggedWireAlignedSlots
import OAI.Hierarchy.ProtocolRAMCatalogueRows
import OAI.Hierarchy.TaggedWirePaidRead

namespace OAI
/-! # Measured catalogue groups and original slot numbers at the terminal emission -/
noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment
open ProbeStage CoreBoard AdaptiveProbe ReportSockets TaggedShorterSupergroups
open HistoryRoles RoleProgram ProtocolRAMReportedPorts Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM
open scoped Classical Fin.CommRing

variable {h W k attempts M H u r K : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h)))
    (depth : ℕ) (marks : Marks h W k attempts) (unique : Exclusive marks)
    (b : Board) (order : Fin b.coreRows≃Edges S h (2^W) k) (acquired : Bought S π depth marks→Fin b.boughtRows)
    (dir : Directory (reserved h W (copies k attempts)) H) (m : Memory u)
    {I J : Type*} [Fintype I] [Fintype J] {core:I→List (Fin b.rows)} {center:J→List (Fin b.rows)}
    (enum:Fin r≃RouteOccurrence core center) (ci:I→ℕ) (cj:J→ℕ)
    (banks:RouteSettlement.Banks) (source table destination:ℕ) (owners:Bank)
local notation "emit" => (b.sink r banks source table destination owners).terminalRows m enum ci cj
local notation "ord" => b.original S π depth marks order acquired
local notation "label" => labelled S π depth marks

omit [Fintype I] [Fintype J] in
/-- Native source words, the actual core/bought split of the terminal
report, and the measured seven-word geometry give the immutable packed
group on each live original row. -/
theorem emitter_groups (groupFit:dir.groups≤2^u)
    (room:b.idBase+b.rows<2^u) (wide:1<2^u)
    (fits:∀f:Fin 7,f≠4→(b.geometry f).Fits u banks.width.base) (space:banks.width.base+b.rows≤ source)
    (coreRows:CoreCatalogue.Rows b.core order dir π M m)
    (v:BoughtSockets.Directory attempts) (same:b.bought=v.source S h W k depth K dir.groups H)
    (boughtRows:∀e,Coordinates dir (boughtInputs v S h W k depth K false) m ((acquired e).val:Word u)
      (locate S π depth marks unique (.inr e,false))) (e:ReportSockets.Row S π depth marks) :
    (emit (ord ((label).symm (.inr e)))).group=(placed S π depth marks unique dir (e,false)).1.val := by
  apply table_group S π depth marks unique b order acquired emit dir m groupFit coreRows
  · exact fun j=>(b.core_reads banks source table destination owners m enum ci cj j room fits space).group
  · exact fun j=>(b.bought_reads banks source table destination owners m enum ci cj j room wide fits space).group
  · exact bought_group S π depth marks unique b acquired dir m v same boughtRows

/-- Full native word resolution, including a core private index or an acquired
original index. Both orientations read the same numerical socket fields
that were used to choose their stable order. -/
theorem resolved_catalogue (L:RoleProgram.Chart) (coreSocket boughtSocket:Bool→Socket) (fits:b.rows<2^u)
    (coreAt:∀j s,Resolved S L (coreSocket s) m (j.val:Word u) (.inl (paid S π depth marks unique (.inl (order j),s))))
    (boughtAt:∀e s,Resolved S L (boughtSocket s) m ((acquired e).val:Word u) (.inl (paid S π depth marks unique (.inr e,s))))
    (e:Catalogue S π depth marks) (s:Bool) :
    Resolved S L (paidInputs b coreSocket boughtSocket s) m ((ord e).val:Word u) (.inl (paid S π depth marks unique (e,s))) := by
  cases e with
  | inl f=>
    simpa only [Board.original, Sum.elim_inl, Equiv.apply_symm_apply] using
      paid_core S L b m coreSocket boughtSocket (order.symm f) s _ fits (coreAt (order.symm f) s)
  | inr j=>
    exact paid_bought S L b m coreSocket boughtSocket (acquired j) s _ fits (boughtAt j s)

omit [Fintype I] [Fintype J] in
theorem resolved_at (L:RoleProgram.Chart) (coreSocket boughtSocket:Bool→Socket)
    (receipt:Alignment b S π depth marks M emit (fun i=>(emit i).width) ord)
    (physical:∀e s,Resolved S L (paidInputs b coreSocket boughtSocket s) m ((ord e).val:Word u)
      (.inl (paid S π depth marks unique (e,s))))
    (i:Active b emit) (s:Bool) :
    Resolved S L (paidInputs b coreSocket boughtSocket s) m (i.val.val:Word u)
      (.inl (paid S π depth marks unique (receipt.ident i,s))) := by
  simpa only [receipt.original i] using physical (receipt.ident i) s

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows.Alignment
end

end OAI
