import OAI.Hierarchy.ProtocolRAMPaidCatalogueBoard
import OAI.Hierarchy.ProtocolRAMCoreCatalogueNative
import OAI.Hierarchy.ProtocolRAMCoreCatalogueLocated
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueSupport
import OAI.Hierarchy.ProtocolRAMCataloguePositiveWidth

namespace OAI
/-! # Physical pruning from the actual CT core and dated acquired-row serializers -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe ProbeStage ProbeStage.Native PurchaseFrozen PurchaseCT
open BoughtSockets ReportSockets CoreBoard TaggedShorterSupergroups ProtocolRAMEmit
open scoped Classical Fin.CommRing
variable {z W k attempts K H R r : ℕ} {I J : Type*} [Fintype I] [Fintype J]

def live_pruning (v : BoughtSockets.Directory attempts) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth M payload boardLevel bits idBase : ℕ) (marks : Marks z W k attempts) (unique : Exclusive marks)
    (groups : Fin K≃AllGroups z (2^W)) (num : ReportGroupROM.Numbering z (2^W))
    (packed : TaggedShorterSupergroups.Directory (reserved z W (ReportSockets.copies k attempts)) H)
    (terminal : Shelf.Mem z (2^W)) (phase : Fin attempts→PhasePrice) (T : Fin attempts→ℝ) (kind mode : Fin attempts→ℕ)
    (frozen fixture : Fin attempts→Shelf.Mem z (2^W))
    (meaning : ∀ a,mode a=3 → marks a=StripDirectory.actualMarks (v.shelf a) (phase a) (T a) (kind a) (frozen a))
    (incoming : ∀a,(v.shelf a).Incoming (k:=k) S π depth (phase a) (T a) (kind a) (frozen a))
    (prepare : ∀a (i : Key z (2^W) k),(v.shelf a).Prepared S depth (fixture a) i (frozen a))
    (room : ∀a,(v.shelf a).flagsBase S z (2^W) k depth+count z (2^W) k*paths z S.degree depth<2^wordBits z (2^W) Native.copies)
    (archive : ∀a (r : Fin (count z (2^W) k*paths z S.degree depth)),terminal (v.flagBase a+r.val)=
      if mode a=3 then (v.shelf a).result S k depth (frozen a) ((v.shelf a).flagsBase S z (2^W) k depth+r.val) else 0)
    (data : ∀a (i : Key z (2^W) k),(v.shelf a).PortData S π depth i terminal) (ct : numberLoaded num π terminal)
    (remap : ReportGroupROM.Resident v.remapBase groups num terminal)
    (outer : (v.header z (2^W) k S.degree depth).Loaded terminal)
    (keys : (StripDirectory.stratumHeader z (2^W) k S.degree depth v.keysBase).Loaded terminal)
    (sites : SiteROM.Resident packed v.sitesBase terminal)
    (tables : ∀g,let j:=((groups.symm g).val:Word (wordBits z (2^W) Native.copies))
      (ProtocolRAMSupergroupDirectory.groupBank v.superBase K).read terminal j=((packed.group g).val:Word _) ∧
      (ProtocolRAMSupergroupDirectory.offsetBank v.superBase K).read terminal j=(packed.base g:Word _))
    (events : attempts≤2^wordBits z (2^W) Native.copies)
    (keySize : count z (2^W) k≤2^wordBits z (2^W) Native.copies)
    (tileSize : (depth+1)*paths z S.degree depth≤2^wordBits z (2^W) Native.copies)
    (gFit : packed.groups≤2^wordBits z (2^W) Native.copies) (sFit : packed.groups*H≤2^wordBits z (2^W) Native.copies)
    (siteFit : siteLast z (2^W) k+1≤2^wordBits z (2^W) Native.copies)
    (order : Fin R≃Edges S z (2^W) k)
    (coreRows : CoreCatalogue.Rows (CoreCatalogue.sourceAt z W k attempts R K packed.groups H bits)
      order packed π M terminal)
    (metricFits : ∀j,coreCode S M (order j)<2^wordBits z (2^W) Native.copies)
    (banks : RouteSettlement.Banks) (source table destination : ℕ) (owners : Bank)
    (core : I→List (Fin (liveBoard v S z W k depth R K packed.groups H bits idBase).rows))
    (center : J→List (Fin (liveBoard v S z W k depth R K packed.groups H bits idBase).rows))
    (enum : Fin r≃RouteOccurrence core center) (ci : I→ℕ) (cj : J→ℕ)
    (idRoom : idBase+(liveBoard v S z W k depth R K packed.groups H bits idBase).rows<2^wordBits z (2^W) Native.copies)
    (wide : 1<2^wordBits z (2^W) Native.copies)
    (fits : ∀f : Fin 7,f≠4→((liveBoard v S z W k depth R K packed.groups H bits idBase).geometry f).Fits
      (wordBits z (2^W) Native.copies) banks.width.base)
    (space : banks.width.base+(liveBoard v S z W k depth R K packed.groups H bits idBase).rows≤ source)
    (support : let b:=liveBoard v S z W k depth R K packed.groups H bits idBase
      ∀j : Fin b.boughtRows,0<((b.sink r banks source table destination owners).terminalRows terminal enum ci cj
        (b.boughtIndex j)).width→b.bought.flag.eval terminal (j.val:Word _)≠0) :
    let b:=liveBoard v S z W k depth R K packed.groups H bits idBase
    Geometry (boardLayout z (2^W) k payload boardLevel) M 1
      ((b.sink r banks source table destination owners).terminalRows terminal enum ci cj) := by
  let b:=liveBoard v S z W k depth R K packed.groups H bits idBase
  exact b.pruning banks source table destination owners terminal enum ci cj S π depth marks payload boardLevel M
    idRoom wide fits space order (fun i=>coreRows.located depth marks i siteFit (metricFits i))
    (fun i hi=>v.active_located S π depth M marks unique groups num packed terminal phase T kind mode frozen fixture
      meaning incoming prepare room archive data ct remap outer keys sites tables events keySize tileSize gFit sFit siteFit i (support i hi))

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
