import OAI.Hierarchy.ProtocolRAMStripNativeIDs
import OAI.Hierarchy.ProtocolRAMBoughtCatalogueSupport

namespace OAI
/-! # A genuine repair use keeps the global ordinal of its original purchase -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage CoreBoard ReportSockets BoughtSockets PurchaseFrozen
open ThreeFlat.RAM
open scoped Fin.CommRing Classical
variable {z W k attempts : ℕ}

theorem physical_purchase (b : Board) (v : Directory attempts) (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^z)))
    (depth K G H : ℕ) (m : Shelf.Mem z (2^W)) (phase : Fin attempts→PhasePrice)
    (T : Fin attempts→ℝ) (kind mode : Fin attempts→ℕ) (frozen fixture : Fin attempts→Shelf.Mem z (2^W))
    (incoming : ∀a,(v.shelf a).Incoming (k:=k) S π depth (phase a) (T a) (kind a) (frozen a))
    (prepare : ∀a (i : Key z (2^W) k),(v.shelf a).Prepared S depth (fixture a) i (frozen a))
    (room : ∀a,(v.shelf a).flagsBase S z (2^W) k depth+count z (2^W) k*paths z S.degree depth<2^Native.wordBits z (2^W) Native.copies)
    (archive : ∀a (r : Fin (count z (2^W) k*paths z S.degree depth)),m (v.flagBase a+r.val)=
      if mode a=3 then (v.shelf a).result S k depth (frozen a) ((v.shelf a).flagsBase S z (2^W) k depth+r.val) else 0)
    (outer : (v.header z (2^W) k S.degree depth).Loaded m) (events : attempts≤2^Native.wordBits z (2^W) Native.copies)
    (e : Bought S π depth (fun a=>Shelf.catalogueMarks (k:=k) (mode a) (v.shelf a) (phase a) (T a) (kind a) (frozen a)))
    (size : (v.header z (2^W) k S.degree depth).count=b.boughtRows)
    (source : b.bought=v.source S z W k depth K G H) (fits : b.rows<2^Native.wordBits z (2^W) Native.copies)
    (ball : Expr) (r : Word (Native.wordBits z (2^W) Native.copies))
    (truth : ball.eval m r=((BoughtLocation.relative e.2).val:Word _)) :
    let head:=v.header z (2^W) k S.degree depth
    let physical:=b.boughtIndex (Fin.cast size (head.enum ⟨e.1,BoughtLocation.relative e.2⟩))
    mode e.1=3 ∧ (b.commonID (b.originalProbe head.ports e.1.val ball)).eval m r-(b.idBase:Word _)=(physical.val:Word _) := by
  obtain ⟨modeRead,flag⟩:=v.original_active S π depth K G H m phase T kind mode frozen fixture incoming prepare room archive outer events e
  exact ⟨modeRead,checkedOriginal b v S z (2^W) k depth size e.1 (BoughtLocation.relative e.2) m r ball truth fits (by simpa only [source] using flag)⟩

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
