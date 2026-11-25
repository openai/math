import OAI.Hierarchy.ProtocolRAMTurnLiveRead
import OAI.Hierarchy.ProtocolRAMRowText

namespace OAI
/-! # Field-major native scans over a chronological word table -/
namespace Hierarchy.ProtocolRAM.DateSpill.Columns
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage.Native
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

variable {W fields rows : ℕ}
def passes (base rows : ℕ) (term : Fin fields→Expr) := ProbeStage.Native.columns rows base (List.ofFn term)

theorem run (base : ℕ) (term : Fin fields→Expr) (m : Memory W)
    (fit : ∀f,(term f).Fits W base) (room : base+fields*rows<2^W) :
    let ps:=passes base rows term
    (program W ps).Exec m (result ps m) (clock ps) ∧
      (∀ (f : Fin fields) (i : Fin rows),result ps m (base+f.val*rows+i.val)=(term f).eval m (i.val:Word W)) ∧
      ∀a,a<base ∨ base+fields*rows≤a→ result ps m a=m a := by
  let es:=List.ofFn term
  have safe (e : Expr) (he : e∈es) : e.Fits W base := by
    obtain ⟨f,rfl⟩:=List.mem_ofFn.mp he
    exact fit f
  refine ⟨columns_exec es m (columns_safe es le_rfl safe (by simpa only [es,List.length_ofFn] using room)),?_,?_⟩
  · intro f i
    have idx : f.val<es.length := by simpa only [es,List.length_ofFn] using f.isLt
    exact (columns_read es m le_rfl safe f.val idx i).trans
      (congrArg (fun e : Expr=>e.eval m (i.val:Word W)) (List.getElem_ofFn (f:=term) idx))
  · intro a ha
    exact columns_frame es m (by simpa only [es,List.length_ofFn] using ha)

end Hierarchy.ProtocolRAM.DateSpill.Columns

end OAI
