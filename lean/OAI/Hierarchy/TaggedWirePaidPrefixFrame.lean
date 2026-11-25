import OAI.Hierarchy.TaggedWireReadBanks
import OAI.Hierarchy.ProtocolRAMCalendarPrefixWidths

namespace OAI
/-! # Positive original paid rows retain their earlier native operand values -/

namespace Hierarchy.ProtocolRAM.PaidWidths
open ThreeFlat.RAM
open Computability.VPVNP.BurstRAM PrivateRAM WireTelescope Calendar
open scoped Classical Fin.CommRing
variable {W edges : ℕ}

/-- A zero weight never consumes an ID from the potentially dormant bought
catalogue. Only positive words require an authenticated endpoint read. -/
theorem Slice.load_congr (s : Slice) (m m' : Memory W)
    (qty : ∀i : Fin s.count,s.amount.eval m (i.val:Word W)=s.amount.eval m' (i.val:Word W))
    (key : ∀i : Fin s.count,0<(s.amount.eval m (i.val:Word W)).val→
      s.edge.eval m (i.val:Word W)=s.edge.eval m' (i.val:Word W)) (e : Fin edges) :
    s.load m e=s.load m' e := by
  apply Finset.sum_congr rfl
  intro i _
  by_cases yes : 0<(s.amount.eval m (i.val:Word W)).val
  · rw [key i yes,qty i]
  · have zero : (s.amount.eval m (i.val:Word W)).val=0:=by omega
    have zero' : (s.amount.eval m' (i.val:Word W)).val=0:=(congrArg Fin.val (qty i)).symm.trans zero
    simp [zero,zero']

theorem Slice.load_observed (s : Slice) (m m' : Memory W) (live : ℕ→Prop)
    (same : ∀x,live x→m x=m' x)
    (qty : ∀i : Fin s.count,ReadBanks.Observed live m (i.val:Word W) s.amount)
    (key : ∀i : Fin s.count,0<(s.amount.eval m (i.val:Word W)).val→
      ReadBanks.Observed live m (i.val:Word W) s.edge) (e : Fin edges) : s.load m e=s.load m' e :=
  s.load_congr m m' (fun i=>ReadBanks.eval_observed live m m' same _ _ (qty i))
    (fun i pos=>ReadBanks.eval_observed live m m' same _ _ (key i pos)) e

theorem total_rows_congr (z : List Slice) (m m' : Memory W)
    (selected : ∀s∈z,∀e : Fin edges,s.load m e=s.load m' e) (e : Fin edges) :
    total z m e=total z m' e := by
  unfold total
  apply congrArg List.sum
  exact List.map_congr_left (fun s mem=>selected s mem e)

theorem prefix_frame (es : List Event) (compile : Event→List Slice) (j : Fin es.length) (m m' : Memory W)
    (old : ∀t∈es.take j.val,∀s∈compile t,∀e : Fin edges,s.load m e=s.load m' e) (e : Fin edges) :
    total (PrefixWidths.prefixRows es compile (j.val+1)) m' e=
      total (PrefixWidths.prefixRows es compile j.val) m e+total (compile (es.get j)) m' e := by
  have fixed : total (PrefixWidths.prefixRows es compile j.val) m e=
      total (PrefixWidths.prefixRows es compile j.val) m' e := by
    apply total_rows_congr
    intro s mem u
    obtain ⟨t,pt,atSite⟩:=List.mem_flatMap.mp mem
    exact old t pt s atSite u
  rw [fixed, List.get_eq_getElem]
  exact PrefixWidths.prefix_step es compile m' e j

end Hierarchy.ProtocolRAM.PaidWidths

end OAI
