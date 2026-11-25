import OAI.Hierarchy.ProtocolRAMCalendarCatalystArchive
import OAI.Hierarchy.ProbeCatalystReservePartition

namespace OAI
/-! # Which original reserve bits the terminal RAM reports as unused -/

noncomputable section
namespace Hierarchy.ProtocolRAM.CatalystArchive
open Calendar ProbeStage ProbeStage.CoreBoard Computability.VPVNP.BurstRAM
open scoped Classical BigOperators
variable {h d k payload w : ℕ} (c : Mesh)
variable (issued : Attempt→Entry (Fintype.card (Columns h d)*k) payload)

def calendarPartition :=
  physicalPartition (h:=h) (d:=d) (k:=k) (site c issued) (debit c issued) (funded c issued)

/-- The index used by the per-resource prefix is the literal number of
rows at earlier dates, plus the original ordinal in this date's rectangle. -/
theorem chronological_rank (t : Fin (events c).length) (row : Fin (atTime c issued t).rows) :
    (rank c issued ⟨t,row⟩).val =
      (∑ u : Fin t.val,(atTime c issued (Fin.castLE t.isLt.le u)).rows)+row.val :=
  finSigmaFinEquiv_apply (n:=fun u=>(atTime c issued u).rows) ⟨t,row⟩

/-- The untouched tail for every physical pair has exactly the size
reported by the two counters after the real reserve scatter. -/
theorem terminal_untouched (a : ReserveUse.Archive) (b : RouteSettlement.Banks) (m : Memory w)
    (mounted : ReserveUse.Mounted a b (fuel c*payload) (site c issued) (debit c issued) m)
    (fitsU : Fintype.card (Columns h d)*k≤b.used.size)
    (fitsR : Fintype.card (Columns h d)*k≤b.reserved.size)
    (wide : fuel c*payload<2^w) (p : Columns h d×Fin k) :
    let key := pairKeys (Columns h d) k p
    let last := ReserveUse.output a b (fuel c*payload) (site c issued) (debit c issued) m
    Fintype.card (Fin (fuel c*payload-usedAt (site c issued) (debit c issued) key)) =
      RouteSettlement.actual b.reserved last key.val-RouteSettlement.actual b.used last key.val := by
  dsimp only
  obtain ⟨used,reserved⟩ := ReserveUse.reported a b (fuel c*payload) (site c issued)
    (debit c issued) m mounted (pairKeys (Columns h d) k p) fitsU fitsR (funded c issued _) wide
  rw [reserved,used]
  exact (Fintype.card_congr (Equiv.refl _)).trans (Fintype.card_fin _)

end Hierarchy.ProtocolRAM.CatalystArchive
end

end OAI
