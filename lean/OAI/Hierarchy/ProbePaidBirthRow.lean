import OAI.Hierarchy.ProbePaidPurchasedHoriz
import OAI.Hierarchy.ProtocolRAMStripBoughtHit

namespace OAI
/-! # The original positive purchase ordinal and the serializer's measured endpoint -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.CatalogueRows
open Computability.VPVNP.BurstRAM PrivateRAM ProbeStage ProbeStage.CoreBoard ProbeStage.ReportSockets AdaptiveProbe
open BoughtSockets PurchaseFrozen ProtocolRAMEmit
open scoped Fin.CommRing Classical

variable {h W k attempts depth w M : ℕ} {S : PurchaseSampler} {π : Equiv.Perm (Fin (2^h))}
    {marked : Marks h W k attempts}

theorem bought_faces (e : Bought S π depth marked) :
    Faces (Prod.map (retainedCol π (marked e.1) e.2) id)
      (LocalCommodity.extraEnds (ChainStrip.commodity depth k) (ChainStrip.probe depth) (.inr ()))
      (actualEnds S π depth marked (.inr e)) :=
  Or.inl rfl

/-- No width or uniqueness is obtained from a bought-board sentinel. This
operand is the chronological purchase prefix plus the selected candidate's
own immutable relative row. -/
theorem original_faces (b : Board) (v : Directory attempts)
    (size : (v.header h (2^W) k S.degree depth).count=b.boughtRows)
    (e : Bought S π depth marked) (m : Memory w) (r : Word w) (ball : Expr)
    (selected : ball.eval m r=((BoughtLocation.relative e.2).val:Word w)) :
    let hd:=v.header h (2^W) k S.degree depth
    let actual:=b.boughtIndex (Fin.cast size (hd.enum ⟨e.1,BoughtLocation.relative e.2⟩))
    (b.originalProbe hd.ports e.1.val ball).eval m r=(actual.val:Word w) ∧
      Faces (Prod.map (retainedCol π (marked e.1) e.2) id)
        (LocalCommodity.extraEnds (ChainStrip.commodity depth k) (ChainStrip.probe depth) (.inr ()))
        (actualEnds S π depth marked (.inr e)) := by
  intro hd actual
  refine ⟨(b.originalProbe_read hd.ports e.1.val ball m r _ selected).trans ?_,bought_faces e⟩
  congr 1
  change b.coreRows+(e.1.val*hd.ports+(BoughtLocation.relative e.2).val)=
    b.coreRows+((BoughtLocation.relative e.2).val+hd.ports*e.1.val)
  ring

/-- Bridge the actual seven-field serializer to a positively paid endpoint
inside its true ball. Both physical orientations and both serializer orders
are covered. -/
theorem Located.placed_endpoint {X : Type} (s : X→Site h (2^W) k) (p : DistinctPair X)
    {e : Catalogue S π depth marked} {v : View} {row : Row} {id : ℕ}
    (seen : Located S π depth marked M v e) (native : Reads row v id)
    (owned : Faces s p (actualEnds S π depth marked e)) :
    ∃x,(siteNumber h (2^W) k (s x)).val=row.endpoint := by
  obtain ⟨flip,first,second,len⟩:=seen.sorted native
  rcases owned with fwd|rev
  · cases flip with
    | false => exact ⟨p.left,by simpa only [fwd,Bool.false_eq_true,ite_false] using first.symm⟩
    | true => exact ⟨p.right,by simpa only [fwd,ite_true] using first.symm⟩
  · cases flip with
    | false => exact ⟨p.right,by simpa only [rev,Bool.false_eq_true,ite_false] using first.symm⟩
    | true => exact ⟨p.left,by simpa only [rev,ite_true] using first.symm⟩

end Hierarchy.ProtocolRAM.Calendar.CatalogueRows
end

end OAI
