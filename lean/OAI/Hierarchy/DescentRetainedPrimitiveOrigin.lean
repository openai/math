import OAI.Hierarchy.DescentRetainedHomeMoverRead

namespace OAI
/-! # A retained primitive is exactly the ordinal from its earlier original rack -/
namespace Hierarchy.DescentRetainedHomeMover.Layout
open DescentSIMDLookup DescentPackedZip DescentGL DescentColonies DescentRotorWindowArchive
open DescentSixParty.PackedFlow.Channels DescentResetRetainedSetup DescentRetainedControl
open scoped Classical Fin.CommRing
noncomputable section
variable (z : DescentRetainedHomeMover.Layout)
local notation "v" => z.transfer

theorem chosen_donor (which : Fin z.shapes→Option ℕ) (Y : Fin (v).hosts→Fin (v).grouped→Cell z.control.rootWidth)
    (rows : Fin (v).channels→Fin (v).hosts→Fin (v).grouped→Cell (v).stripWord)
    (t : Fin z.shapes) (n : Fin (v).nodes) (h : Fin (v).hosts) (g : Fin (v).grouped)
    (accept : Fin (v).donors→Bool) (prior : Fin (v).donors→Fin (v).donors→Bool) (order : Fin (v).donors≃Fin (v).donors)
    (seen : filter (D:=z.degree) (L:=(v).donors) (cap:=z.cap) (which t) (Y h g)=vector accept prior)
    (comparison : ∀i j,prior i j=decide ((order i).val<(order j).val))
    (d : Fin (v).donors) (j : Fin (v).previousNodes) (here : accept d=true)
    (position : n.val=(v).offset ((v).routedWord accept prior ((v).site rows h g)) (order d)+j.val)
    (live : j.val<(v).originalCount ((v).site rows h g) d) :
    z.targetInputs which Y rows (finProdFinEquiv (n,t)) h g=(v).entry ((v).site rows h g) d j (v).occupiedField:=by
  let old:=(v).site rows h g
  let routed:=(v).routedWord accept prior old
  have rank:=(v).original_rank prior order comparison
  have word:=joined v accept prior order rank (fun i=>rows i h g)
  have count : (v).originalCount routed (order d)=(v).originalCount old d:=by
    simpa [routed,here] using (v).routed_count accept prior order rank old d
  have paid:=z.toLayout.chosen (order d) j n routed position (count.symm ▸ live)
  simp only [targetInputs,Equiv.symm_apply_apply,seen,role,DescentRetainedPrimitive.Layout.role,word]
  exact paid.trans (by simpa [routed,here] using (v).routed_entry accept prior order rank old d j (v).occupiedField)

theorem original (which : Fin z.shapes→Option ℕ) (Y : Fin (v).hosts→Fin (v).grouped→Cell z.control.rootWidth)
    (size : 2^((v).high+(v).low)=(v).groups*(v).blocks) (cut : (v).cut≤(v).high+(v).low) (L : DescentGL.Layout ((v).high+(v).low))
    (X : Fin (v).blocks→Fin (v).hosts→Fin (v).groups→Cell (v).wholeWord) (t : Fin z.shapes) (n : Fin (v).nodes)
    (h : Fin (v).hosts) (g : Fin (v).grouped) (accept : Fin (v).donors→Bool) (prior : Fin (v).donors→Fin (v).donors→Bool)
    (order : Fin (v).donors≃Fin (v).donors)
    (seen : filter (D:=z.degree) (L:=(v).donors) (cap:=z.cap) (which t) (Y h g)=vector accept prior)
    (comparison : ∀i j,prior i j=decide ((order i).val<(order j).val))
    (d : Fin (v).donors) (j : Fin (v).previousNodes) (here : accept d=true) :
    let old:=(v).site (z.oldStrips size cut L X) h g
    let idx:=(rearrange L).symm (DescentIssuedFallbackPanel.join cut g d)
    let pos:=(finProdFinEquiv.symm (Fin.cast size idx) : Fin (v).groups×Fin (v).blocks)
    n.val=(v).offset ((v).routedWord accept prior old) (order d)+j.val→j.val<(v).originalCount old d→
    z.targetInputs which Y (z.oldStrips size cut L X) (finProdFinEquiv (n,t)) h g=
      DescentOrdinaryAtomFieldRAM.ScalarOperand.take (a:=(v).bits) j (X pos.2 h pos.1):=by
  intro old idx pos position live
  rw [z.chosen_donor which Y (z.oldStrips size cut L X) t n h g accept prior order seen comparison d j here position live]
  have expanded : z.oldStrips size cut L X =
      fun j => blockValues cut ((v).before size (z.toLayout.priorValues X) j) L := rfl
  rw [expanded]
  simpa only [pos,idx,DescentRetainedPrimitive.Layout.priorValues,DescentResetRetainedSetup.Layout.sourceID,Equiv.symm_apply_apply] using
    (v).prior_digit (z.toLayout.priorValues X) size cut L h g d j (v).occupiedField

end
end Hierarchy.DescentRetainedHomeMover.Layout

end OAI
