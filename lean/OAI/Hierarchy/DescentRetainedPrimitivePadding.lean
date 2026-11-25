import OAI.Hierarchy.DescentRetainedPrimitiveOrigin
import OAI.Hierarchy.DescentRetainedHomePrefix

namespace OAI
/-! # Empty retained slots and the exact count of the preceding primitive register -/
namespace Hierarchy.DescentRetainedHomeMover.Layout
open DescentSIMDLookup DescentGL DescentColonies DescentRetainedControl DescentResetRetainedSetup DescentSixParty.PackedFlow.Channels
open DescentOrdinaryAtomFieldRAM
open scoped Classical Fin.CommRing
noncomputable section
variable (z : DescentRetainedHomeMover.Layout)
local notation "v" => z.transfer

theorem previous_count (size : 2^((v).high+(v).low)=(v).groups*(v).blocks) (cut : (v).cut≤(v).high+(v).low)
    (L : DescentGL.Layout ((v).high+(v).low)) (X : Fin (v).blocks→Fin (v).hosts→Fin (v).groups→Cell (v).wholeWord)
    (h : Fin (v).hosts) (g : Fin (v).grouped) (d : Fin (v).donors) (len : ℕ) (fits : len≤(v).previousNodes) :
    let idx:=(rearrange L).symm (DescentIssuedFallbackPanel.join cut g d)
    let pos:=(finProdFinEquiv.symm (Fin.cast size idx) : Fin (v).groups×Fin (v).blocks)
    (∀j : Fin (v).previousNodes,(ScalarOperand.take (a:=(v).bits) j (X pos.2 h pos.1)).val≠0 ↔ j.val<len)→
      (v).originalCount ((v).site (z.oldStrips size cut L X) h g) d=len:=by
  intro idx pos populated
  apply DescentPaidResidentCount.Reset.count_occupied v _ d len fits
  intro j
  have cell:=(v).prior_digit (z.toLayout.priorValues X) size cut L h g d j (v).occupiedField
  simp only [DescentRetainedPrimitive.Layout.priorValues,DescentResetRetainedSetup.Layout.sourceID,Equiv.symm_apply_apply] at cell
  rw [show (v).entry ((v).site (z.oldStrips size cut L X) h g) d j (v).occupiedField=ScalarOperand.take (a:=(v).bits) j (X pos.2 h pos.1) from cell]
  exact populated j

theorem past_end (word : Cell (v).siteWord) (n : Fin (v).nodes)
    (absent : ∑d,(v).originalCount word d≤n.val) : z.toLayout.choose n word=0:=by
  have none : (v).root word n.val=none:=by
    apply List.find?_eq_none.mpr
    intro d _
    have bound : (v).offset word d+(v).originalCount word d≤∑j,(v).originalCount word j:=by
      change ProtocolRAMPortRanks.«prefix» ((v).originalCount word) Fin.val d+_≤_
      rw [Nat.add_comm]
      unfold ProtocolRAMPortRanks.«prefix»
      rw [←Finset.sum_insert (show d∉Finset.univ.filter (fun e : Fin (v).donors=>e.val<d.val) by simp)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
    have no : ¬(v).owns word n.val d:=fun yes=>Nat.not_lt_of_ge (bound.trans absent) yes.2
    simpa using no
  simp [DescentRetainedPrimitive.Layout.choose,none]

theorem ghost (which : Fin z.shapes→Option ℕ) (Y : Fin (v).hosts→Fin (v).grouped→Cell z.control.rootWidth)
    (rows : Fin (v).channels→Fin (v).hosts→Fin (v).grouped→Cell (v).stripWord)
    (t : Fin z.shapes) (n : Fin (v).nodes) (h : Fin (v).hosts) (g : Fin (v).grouped)
    (accept : Fin (v).donors→Bool) (prior : Fin (v).donors→Fin (v).donors→Bool) (order : Fin (v).donors≃Fin (v).donors)
    (seen : filter (D:=z.degree) (L:=(v).donors) (cap:=z.cap) (which t) (Y h g)=vector accept prior)
    (comparison : ∀i j,prior i j=decide ((order i).val<(order j).val))
    (absent : (∑d,if accept d then (v).originalCount ((v).site rows h g) d else 0)≤n.val) :
    z.targetInputs which Y rows (finProdFinEquiv (n,t)) h g=0:=by
  let old:=(v).site rows h g
  have rank:=(v).original_rank prior order comparison
  have word:=joined v accept prior order rank (fun i=>rows i h g)
  simp only [targetInputs,Equiv.symm_apply_apply,seen,role,DescentRetainedPrimitive.Layout.role,word]
  apply z.past_end
  calc
    (∑j,(v).originalCount ((v).routedWord accept prior old) j)=∑d,(v).originalCount ((v).routedWord accept prior old) (order d):=(order.sum_comp _).symm
    _=∑d,if accept d then (v).originalCount old d else 0:=Finset.sum_congr rfl (fun d _=>(v).routed_count accept prior order rank old d)
    _≤n.val:=absent

end
end Hierarchy.DescentRetainedHomeMover.Layout

end OAI
