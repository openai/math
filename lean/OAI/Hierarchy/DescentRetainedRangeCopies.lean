import OAI.Hierarchy.DescentRetainedRangeDigits
import OAI.Hierarchy.DescentRetainedHomeMask
import OAI.Hierarchy.DescentOrdinaryFinalLaw

namespace OAI
/-! # The three repeated slice digits survive the two chronological gate transfers -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentSIMDLookup DescentPackedOperand DescentOperandStateBanks DescentLocalPrivateNames
open DescentBundleHistory DescentKernelHistory
noncomputable section
variable {p : ℕ} {U V : Type} {w : V→ℕ} {r : BitRecipe U V w}
variable {U' V' : Type} {w' : V'→ℕ} {r' : BitRecipe U' V' w'}

theorem ordinary_copy (B : DescentOrdinaryFinal.Chart) (f : Fin 3) (arg : Fin B.layout.operands)
    (n : Fin B.layout.nodes) (x : B.Input) (active : B.live x (B.slots (n,arg)))
    (s : Shape p r) (u : r.Node) (t : Shape p r') (v : r'.Node)
    (shape : t.sliceFields v=s.sliceFields u)
    (previous : digit B.field n.val (x (B.columns (.inl 2))).val=atSlot s u arg.val f) :
    digit B.field n.val (B.law (B.pages (page f,arg)) x).val=atSlot t v arg.val f:=by
  rw [B.span (page f) (by change 4≤4+f.val;omega) arg n x active,previous,of_fields t v s u shape]

/-- The copied node in the primary receiver occurs after only strictly earlier accepted donors. -/
theorem reset_copy (L : DescentResetRetainedSetup.Layout) (accept : Fin L.donors→Bool)
    (prior : Fin L.donors→Fin L.donors→Bool) (order : Fin L.donors≃Fin L.donors)
    (rank : ∀d,L.donorRank prior d=(order d).val) (word : Cell L.siteWord)
    (d : Fin L.donors) (n : Fin L.previousNodes) (j : Fin L.previousArgs) (f : Fin 3)
    (active : accept d=true) (live : n.val<L.originalCount word d)
    (present : j.val<(L.entry word d n L.arityField).val)
    (s : Shape p r) (u : r.Node) (t : Shape p r') (v : r'.Node)
    (shape : t.sliceFields v=s.sliceFields u)
    (previous : (L.entry word d n (L.operandField (page f) j)).val=atSlot s u j.val f) :
    let out:=L.routedWord accept prior word
    (L.rawField out (L.offset out (order d)+n.val) j.val (page f)).val=atSlot t v j.val f:=by
  dsimp only
  rw [L.routed_old_field accept prior order rank word d n j (page f) active live present,
    previous,of_fields t v s u shape]

end
end Hierarchy.DescentRetainedRangeDigits

end OAI
