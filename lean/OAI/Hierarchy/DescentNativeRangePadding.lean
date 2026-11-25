import OAI.Hierarchy.DescentRetainedMovedRange

namespace OAI
/-! # Native out-of-arity words in ordinary and reset retention -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentSIMDLookup DescentPackedZip DescentRetainedControl DescentRotorWindowArchive
open DescentResetOperandSetup.Chart ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable (C : DescentResetOperandSetup.Chart)
local notation "L" => C.retained
variable (which : C.seven.control.Targets) (X : C.seven.Packets) (panels : C.retained.Strips)
variable (t : Fin C.placement.shapes) (h : Fin C.retained.hosts) (g : Fin C.retained.grouped)
local notation "unpack" => (encode C.seven.packetBits (count C.seven.degree (L).donors C.seven.capacity)).symm (X h g)
local notation "accept" => ownerAt C which X t h g
local notation "prior" => priorAt C X h g
local notation "before" => (L).site panels h g
local notation "out" => (L).routedWord accept prior before

/-- The real routed arity cuts off every higher argument in both summands of the old-page decoder,
including indices beyond the physically allocated predecessor argument page. -/
theorem decoded_padding (mode : Fin 2) (order : Fin (L).donors≃Fin (L).donors)
    (rank : ∀d,neighbors prior d=(order d).val) (d : Fin (L).donors) (n : Fin (L).previousNodes)
    (active : accept d=true) (valid : n.val<(L).originalCount before d)
    (slot : Fin (L).nodes) (number : slot.val=(L).offset out (order d)+n.val)
    (operand : Fin (L).args) (past : ((L).entry before d n (L).arityField).val≤operand.val) (f : Fin 3) :
    C.seven.decoded which X panels ((L).outputID mode (page f) operand slot) t h g=0 := by
  have socket : C.seven.roster which X t h g=vector accept prior:=rfl
  have word_ : (L).site (C.seven.stripes which X panels t) h g=out:=by
    unfold DescentResetRetainedSetup.Layout.site DescentRetainedSeven.Chart.stripes
    simp only [socket]
    exact joined _ _ _ order rank _
  have alive : n.val<(L).originalCount out (order d):=by
    simpa only [(L).routed_count accept prior order rank before,active,ite_true] using valid
  have off : ¬operand.val<((L).entry out (order d) n (L).arityField).val:=by
    simpa only [(L).routed_entry accept prior order rank before,active,ite_true] using Nat.not_lt.mpr past
  have none_ : (L).location out ((L).offset out (order d)+n.val) operand.val=none:=by
    by_cases room : operand.val<(L).previousArgs <;>
      simp [DescentResetRetainedSetup.Layout.location,(L).root_at out (order d) n.val alive,
        n.isLt,room,off]
  rw [decoded_output,word_]
  simp only [DescentResetRetainedSetup.Layout.decodeDigit,
    show 4≤(page f).val from Nat.le_add_right ..,true_or,or_true,ite_true,number]
  exact ((L).ghost _ _ _ none_).1 _

end
end Hierarchy.DescentRetainedRangeDigits

end OAI
