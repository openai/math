import OAI.Hierarchy.DescentRetainedMovedRange

namespace OAI
/-! # An absent primary scalar has zero native range digits -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentSIMDLookup DescentPackedZip DescentRetainedControl DescentRotorWindowArchive
open DescentResetOperandSetup.Chart ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing BigOperators
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

theorem decoded_empty (order : Fin (L).donors≃Fin (L).donors)
    (rank : ∀d,neighbors prior d=(order d).val) (slot : Fin (L).nodes)
    (absent : (∑d,if accept d then (L).originalCount before d else 0)≤ slot.val)
    (arg : Fin (L).args) (f : Fin 3) :
    C.seven.decoded which X panels ((L).outputID 1 (page f) arg slot) t h g=0:=by
  have socket : C.seven.roster which X t h g=vector accept prior:=rfl
  have word_ : (L).site (C.seven.stripes which X panels t) h g=out:=by
    unfold DescentResetRetainedSetup.Layout.site DescentRetainedSeven.Chart.stripes
    simp only [socket]
    exact joined _ _ _ order rank _
  have restored : (∑j,(L).originalCount out j)≤ slot.val:=by
    rw [←order.sum_comp (fun j=>(L).originalCount out j)]
    simp only [(L).routed_count accept prior order rank before]
    exact absent
  have none_ : (L).root out slot.val=none:=by
    apply List.find?_eq_none.mpr
    intro d _
    have bound : (L).offset out d+(L).originalCount out d≤∑j,(L).originalCount out j:=by
      change ProtocolRAMPortRanks.«prefix» ((L).originalCount out) Fin.val d+_≤_
      rw [Nat.add_comm]
      unfold ProtocolRAMPortRanks.«prefix»
      rw [←Finset.sum_insert (show d∉Finset.univ.filter (fun e : Fin (L).donors=>e.val<d.val) by simp)]
      exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _) (by intros; omega)
    have no : ¬(L).owns out slot.val d:=fun yes=>Nat.not_lt_of_ge (bound.trans restored) yes.2
    simpa using no
  have off : (L).location out slot.val arg.val=none:=by simp [DescentResetRetainedSetup.Layout.location,none_]
  rw [decoded_output,word_]
  simp only [DescentResetRetainedSetup.Layout.decodeDigit,
    show 4≤(page f).val from Nat.le_add_right ..,true_or,or_true,ite_true]
  exact ((L).ghost _ _ _ off).1 _

end
end Hierarchy.DescentRetainedRangeDigits

end OAI
