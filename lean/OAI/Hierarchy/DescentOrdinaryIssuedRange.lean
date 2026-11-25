import OAI.Hierarchy.DescentRangeRegisterRAM
import OAI.Hierarchy.DescentOrdinaryRetainedRangeRead

namespace OAI
/-! # Carried range field in the original ordinary date's issued numerical bank -/
namespace Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary
open DescentSIMDLookup DescentPackedColony DescentDatedAddressBook DescentDatedPriorOperand
open DescentOperandStateBanks DescentPackedOperand DescentKernelHistory DescentLocalArchiveOrder
open DescentRetainedRangeDigits DescentOrdinaryAtomFieldRAM.ScalarOperand
open Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM DescentCompiler
noncomputable section
set_option quotPrecheck false
open scoped Classical Fin.CommRing
variable {F P A : Type} [Field F] {d : ℕ} {bits : A→ℕ} {world : MarkedWorld F d A bits}
    {B : BitDescription world} (v : PhysicalOrdinary F P) {w : ℕ}
variable (floor : ℕ) (safe : v.finalChart.Early (v.finalSources floor) (v.metaEnd floor) w)
    (room : v.afterEnd floor<2^w) (m : Memory w) («meta» : v.MetaWords) (old : Books v.resolver)
    (jobs : Fin v.resolver.jobs→DescentDatedPriorOperand.Source v.resolver)
    (newRead : ∀f x,Reads (v.nodeChart.bank (v.nodeBankBase floor) f x) («meta» f x) v.resolver.lanes m)
    (spanRead : ∀x p,Reads (previousBank v.resolver (v.vectorOutput floor) x p) (old x p) v.resolver.lanes m)
    (keyRead : ∀j,Reads (Banks.wordBank v.resolver (v.normalizedEnd floor) j)
      (fun h g=>word ((jobs j).compiled h g)) v.resolver.lanes m)
variable (block : NodeOrder.All B→Fin v.resolver.blocks) (host : NodeOrder.All B→Fin v.resolver.hosts)
    (groupOf : NodeOrder.All B→Fin v.resolver.groups) (number : NodeOrder.All B→Fin v.resolver.nodes)
    (pos : 0<v.resolver.lanes) (fit : v.finalChart.field*v.resolver.nodes*v.resolver.lanes≤w)

local notation "rangePage" f:arg j:arg =>
  DescentOperandStateBanks.page (DescentRetainedRangeDigits.page f) j

private theorem unpack {a N : ℕ} (x : Cell (a*N)) (i : Fin N) :
    ((encode a N).symm x i).val=digit a i.val x.val := by
  simpa only [Equiv.apply_symm_apply] using (digit_encode ((encode a N).symm x) i).symm

include newRead spanRead keyRead fit in
theorem issued_range_at (x : NodeOrder.All B) (j : Fin v.resolver.operands) (f : Fin 3)
    :
    (DescentRetainedRangeDigits.fromRAM (B:=B) (PriorResetArchive.ordinary v floor) v.resolver v.finalChart.field
      ((v.argumentsAfter floor safe room).image m) pos block host groupOf number).word x j.val f=(take (number x) (old (block x) (rangePage f j) (host x) (groupOf x))).val := by
  let prior:=old (block x) (rangePage f j) (host x) (groupOf x)
  have read:=v.argumentsAfter_issued floor safe room m «meta» old jobs newRead spanRead keyRead (block x) (rangePage f j)
  have issued:=DescentRetainedRangeDigits.word_read (B:=B) (PriorResetArchive.ordinary v floor) v.resolver v.finalChart.field ((v.argumentsAfter floor safe room).image m) pos block host groupOf number x j f _ read fit
  have keep:=v.finalChart.span_all (DescentRetainedRangeDigits.page f) (by change 4≤4+f.val;omega) j (number x) (v.finalChart.dataAt (v.numericInputs «meta» old jobs)
        (rangePage f j) (block x) (host x) (groupOf x))
  have width : v.finalChart.field*v.resolver.nodes≤v.finalChart.scalarWidth:=
    (Nat.le_max_left ..).trans ((Nat.le_max_right ..).trans (Nat.le_max_right ..))
  have identity : ((v.finalChart.dataAt (v.numericInputs «meta» old jobs)
        (rangePage f j) (block x) (host x) (groupOf x)) (v.finalChart.columns (.inl 2))).val=prior.val := by
    simp only [DescentOrdinaryFinal.Chart.dataAt,numericInputs,Equiv.symm_apply_apply]
    change ((prior.val%(2^(v.finalChart.field*v.resolver.nodes)))%(2^v.finalChart.scalarWidth))=prior.val
    have priorFits : prior.val < 2^(v.finalChart.field*v.resolver.nodes) := prior.isLt
    rw [Nat.mod_eq_of_lt priorFits,Nat.mod_eq_of_lt (priorFits.trans_le (Nat.pow_le_pow_right (by decide : 0<2) width))]
  exact issued.trans ((unpack _ _).trans (keep.trans ((congrArg (digit v.finalChart.field (number x).val) identity).trans (unpack prior _).symm)))

include newRead spanRead keyRead fit in
theorem issued_range (x : NodeOrder.All B) (j : Fin v.resolver.operands) (f : Fin 3)
    (_live : v.finalChart.live (v.finalChart.dataAt (v.numericInputs «meta» old jobs)
        (rangePage f j) (block x) (host x) (groupOf x)) (v.finalChart.slots (number x,j))) :
    (DescentRetainedRangeDigits.fromRAM (B:=B) (PriorResetArchive.ordinary v floor) v.resolver v.finalChart.field
      ((v.argumentsAfter floor safe room).image m) pos block host groupOf number).word x j.val f=(take (number x) (old (block x) (rangePage f j) (host x) (groupOf x))).val :=
  v.issued_range_at floor safe room m «meta» old jobs newRead spanRead keyRead block host groupOf number pos fit x j f

include newRead spanRead keyRead fit in
theorem issued_padding (x : NodeOrder.All B) (j : Fin v.resolver.operands) (f : Fin 3)
    (empty_ : (take (number x) (old (block x) (rangePage f j) (host x) (groupOf x))).val=0) :
    (DescentRetainedRangeDigits.fromRAM (B:=B) (PriorResetArchive.ordinary v floor) v.resolver v.finalChart.field
      ((v.argumentsAfter floor safe room).image m) pos block host groupOf number).word x j.val f=0 :=
  (v.issued_range_at floor safe room m «meta» old jobs newRead spanRead keyRead block host groupOf number pos fit x j f).trans empty_

end
end Hierarchy.DescentSixParty.Chronology.PhysicalOrdinary

end OAI
