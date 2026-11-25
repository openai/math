import OAI.Hierarchy.DescentRegisteredWindow
import OAI.Hierarchy.DescentSelectedDateLedger
import OAI.Hierarchy.DescentPhysicalDateHistory

namespace OAI
/-! Sum the actual register-selected instruction prices and keep the single
initial native program separate from the dated maneuvers. -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open ProtocolRAM DescentCompiler TerminalScale DescentDatedAddressBook
open scoped BigOperators Classical
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {G : PoweredGadget F} {S : AtomSchedule}
    {bits : P→ℕ} {d k wire hist final w : ℕ} {q ε : ℝ} {C : Type*}
    (traces : C→RunTrace G q ε S k wire hist final bits d) {n degree : ℕ}
    (b : Menu n degree) (initial : Position)
set_option quotPrecheck false
local notation "current" i => calendar (w:=w) traces b initial i
local notation "machine" => instruction (w:=w) traces b initial

omit [Fintype P] in
/-- Charge the selected native instruction only to the existing named cut.
The public empty scan has its own measured four steps and nineteen names. -/
theorem selected_tariff (i limit : ℕ) (idle : 137*w ≤ limit)
    (actual : ∀(e : RunTrace.Events traces i) (m : Move w),issued traces b i e (current i) m→m.code.tariff ≤ limit) :
    (machine i).tariff ≤ limit :=
  CostCore.selected_tariff (issued traces b) initial i limit idle actual

omit [Fintype P] in
/-- The finite ledger includes one additional boundary index. Give it the
empty sum, since terminal replay starts after the last registered instruction. -/
theorem date_ledger (t J f g reset M τ h p high low saving : ℕ)
    (config : S=stageNumbers G t J f g reset M (tail τ J)) (positive : 0 < h)
    (host : ((S.length+1)*(high+1))*h ≤ p*2^(tail τ J))
    (items : (S.length+1)*(2^S.hostGain)^S.length*low*2^J ≤ p)
    (fees : ∀i < S.length,(machine i).tariff ≤ S.hostSize i*h*high+
      S.hostSize i*(S.groupCount i*S.radix)*low+M/(2^J)^saving) :
    (∑i∈Finset.range S.length,(machine i).tariff)*2^J ≤ 2*(M*(S.copies*p)) :=
  CostCore.date_ledger (issued traces b) initial t J f g reset M τ h p high low saving config positive host items fees

omit [Fintype P] in
/-- A single cofinal instruction estimate covers each side of the actual
public menu. Several shared table residues can be paid with the original hosts. -/
theorem funded_issue (t J f g reset M τ h ratio p lead exponent share saving : ℕ)
    (config : S=stageNumbers G t J f g reset M (tail τ J)) (positive : 0 < h)
    (sites : 0 < M) (width : w ≤ ratio*h)
    (issuedFees : ∀i < S.length,∀(e : RunTrace.Events traces i) (m : Move w),
      issued traces b i e (current i) m→m.code.tariff ≤
        S.hostSize i*h*(lead*scale J exponent)+S.hostSize i*(S.groupCount i*S.radix)*(lead*scale J exponent)+
        share*(M/(2^J)^saving)) :
    let coef:=lead+share+137*ratio
    let localRate:=coef*scale J exponent
    ((S.length+1)*(localRate+1))*h ≤ p*2^(tail τ J) →
    (S.length+1)*(2^S.hostGain)^S.length*localRate*2^J ≤ p →
    (∑i∈Finset.range S.length,(machine i).tariff)*2^J ≤ 2*(M*(S.copies*p)) :=
  CostCore.funded_issue (issued traces b) initial t J f g reset M τ h ratio p lead exponent share saving
    config positive sites width issuedFees

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
