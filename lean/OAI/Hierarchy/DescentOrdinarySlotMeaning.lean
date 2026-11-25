import OAI.Hierarchy.DescentFreshRoleOccurrences
import OAI.Hierarchy.DescentRetainedRangeDigits
import OAI.Hierarchy.DescentOrdinarySliceChronology

namespace OAI
/-! # All three physical operand interval digits of an ordinary old or newborn node -/
namespace Hierarchy.DescentRetainedRangeDigits
open DescentTerminalSliceRuns DescentBundleHistory DescentLocalArchiveOrder DescentSixParty
open DescentSixParty.Chronology DescentCompiler DescentKernelHistory Computability.BorderVNP.Crossing
open scoped Classical
set_option quotPrecheck false
noncomputable section
variable {F P : Type} [Field F] {d k p R : ℕ} {bits : P→ℕ}
variable {G : PoweredGadget F} {q ε u : ℝ} {S : AtomSchedule} {i z D z' D' wire hist : ℕ}
    {W : MarkedWorld F d P bits} {cap : Reached W G q ε S k i z D wire hist}
    {he : 0≤ε} {T : StageInput W G u ε} {c : (T.result he).Choice}
    {n : Normalize ((T.result he).state c)} {target : Reached n.result G q ε S k (i+1) z' D' wire hist}
    (ticket : OrdinaryLink cap he T c n target) (arch : Archive W) (previous : WorldShape p R arch.bit)
    (hp : 0<p) (one : 1≤R) (pins : ∀v,p∣bits v) (unit : p∣T.z)
local notation "r" => BitDescription.scannedRows he T
local notation "chosen" => (ticket.advance arch).bit
local notation "post" => WorldShape.follow hp T.unitPos unit n (ticket.quantum.symm ▸ ticket.cuts)
    (WorldShape.scanned he hp one pins T previous unit c)

/-- A carried node retains every interval digit, including the padded tail.
A new role uses one whole scalar word per original paid incidence. -/
theorem ordinary_slot_meaning (x : NodeOrder.All chosen) (j : ℕ) (f : Fin 3) :
    atSlot ((post).sites x.1) x.2 j f=
      Sum.elim (fun y : NodeOrder.All arch.bit=>atSlot (previous.sites y.1) y.2 j f)
        (fun a=>(if j<DescentFreshRoleFields.arity G p T.z ((r).profile c a.1) a.2 then value whole f else 0))
        (roots ticket arch x):=by
  have original:=ordinary_fields ticket arch previous hp one pins unit x
  cases kind : roots ticket arch x with
  | inl y =>
    simp only [kind,Sum.elim_inl] at original
    exact of_fields _ _ _ _ original j f
  | inr a =>
    simp only [kind,Sum.elim_inr] at original
    unfold atSlot
    rw [←layout ((post).sites x.1) x.2]
    change ((repeatFields ((post).nodeFields x).flatten)[j]?).elim 0 (fun v=>value v f)=_
    rw [original,fresh_occurrences]
    rw [List.getElem?_replicate]
    by_cases within : j<DescentFreshRoleFields.arity G p T.z ((r).profile c a.1) a.2 <;> simp [within]
end
end Hierarchy.DescentRetainedRangeDigits

end OAI
