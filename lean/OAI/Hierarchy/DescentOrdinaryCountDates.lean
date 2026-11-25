import OAI.Hierarchy.DescentChronologicalGrains
import OAI.Hierarchy.DescentTerminalEpochCapacity
import OAI.Hierarchy.DescentLowCountBook

namespace OAI
/-! # Transfer the attained ordinary pair counts in selector order, skipping reset dates -/
namespace Hierarchy.DescentSixParty.Chronology
open DescentCompiler DescentTerminalEpochDecoder Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section

/-- The public stage addresses corresponding to the ordinary selector ordinals. -/
def countDates (start : ℕ) : List Bool → List ℕ
  | []=>[]
  | true::rest=>countDates (start+1) rest
  | false::rest=>start::countDates (start+1) rest

theorem countDates_append (start : ℕ) (a b : List Bool) :
    countDates start (a++b)=countDates start a++countDates (start+a.length) b :=by
  induction a generalizing start with
  | nil=>simp [countDates]
  | cons flag rest ih=>
    cases flag <;> simp [countDates,ih,Nat.add_comm,Nat.add_left_comm]

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {G : PoweredGadget F}
    {q ε u : ℝ} {S : AtomSchedule} {k wire hist : ℕ}
variable {W₀ W₁ : MarkedWorld F d P bits} {i₀ z₀ D₀ i z D : ℕ}
variable {first : Reached W₀ G q ε S k i₀ z₀ D₀ wire hist}
    {last : Reached W₁ G q ε S k i z D wire hist}

/-- These are actual date ordinals, before any graph-dependent choices. -/
theorem Path.countDates_length (p : Path first last) :
    (countDates i₀ p.kinds).length=p.selections.length :=by
  induction p with
  | here=>rfl
  | ordinary prev ticket ih=>
    change (countDates i₀ (prev.kinds ++ [false])).length = (prev.selections ++ [ticket.selection]).length
    simp [countDates_append, countDates, ih]
  | reset prev step ih=>
    change (countDates i₀ (prev.kinds ++ [true])).length = prev.selections.length
    simp [countDates_append, countDates, ih]

/-- Only reached observations through the first bad proposal are consumed by the
physical verifier. Later memory may depend arbitrarily on its malformed bits. -/
def Path.CountsAt (p : Path first last) (count : ℕ → ℕ) (limit : ℕ) {w : ℕ} (m : Memory w) : Prop :=
  ∀j<limit,∀v,p.selections[j]?=some v →
    ∀a,(countDates i₀ p.kinds)[j]?=some a → (m (count a)).val=selectionCount G v

theorem Path.emptyCounts (count : ℕ → ℕ) (limit : ℕ) {w : ℕ} (m : Memory w) :
    (Path.here (start:=first)).CountsAt count limit m :=by
  intro j _ v hit
  simp [selections] at hit

theorem Path.counts_moved (p : Path first last) (count : ℕ → ℕ) (limit : ℕ) {w : ℕ} (m out : Memory w)
    (old : p.CountsAt count limit m)
    (retained : ∀a∈countDates i₀ p.kinds,out (count a)=m (count a)) :
    p.CountsAt count limit out :=by
  intro j reached v selected a date
  rw [retained a (List.mem_of_getElem? date)]
  exact old j reached v selected a date

theorem Path.counts_ordinary (p : Path first last) {he : 0≤ε} {T : StageInput W₁ G u ε}
    {c : (T.result he).Choice} {norm : Normalize ((T.result he).state c)} {z' D' : ℕ}
    {target : Reached norm.result G q ε S k (i+1) z' D' wire hist}
    (step : OrdinaryLink last he T c norm target) (count : ℕ → ℕ) (limit : ℕ) {w : ℕ} (m : Memory w)
    (earlier : p.CountsAt count limit m)
    (actual : p.selections.length<limit → (m (count i)).val=selectionCount G step.selection) :
    (p.ordinary step).CountsAt count limit m :=by
  intro j reached v selected a dated
  change (p.selections++[step.selection])[j]?=some v at selected
  change (countDates i₀ (p.kinds++[false]))[j]?=some a at dated
  rw [countDates_append,p.kinds_length] at dated
  change (countDates i₀ p.kinds++[i])[j]?=some a at dated
  by_cases before:j<p.selections.length
  · rw [List.getElem?_append_left before] at selected
    rw [List.getElem?_append_left (p.countDates_length.symm ▸ before)] at dated
    exact earlier j reached v selected a dated
  · rw [List.getElem?_append_right (Nat.le_of_not_gt before)] at selected
    rw [List.getElem?_append_right (p.countDates_length.symm ▸ (Nat.le_of_not_gt before)),p.countDates_length] at dated
    cases h:j-p.selections.length with
    | zero=>
      have time : j=p.selections.length:=by omega
      simp only [h,List.getElem?_cons_zero,Option.some.injEq] at selected dated
      simpa only [←selected,←dated] using actual (time ▸ reached)
    | succ t=>simp [h] at selected

theorem Path.counts_reset (p : Path first last) {n h C f g cut tail : ℕ}
    {ctl : ResetRates G S k D n h C f g cut tail} (reset : ClosedReset last ctl)
    (count : ℕ → ℕ) (limit : ℕ) {w : ℕ} (m : Memory w) (earlier : p.CountsAt count limit m) :
    (p.reset reset).CountsAt count limit m :=by
  intro j reached v selected a dated
  change (countDates i₀ (p.kinds++[true]))[j]?=some a at dated
  rw [countDates_append] at dated
  simp only [countDates,List.append_nil] at dated
  exact earlier j reached v selected a dated

/-- The final paid low-copy program delivers the precise verifier input, on the
same RAM state, for all real chronological observations that it can reach. -/
theorem Path.copy_counts (p : Path first last) (location : ℕ → ℕ) (limit firstLow : ℕ) {w : ℕ} (m : Memory w)
    (old : p.CountsAt location limit m) (publicTags : List Bool) (same : p.kinds=publicTags)
    (above : ∀a∈countDates i₀ publicTags,firstLow+p.selections.length≤location a) :
    let dates:=countDates i₀ publicTags
    let src:=fun j=>location (dates[j]?.getD 0)
    ∀j<limit,∀v,p.selections[j]?=some v →
      (DescentLowCountBook.output firstLow src m dates.length (firstLow+j)).val=selectionCount G v :=by
  subst publicTags
  intro dates src j used v present
  have bound : j<p.selections.length:=by
    by_contra! bad
    rw [List.getElem?_eq_none (by omega)] at present
    contradiction
  have inside : j<dates.length:=p.countDates_length.symm ▸ bound
  let a:=dates[j]
  have found : dates[j]?=some a:=List.getElem?_eq_getElem inside
  have real (k : ℕ) (hk : k<dates.length) : firstLow+dates.length≤ src k:=by
    rw [show dates.length=p.selections.length from p.countDates_length]
    have here:=List.getElem?_eq_getElem (l:=dates) hk
    simpa only [src,here,Option.getD_some] using above dates[k] (List.getElem_mem hk)
  have get:=DescentLowCountBook.read firstLow src m dates.length real ⟨j,inside⟩
  change (DescentLowCountBook.output firstLow src m dates.length (firstLow+j)).val=_
  rw [get]
  simpa only [src,found,Option.getD_some] using old j used v present a found

end
end Hierarchy.DescentSixParty.Chronology

end OAI
