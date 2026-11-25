import OAI.Hierarchy.DescentChronologicalWordReads
import OAI.Hierarchy.DescentPhysicalDateHistory

namespace OAI
/-! # The word observations consumed by the original funded capture -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.BorderVNP.Crossing DescentCompiler DescentGL DescentColonies DescentExterior DescentKernelHistory
open DescentTerminalEpochDecoder Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section

/-- A readback depends only on the states through the attained path length. -/
theorem Path.dateReadbacks_congr {F P : Type} [Field F] [Fintype P] {d k wire hist w : ℕ}
    {bits:P→ℕ} {G:PoweredGadget F} {S:AtomSchedule} {q ε:ℝ} {I W:MarkedWorld F d P bits}
    {z₀ D₀ i z D:ℕ} {base:Reached I G q ε S k 0 z₀ D₀ wire hist}
    {last:Reached W G q ε S k i z D wire hist} (p : Path base last)
    {start stop : ℕ→Memory w} (tag : ℕ→Bool) (saved count : ℕ→ℕ) (limit : ℕ) (valid : Prop)
    (same : ∀j≤ i,stop j=start j) (read : p.dateReadbacks start tag saved count limit valid) :
    p.dateReadbacks stop tag saved count limit valid := by
  induction p with
  | here => trivial
  | @ordinary _ age _ _ _ _ src prev _ he T c norm dst tick ih =>
    obtain ⟨old,word,rotation⟩:=read
    refine ⟨ih (fun t ht=>same t (Nat.le_succ_of_le ht)) old,?_,?_⟩
    · intro active
      rw [same (age+1) le_rfl]
      exact word active
    · intro completed
      obtain ⟨kind,stored⟩:=rotation completed
      exact ⟨kind,by rw [same (age+1) le_rfl];exact stored⟩
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl b ih =>
    obtain ⟨old,rotation⟩:=read
    refine ⟨ih (fun t ht=>same t (Nat.le_succ_of_le ht)) old,?_⟩
    intro completed
    obtain ⟨kind,stored⟩:=rotation completed
    exact ⟨kind,by rw [same (age+1) le_rfl];exact stored⟩

/-- The first tape is the actual state after boot. An ordinary or reset instruction can
update the earlier header while all recorded words from preceding dates survive. -/
structure FundedDateInputs {w : ℕ} (S : AtomSchedule) (date : ℕ→DateCode w) (start : Memory w)
    (header capture roof : ℕ) (floors count saved : ℕ→ℕ) (observations : Prop) : Prop where
  run : ∀i<S.length,∀m,∃out,(date i).Runs m out
  cheap : ∀i<S.length,(date i).cheap
  order : ∀i<S.length,header<floors i
  observed : observations
  countApart : ∀i<S.length,count i≠header
  matrixApart : ∀i<S.length,saved i≠header
  countBefore : ∀j<S.length,∀i,S.length≥i→j< i→count j<floors i
  matrixBefore : ∀j<S.length,∀i,S.length≥i→j< i→saved j<floors i
  frame : ∀i<S.length,∀a,a≠header→a<floors i→DateCode.history date start (i+1) a=DateCode.history date start i a
  counts : ∀i∈countDates 0 (kindCalendar S.rounds S.height),
    capture+(countDates 0 (kindCalendar S.rounds S.height)).length≤count i ∧ count i+1<2^w
  rotationsLow : ∀i<S.length,capture+(countDates 0 (kindCalendar S.rounds S.height)).length≤ saved i
  rotationsHigh : ∀i<S.length,saved i<roof

end
end Hierarchy.DescentSixParty.Chronology

end OAI
