import OAI.Hierarchy.DescentIssuedRotationWords
import OAI.Hierarchy.DescentOrdinaryCountDates

namespace OAI
/-! # Recover every surviving count and change of basis from its dated native store -/
namespace Hierarchy.DescentSixParty.Chronology
open Computability.BorderVNP.Crossing DescentCompiler DescentGL DescentColonies DescentExterior DescentKernelHistory
open DescentTerminalEpochDecoder Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
variable {F P : Type} [Field F] [Fintype P] {d k wire hist w : ℕ} {bits:P→ℕ} {G:PoweredGadget F}
    {S:AtomSchedule} {q ε:ℝ} {I W:MarkedWorld F d P bits} {z₀ D₀ i z D:ℕ}
    {initial:Reached I G q ε S k 0 z₀ D₀ wire hist} {current:Reached W G q ε S k i z D wire hist}
    (p : Path initial current) (state : ℕ→Memory w)
    (reset : ℕ→Bool) (saved count : ℕ→ℕ) (limit : ℕ) (valid : Prop)

theorem countDates_age_lt {j start : ℕ} {tags : List Bool} (inside : j∈countDates start tags) :
    j<start+tags.length :=by
  induction tags generalizing start with
  | nil=>simp [countDates] at inside
  | cons b tail ih=>
    cases b
    · rcases List.mem_cons.mp inside with rfl|h
      · simp
      · have t:=ih h
        simp only [List.length_cons]
        omega
    · have t:=ih inside
      simp only [List.length_cons]
      omega

/-- The immediate data returned by each particular instruction. Only the first
rejected ordinary ballot and its predecessors have an observable pair count.
The final exterior matrix is used only when the whole ballot survives. -/
def Path.dateReadbacks : Prop :=by
  induction p with
  | here=>exact True
  | @ordinary _ age _ _ _ _ src prev _ he T c norm dst t ih=>
    let rot:=multiplier src.placement.fieldBits (BitDescription.scannedRows he src.placement.stage).μ
    exact ih ∧ (prev.selections.length<limit →
      state (age+1) (count age)=(selectionCount G t.selection:Computability.VPVNP.BurstRAM.Word w)) ∧
      (valid → reset age=false ∧ state (age+1) (saved age)=((matrixCode rot).val:Computability.VPVNP.BurstRAM.Word w))
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl b ih=>
    exact ih ∧ (valid → reset age=true ∧ state (age+1) (saved age)=((matrixCode b.frame.basis).val:Computability.VPVNP.BurstRAM.Word w))

omit [Fintype P] in
/-- Date-local values in the actual successive memories suffice. Off-date reads use
only the ordinary low-register frame, with its true private scalar exception. -/
theorem Path.retained_words (readbacks : p.dateReadbacks state reset saved count limit valid)
    (floors : ℕ→ℕ) (header : ℕ) (apart₁ : ∀j< i,count j≠header) (apart₂ : ∀j< i,saved j≠header)
    (below₁ : ∀j< i,∀v,i≥v→j<v→count j<floors v) (below₂ : ∀j< i,∀v,i≥v→j<v→saved j<floors v)
    (unchanged : ∀v< i,∀a,a≠header→a<floors v→state (v+1) a=state v a)
    (radix : S.radix=2^k) (elapsed : i≤S.length) (capacity : S.batch<2^w) :
    p.CountsAt count limit (state i) ∧ (valid→p.RotationWords reset saved (state i)) :=by
  induction p with
  | here=>exact ⟨Path.emptyCounts count limit _,fun _=>True.intro⟩
  | @ordinary _ age _ _ _ _ src prev _ he T c norm dst t ih=>
    have strict : age<age+1:=Nat.lt_succ_self _
    obtain ⟨counts,matrices⟩:=ih readbacks.1 (fun j h=>apart₁ j (h.trans strict))
      (fun j h=>apart₂ j (h.trans strict))
      (fun j h v hv=>below₁ j (h.trans strict) v (hv.trans strict.le))
      (fun j h v hv=>below₂ j (h.trans strict) v (hv.trans strict.le))
      (fun v h=>unchanged v (h.trans strict)) (strict.le.trans elapsed)
    have old:=prev.counts_moved count limit _ _ counts (fun j in_=>by
      have low : j<age:=by have h:=countDates_age_lt in_;rw [prev.kinds_length] at h;exact h
      exact unchanged _ strict _ (apart₁ _ (low.trans strict)) (below₁ _ (low.trans strict) _ strict.le low))
    constructor
    · apply prev.counts_ordinary t count limit _ old
      intro hit
      rw [readbacks.2.1 hit]
      have small:=(at_link G he t radix (strict.le.trans elapsed)).trans_lt capacity
      exact Nat.mod_eq_of_lt small
    · intro accepted
      refine ⟨Path.RotationWords.move prev reset saved (matrices accepted) ?_,readbacks.2.2 accepted⟩
      intro j h;exact unchanged _ strict _ (apart₂ _ (h.trans strict)) (below₂ _ (h.trans strict) _ strict.le h)
  | @reset _ age _ _ _ _ _ _ _ _ _ src prev ctl b ih=>
    have strict : age<age+1:=Nat.lt_succ_self _
    obtain ⟨counts,matrices⟩:=ih readbacks.1 (fun j h=>apart₁ j (h.trans strict))
      (fun j h=>apart₂ j (h.trans strict))
      (fun j h v hv=>below₁ j (h.trans strict) v (hv.trans strict.le))
      (fun j h v hv=>below₂ j (h.trans strict) v (hv.trans strict.le))
      (fun v h=>unchanged v (h.trans strict)) (strict.le.trans elapsed)
    have old:=prev.counts_moved count limit _ _ counts (fun j in_=>by
      have low : j<age:=by have h:=countDates_age_lt in_;rw [prev.kinds_length] at h;exact h
      exact unchanged _ strict _ (apart₁ _ (low.trans strict)) (below₁ _ (low.trans strict) _ strict.le low))
    exact ⟨prev.counts_reset b count limit _ old,fun accepted=>
      ⟨Path.RotationWords.move prev reset saved (matrices accepted) (fun j h=>
        unchanged _ strict _ (apart₂ _ (h.trans strict)) (below₂ _ (h.trans strict) _ strict.le h)),
        readbacks.2 accepted⟩⟩

end
end Hierarchy.DescentSixParty.Chronology

end OAI
