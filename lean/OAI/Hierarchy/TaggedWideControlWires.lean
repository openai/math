import OAI.Hierarchy.TaggedWideTagValidity
import OAI.Hierarchy.TaggedWideControlHeight

namespace OAI
/-! # The real control occurrence list: parent tag validity and all slices of one native memory sort -/

noncomputable section
namespace Hierarchy.Tagged.WideHost
open scoped Classical BigOperators
variable {V F : Type*} [Field F] {a h m : ℕ}

def controlRows (a h slots : ℕ) : Fin (a+1)→ℕ := Fin.cases (2^h) (fun _=>slots)
def controlSizes (a h m : ℕ) : Fin (a+1)→ℕ := Fin.cases h (fun _=>m)

theorem control_sizes (a h slots : ℕ) :
    (fun j=>controlHeight h (controlRows a h slots j))=controlSizes a h (controlHeight h slots) := by
  funext j
  refine Fin.cases ?_ (fun _=>rfl) j
  simp [controlRows,controlSizes,controlHeight,Nat.clog_pow 2 h (by decide)]

theorem control_count (h slots a : ℕ) {limit : ℝ} (tagFits : (2:ℝ)^h≤limit) (timedFits : (slots:ℝ)≤limit) :
    ∀ j,(controlRows a h slots j:ℝ)≤limit := by
  intro j
  refine Fin.cases ?_ (fun _=>timedFits) j
  simpa [controlRows] using tagFits

def controlWires (tagPort : Row h×Fin h→V) (sortPort : Fin a→Fin (pins m m)→V) :
    (j : Fin (a+1))→Fin (pins (controlSizes a h m j) (controlSizes a h m j))→V :=
  Fin.cases (permutationRead tagPort) sortPort

/-- These are the same attached sort pins used by the sorted native CPU
history, plus the one occurrence that checks authenticity of the input tag. -/
theorem control_product (tagPort : Row h×Fin h→V) (sortPort : Fin a→Fin (pins m m)→V) (x : V→Bool) :
    (∏j,coeff F (controlSizes a h m j) (controlSizes a h m j) (x ∘ controlWires tagPort sortPort j)) =
      (if Function.Bijective (fun i : Row h=> (Computability.VPVNP.RAMSerialization.wordBits h).symm
        (fun b=>x (tagPort (i,b)))) then 1 else 0) *
      ∏j,coeff F m m (x ∘ sortPort j) := by
  rw [Fin.prod_univ_succ]
  change coeff F h h (x ∘ permutationRead tagPort)*(∏j,coeff F m m (x ∘ sortPort j))=_
  rw [permutation_factor]

end Hierarchy.Tagged.WideHost

end
end OAI
