import OAI.Computability.VPVNP.RAMTapeSortGather
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord

/-! # Indexed sort lookup preserving the row counter

Copy the live row tally into the gather routine's private offset register
before fetching the record. The gather's width scratch is free during this
copy, and the original row tally is available to the next row instruction.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SortGather

variable {K : Type}

/-- Copy the live unary row index into private scratch before fetching the record, preserving
the caller's index for the next operation. -/
def fetchPreserving (ports : Port → K) (index : K) : FiniteRoutine K :=
  (SuccessorFields.prependCopy index (ports .offset) (ports .widthBack)).followedBy
    (fetch.onPorts ports)

variable [DecidableEq K]

theorem fetchPreserving_runs (ports : Port → K) (hp : Function.Injective ports) (index : K)
    (hdist : ∀ j, index ≠ ports j) (w i : ℕ) (s : Stacks K) (pre data tail : List Bool)
    (hpre : pre.length = i*(5*w)) (hdata : data.length = 5*w)
    (hb : s (ports .block) = pre ++ data ++ tail) (hi : s index = List.replicate i true)
    (ho : s (ports .offset) = []) (hw : s (ports .width) = List.replicate w true)
    (ht : s (ports .widthBack) = []) (hs : s (ports .saved) = []) (hr : s (ports .recordBack) = []) :
    (fetchPreserving ports index).Runs (5*i+2 + cost i w) s
      (Function.update s (ports .output) (data++s (ports .output))) := by
  let m := Function.update s (ports .offset) (List.replicate i true)
  have copy := SuccessorFields.prependCopy_runs index (ports .offset) (ports .widthBack)
    (hdist _) (hdist _) (hp.ne (by decide)) s ht
  rw [hi, ho, List.append_nil, List.length_replicate] at copy
  have neq (p : Port) (h : p ≠ .offset) : m (ports p) = s (ports p) :=
    Function.update_of_ne (hp.ne h) ..
  have run := fetch_runs w i (m ∘ ports) pre data tail hpre hdata
    ((neq _ (by decide)).trans hb) (Function.update_self ..) ((neq _ (by decide)).trans hw)
    ((neq _ (by decide)).trans ht) ((neq _ (by decide)).trans hs) ((neq _ (by decide)).trans hr)
  have lifted : (fetch.onPorts ports).Runs (cost i w) m
      (Function.update s (ports .output) (data++s (ports .output))) := by
    apply fetch.runs_onPorts_framed hp run (fun _ => rfl)
    · intro j
      cases j <;> simp [m, Function.comp_def, hp.eq_iff, ho]
    · intro j hj
      simp [m, Ne.symm (hj .output), Ne.symm (hj .offset)]
  exact FiniteRoutine.Runs.followedBy copy lifted

end RAMTape.SortGather

end VPVNP
end Computability
end OAI
