import OAI.Computability.VPVNP.RAMTapeSuccessorPowerBit
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord
import OAI.Computability.VPVNP.RAMTapeCeilLog
import OAI.Computability.VPVNP.RAMTapeMapWord

/-!
# Building the global cost cap on the processor's stack tape

The input parser retains the unary site logarithm `d`, bucket capacity `H`
and word width `w`. Compute `e = ⌈log₂ H⌉` on a copy of the tally, then set
bit `d+e` in a zero word. For `H = 2^e` this produces exactly the w-bit
global cost cap `SH`, and retains all the tallies needed by the site.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SuccessorParameters

open BurstRAM

/-- Unary dimensions, intermediate tally and scratch stacks, and the binary cap register used
to construct the global cost cap. -/
inductive Port where | siteLog | bucket | width | bucketLog | cap | work | tmp
  deriving DecidableEq
instance : Fintype Port := derive_fintype% _

/-- Store the site logarithm, bucket capacity, word width, bucket logarithm, and working count
in unary alongside the supplied cap bits. -/
def bank (d H w e work : ℕ) (cap : List Bool) : Stacks Port
  | .siteLog => List.replicate d true
  | .bucket => List.replicate H true
  | .width => List.replicate w true
  | .bucketLog => List.replicate e true
  | .work => List.replicate work true
  | .cap => cap
  | .tmp => []

private def logPorts : CeilLog.Port → Port
  | .src => .work
  | .tmp => .tmp
  | .out => .bucketLog

private def bitPorts : SuccessorPowerBit.Port → Port
  | .exponent => .work
  | .word => .cap
  | .tmp => .tmp

private theorem logPorts_inj : Function.Injective logPorts := by decide
private theorem bitPorts_inj : Function.Injective bitPorts := by decide

private def takeLog : FiniteRoutine Port :=
  FiniteRoutine.ofStackCode (CeilLog.code 1) logPorts .scan (· == .done)

private def addWork (src : Port) : FiniteRoutine Port :=
  SuccessorFields.prependCopy src .work .tmp

private def zeros : FiniteRoutine Port := WordCopy.mapWord .tmp .cap (fun _ ↦ false) .width

/-- One fixed table, including both the logarithm and power-bit scans. -/
def prepare : FiniteRoutine Port :=
  (((((addWork .bucket).followedBy takeLog).followedBy (addWork .siteLog)).followedBy
    (addWork .bucketLog)).followedBy zeros).followedBy (SuccessorPowerBit.routine bitPorts)

private theorem addWork_runs (d H w e m : ℕ) (cap : List Bool) (src : Port) (k : ℕ)
    (hs : src ≠ .work) (ht : src ≠ .tmp) (hk : bank d H w e m cap src = List.replicate k true) :
    (addWork src).Runs (5*k+2) (bank d H w e m cap) (bank d H w e (k+m) cap) := by
  have h := SuccessorFields.prependCopy_runs src .work .tmp hs ht (by decide) (bank d H w e m cap) rfl
  have he : Function.update (bank d H w e m cap) .work (List.replicate k true ++ List.replicate m true) =
      bank d H w e (k+m) cap := by
    funext j
    cases j <;> first | rfl | exact (List.replicate_add ..).symm
  simp only [hk, List.length_replicate] at h
  exact he ▸ h

private theorem takeLog_runs (d e w : ℕ) :
    takeLog.Runs (CeilLog.cost 1 (2^e)) (bank d (2^e) w 0 (2^e) []) (bank d (2^e) w e 0 []) := by
  have h := CeilLog.runs 1 (2^e) []
  rw [Nat.clog_pow 2 e (by decide), Nat.one_mul, List.append_nil] at h
  apply FiniteRoutine.runs_ofStackCode_framed logPorts_inj (normal := (· == .done)) rfl rfl
    (fun q he ↦ by simp only [beq_iff_eq] at he; subst q; rfl) h
  · intro j; cases j <;> rfl
  · intro j; cases j <;> rfl
  · intro j hj
    cases j <;> first | rfl | exact (hj .out rfl).elim | exact (hj .src rfl).elim

private theorem zeros_runs (d H w e m : ℕ) :
    zeros.Runs (5*w+2) (bank d H w e m []) (bank d H w e m (List.replicate w false)) := by
  have h := WordCopy.mapWord_run Port.tmp .cap (fun _ ↦ false) (src := .width) (by decide)
    (by decide) (by decide) (bank d H w e m []) rfl
  have he : Function.update (bank d H w e m []) .cap (List.replicate w false) =
      bank d H w e m (List.replicate w false) := by funext j; cases j <;> rfl
  simpa only [zeros, bank, List.length_replicate, List.map_replicate, List.reverse_replicate,
    List.append_nil, ← he] using h

/-- The global cap word with value two to the sum of the site and bucket logarithms, when its
set bit fits the width. -/
def capWord (d e w : ℕ) (h : d + e < w) : Word w :=
  ⟨2^d * 2^e, by rw [← pow_add]; exact Nat.pow_lt_pow_right (by decide) h⟩

private theorem bit_runs (d e w : ℕ) (h : d+e < w) :
    (SuccessorPowerBit.routine bitPorts).Runs (5*(d+e)+4)
      (bank d (2^e) w e (d+e) (List.replicate w false))
      (bank d (2^e) w e 0 (BurstRAM.wordBits (capWord d e w h))) := by
  apply FiniteRoutine.runs_ofStackCode_framed bitPorts_inj (normal := (· == .done)) rfl rfl
    (fun q he ↦ by simp only [beq_iff_eq] at he; subst q; rfl) (SuccessorPowerBit.run (d+e) w h)
  · intro j; cases j <;> rfl
  · intro j
    cases j <;> first | rfl | exact congrArg BurstRAM.wordBits (Fin.ext (pow_add 2 d e).symm)
  · intro j hj
    cases j <;> first | rfl | exact (hj .word rfl).elim | exact (hj .exponent rfl).elim

/-- Number of steps to construct the cap word from the site logarithm, power-of-two bucket
capacity, and word width. -/
def steps (d e w : ℕ) : ℕ :=
  5*(2^e)+2 + CeilLog.cost 1 (2^e) + (5*d+2) + (5*e+2) + (5*w+2) + (5*(d+e)+4)

theorem prepare_runs (d e w : ℕ) (h : d+e < w) :
    prepare.Runs (steps d e w) (bank d (2^e) w 0 0 [])
      (bank d (2^e) w e 0 (BurstRAM.wordBits (capWord d e w h))) := by
  have ha := addWork_runs d (2^e) w 0 0 [] .bucket (2^e) (by decide) (by decide) rfl
  have hb := takeLog_runs d e w
  have hd := addWork_runs d (2^e) w e 0 [] .siteLog d (by decide) (by decide) rfl
  have he := addWork_runs d (2^e) w e d [] .bucketLog e (by decide) (by decide) rfl
  rw [Nat.add_comm e d] at he
  exact (((((ha.followedBy hb).followedBy hd).followedBy he).followedBy
    (zeros_runs ..)).followedBy (bit_runs d e w h))

/-- Install the parameter adapter in a caller's bank. Only the two output
registers are changed, and the work and temporary stacks return empty. -/
theorem prepare_onPorts_runs {K : Type} [DecidableEq K] (ports : Port → K) (hp : Function.Injective ports)
    (s : Stacks K) (d e w : ℕ) (h : d+e < w)
    (hs : ∀ j, s (ports j) = bank d (2^e) w 0 0 [] j) :
    (prepare.onPorts ports).Runs (steps d e w) s
      (Function.update (Function.update s (ports .bucketLog) (List.replicate e true))
        (ports .cap) (BurstRAM.wordBits (capWord d e w h))) := by
  apply FiniteRoutine.runs_onPorts_framed _ hp (prepare_runs d e w h) hs
  · intro j
    cases j <;> simp [hp.eq_iff, hs, bank]
  · intro j hj
    simp [Function.update_of_ne (Ne.symm (hj .cap)), Function.update_of_ne (Ne.symm (hj .bucketLog))]

/-- Linear in the unary inputs and the word length. -/
theorem steps_le (d e w : ℕ) : steps d e w ≤ 38*(2^e)+10*(d+e)+5*w+45 := by
  have h := CeilLog.cost_le 1 (2^e)
  unfold steps
  omega

end RAMTape.SuccessorParameters

end VPVNP
end Computability
end OAI
