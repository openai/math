import OAI.Computability.VPVNP.RAMTapeMapWord
import OAI.Computability.VPVNP.RAMTapeSiteEndpointTrim
import OAI.Computability.VPVNP.RAMTapeSiteEndpointWords
import OAI.Computability.VPVNP.RAMTapeSuccessorRecord
import OAI.Computability.VPVNP.RAMTapeWordOperands

/-!
# Computing the two physical cost endpoints from the site address

Allocate a zero word and remove the public number of cells reserved for the
address and low shift bits. Prepend the address, copy and increment the
padded word, then prepend the low zero bits to both results.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.SiteEndpoints

open BurstRAM TapeWord

/-- Ports for the site address, address and bucket exponents, word width, two cost endpoints,
and trimming scratch. -/
inductive Port where | address | siteLog | bucketLog | width | startCost | endCost | count | tmp
  deriving DecidableEq
instance : Fintype Port := derive_fintype% _

private def incPorts : ScanPort → Port
  | .left => .startCost
  | .right => .count
  | .tmp => .tmp
  | .out => .endCost

private theorem incPorts_inj : Function.Injective incPorts := by decide

private def incBit (carry b : Bool) := (b ^^ carry, b && carry)

private theorem emitted_inc (carry : Bool) (xs : List Bool) :
    Operand.emitted incBit carry xs = UnaryWord.incScan carry xs := by
  induction xs generalizing carry with
  | nil => rfl
  | cons b xs ih => simp [Operand.emitted, incBit, UnaryWord.incScan, ih]

private def done : Operand.State Bool → Bool
  | .done _ => true
  | _ => false

private def incrementCopy : FiniteRoutine Port :=
  FiniteRoutine.ofStackCode (Operand.code incBit) incPorts (.clear true) done

private theorem incrementCopy_runs (s : Stacks Port) (hc : s .count = []) (ht : s .tmp = []) :
    incrementCopy.Runs ((s .endCost).length + 7*(s .startCost).length+3) s
      (Function.update s .endCost (UnaryWord.incScan true (s .startCost)).1) := by
  have h := Operand.run incBit true (s .startCost) (s .endCost)
  rw [emitted_inc] at h
  apply FiniteRoutine.runs_ofStackCode_framed incPorts_inj (normal := done) rfl rfl
    (fun q hn => by cases q <;> first | rfl | contradiction) h
  · intro k
    cases k <;> first | rfl | exact hc | exact ht
  · intro k
    cases k <;> first | rfl | exact hc | exact ht
  · intro k hk
    exact Function.update_of_ne (Ne.symm (hk .out)) ..

private def zeros (src dst : Port) := WordCopy.mapWord .tmp dst (fun _ => false) src

private theorem zeros_runs (src dst : Port) (ht : src ≠ .tmp) (hd : src ≠ dst) (hu : .tmp ≠ dst)
    (s : Stacks Port) (hs : s .tmp = []) :
    (zeros src dst).Runs (5*(s src).length+2) s
      (Function.update s dst (List.replicate (s src).length false ++ s dst)) := by
  simpa only [zeros, List.map_const', List.reverse_replicate] using
    WordCopy.mapWord_run Port.tmp dst (fun _ => false) ht hd hu s hs

private def copy (src dst : Port) := SuccessorFields.prependCopy src dst .tmp

private theorem copy_runs (src dst : Port) (hd : src ≠ dst) (hs : src ≠ .tmp) (ht : dst ≠ .tmp)
    (s : Stacks Port) (h : s .tmp = []) :
    (copy src dst).Runs (5*(s src).length+2) s (Function.update s dst (s src ++ s dst)) :=
  SuccessorFields.prependCopy_runs src dst .tmp hd hs ht s h

private def localPrepare : FiniteRoutine Port :=
  (((((((zeros .width .startCost).followedBy (copy .siteLog .count)).followedBy
    (copy .bucketLog .count)).followedBy (SiteEndpointTrim.routine .count .startCost)).followedBy
    (copy .address .startCost)).followedBy incrementCopy).followedBy
    (zeros .bucketLog .startCost)).followedBy (zeros .bucketLog .endCost)

/-- One finite instruction table for every width, site count and bucket size. -/
def prepare {K : Type} (ports : Port → K) := localPrepare.onPorts ports

/-- Step count for allocating, trimming, incrementing, and shifting the two padded
cost-endpoint words. -/
def steps (d e w : ℕ) :=
  (5*w+2)+(5*d+2)+(5*e+2)+(3*(d+e)+1)+(5*d+2)+(7*(w-e)+3)+(5*e+2)+(5*e+2)

theorem steps_le (d e w : ℕ) (h : d+e < w) : steps d e w ≤ 25*w+16 := by
  unfold steps
  omega

private abbrev marks (n : ℕ) := List.replicate n true
private abbrev zeroBits (n : ℕ) := List.replicate n false

private def bank (address : List Bool) (d e w n : ℕ) (low high : List Bool) : Stacks Port
  | .address => address
  | .siteLog => marks d
  | .bucketLog => marks e
  | .width => marks w
  | .count => marks n
  | .tmp => []
  | .startCost => low
  | .endCost => high

private theorem write_count (address : List Bool) (d e w n : ℕ) (low high : List Bool) (m : ℕ) :
    Function.update (bank address d e w n low high) .count (marks m) = bank address d e w m low high := by
  funext j; cases j <;> rfl

private theorem write_low (address : List Bool) (d e w n : ℕ) (low high xs : List Bool) :
    Function.update (bank address d e w n low high) .startCost xs = bank address d e w n xs high := by
  funext j; cases j <;> rfl

private theorem write_high (address : List Bool) (d e w n : ℕ) (low high xs : List Bool) :
    Function.update (bank address d e w n low high) .endCost xs = bank address d e w n low xs := by
  funext j; cases j <;> rfl

private theorem local_prepare_runs {d : ℕ} (v : Word d) (e w : ℕ) (hf : d+e < w) :
    localPrepare.Runs (steps d e w) (bank (wordBits v) d e w 0 [] [])
      (bank (wordBits v) d e w 0 (wordBits (startWord e w v hf)) (wordBits (endWord e w v hf))) := by
  let st := bank (wordBits v) d e w
  let pad := zeroBits (w-(d+e))
  let x := padded e w v
  let y := (UnaryWord.incScan true x).1
  have z := zeros_runs .width .startCost (by decide) (by decide) (by decide) (st 0 [] []) rfl
  change (zeros ..).Runs (5*(marks w).length+2) _ (Function.update (st 0 [] []) .startCost
    (zeroBits (marks w).length ++ [])) at z
  rw [List.length_replicate, List.append_nil, write_low] at z
  have c₁ := copy_runs .siteLog .count (by decide) (by decide) (by decide) (st 0 (zeroBits w) []) rfl
  change (copy ..).Runs (5*(marks d).length+2) _ (Function.update (st 0 (zeroBits w) []) .count
    (marks d ++ [])) at c₁
  rw [List.length_replicate, List.append_nil, write_count] at c₁
  have c₂ := copy_runs .bucketLog .count (by decide) (by decide) (by decide) (st d (zeroBits w) []) rfl
  change (copy ..).Runs (5*(marks e).length+2) _ (Function.update (st d (zeroBits w) []) .count
    (marks e ++ marks d)) at c₂
  rw [List.length_replicate, show marks e ++ marks d = marks (d+e) by rw [← List.replicate_add, Nat.add_comm],
    write_count] at c₂
  have hwidth : zeroBits w = zeroBits (d+e) ++ pad := by
    rw [← List.replicate_add, show d+e+(w-(d+e)) = w by omega]
  have tr := SiteEndpointTrim.run (count := Port.count) (dst := .startCost) (by decide)
    (st (d+e) (zeroBits w) []) (d+e) pad rfl hwidth
  change (SiteEndpointTrim.routine ..).Runs _ _
    (Function.update (Function.update (st (d+e) (zeroBits w) []) .count (marks 0)) .startCost pad) at tr
  rw [write_count, write_low] at tr
  have addr := copy_runs .address .startCost (by decide) (by decide) (by decide) (st 0 pad []) rfl
  change (copy ..).Runs (5*(wordBits v).length+2) _ (Function.update (st 0 pad []) .startCost x) at addr
  rw [length_wordBits, write_low] at addr
  have inc := incrementCopy_runs (st 0 x []) rfl rfl
  change incrementCopy.Runs (0+7*x.length+3) _ (Function.update (st 0 x []) .endCost y) at inc
  rw [Nat.zero_add, padded_length _ _ _ hf, write_high] at inc
  have low := zeros_runs .bucketLog .startCost (by decide) (by decide) (by decide) (st 0 x y) rfl
  change (zeros ..).Runs (5*(marks e).length+2) _ (Function.update (st 0 x y) .startCost
    (zeroBits (marks e).length ++ x)) at low
  rw [List.length_replicate, start_bits _ _ _ hf, write_low] at low
  have high := zeros_runs .bucketLog .endCost (by decide) (by decide) (by decide)
    (st 0 (wordBits (startWord e w v hf)) y) rfl
  change (zeros ..).Runs (5*(marks e).length+2) _ (Function.update _ .endCost
    (zeroBits (marks e).length ++ y)) at high
  rw [List.length_replicate, end_bits _ _ _ hf, write_high] at high
  exact ((((((z.followedBy c₁).followedBy c₂).followedBy tr).followedBy addr).followedBy inc).followedBy
    low).followedBy high

/-- Compute both cost words, preserve the address and public counters, and
return both scratch stacks empty. The last site's end word is the global cap. -/
theorem prepare_runs {K : Type} [DecidableEq K] {d : ℕ} (ports : Port → K) (hp : Function.Injective ports)
    (s : Stacks K) (v : Word d) (e w : ℕ) (hf : d+e < w)
    (hv : s (ports .address) = wordBits v) (hd : s (ports .siteLog) = List.replicate d true)
    (he : s (ports .bucketLog) = List.replicate e true) (hw : s (ports .width) = List.replicate w true)
    (hstart : s (ports .startCost) = []) (hend : s (ports .endCost) = [])
    (hc : s (ports .count) = []) (ht : s (ports .tmp) = []) :
    (prepare ports).Runs (steps d e w) s (Function.update (Function.update s (ports .startCost)
      (wordBits (startWord e w v hf))) (ports .endCost) (wordBits (endWord e w v hf))) := by
  apply FiniteRoutine.runs_onPorts_framed localPrepare hp (local_prepare_runs v e w hf)
  · intro p
    cases p <;> assumption
  · intro p
    cases p <;> simp [bank, hp.eq_iff, hv, hd, he, hw, hc, ht]
  · intro p h
    rw [Function.update_of_ne (Ne.symm (h .endCost)), Function.update_of_ne (Ne.symm (h .startCost))]

end RAMTape.SiteEndpoints

end VPVNP
end Computability
end OAI
