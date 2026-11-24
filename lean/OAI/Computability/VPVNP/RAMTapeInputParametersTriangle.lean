import OAI.Computability.VPVNP.TallyStacks
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Tactic.Linarith

/-!
# Computing the triangular sorting-layer count on unary stacks

The outer counter starts at the source value. After each pop, its remaining
value is copied to the destination and one additional mark is pushed. This
adds the successive integers from the source value down to one.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace RAMTape.Tally

open Function Routine

variable {K : Type*} [DecidableEq K]

private def triangleBody (counter dst tmp : K) :=
  (copyAdd counter dst tmp).followedBy (push dst true)

private def triangleLoop (counter dst tmp : K) :=
  popLoop counter (fun _ => true) (halt false) (triangleBody counter dst tmp)

/-- Add the number of unordered pairs from `d+1` elements to the destination,
where `d` is the number of unary marks on the source stack. -/
def triangleAdd (src dst counter tmp : K) :=
  (copyAdd src counter tmp).followedBy (triangleLoop counter dst tmp)

private theorem triangleBody_runs (counter dst tmp : K) (hcd : counter ≠ dst)
    (hct : counter ≠ tmp) (hdt : dst ≠ tmp) (s : State K) (ht : s tmp = 0) :
    (triangleBody counter dst tmp).Runs (5 * s counter + 3) (encode s)
      (encode (update s dst (s dst + s counter + 1))) := by
  have hc := copyAdd_runs counter dst tmp hcd hct hdt s ht
  have hp := increment (update s dst (s dst + s counter)) dst
  simpa [triangleBody] using hc.followedBy hp

private theorem choose_succ_two (d : ℕ) : (d + 1).choose 2 = d + d.choose 2 := by
  rw [Nat.choose_succ_succ d 1, Nat.choose_one_right]

private theorem triangleLoop_runs (counter dst tmp : K) (hcd : counter ≠ dst)
    (hct : counter ≠ tmp) (hdt : dst ≠ tmp) (d : ℕ) (s : State K)
    (hd : s counter = d) (ht : s tmp = 0) :
    (triangleLoop counter dst tmp).Runs (1 + 4 * d + 5 * d.choose 2) (encode s)
      (encode (update (update s counter 0) dst (s dst + (d+1).choose 2))) := by
  induction d generalizing s with
  | zero =>
    have he := Runs.popLoop_empty counter (fun _ => true) (halt false) (triangleBody counter dst tmp)
      (s := encode s) (by simp [encode, hd])
    have hreset : update s counter 0 = s := hd ▸ update_eq_self counter s
    simpa [triangleLoop, hreset, update_eq_self] using he
  | succ d ih =>
    let popped := update s counter d
    let mid := update popped dst (s dst + d + 1)
    have hp : popped counter = d := update_self ..
    have hp' : popped dst = s dst := update_of_ne hcd.symm _ _
    have htmp : popped tmp = 0 := (update_of_ne hct.symm _ _).trans ht
    have hmid : mid counter = d := (update_of_ne hcd _ _).trans hp
    have hmidt : mid tmp = 0 := (update_of_ne hdt.symm _ _).trans htmp
    have hpop : update (encode s) counter (List.replicate d true) = encode popped :=
      encode_update s counter d
    have hb : (triangleBody counter dst tmp).Runs (5 * d + 3)
        (update (encode s) counter (List.replicate d true)) (encode mid) := by
      rw [hpop]
      simpa only [hp, hp', mid] using triangleBody_runs counter dst tmp hcd hct hdt popped htmp
    have hr := Runs.popLoop_true_continue counter (fun _ => true) (halt false)
      (triangleBody counter dst tmp) (by simp [encode, hd, List.replicate_succ]) rfl hb
      (ih mid hmid hmidt)
    have hstate : update (update mid counter 0) dst (mid dst + (d + 1).choose 2) =
        update (update s counter 0) dst (s dst + (d + 1 + 1).choose 2) := by
      funext i
      by_cases he : i = dst
      · subst i
        simp only [update_self, mid, choose_succ_two]
        omega
      · by_cases hc : i = counter
        · subst i; simp [update_of_ne hcd]
        · simp [mid, popped, update_of_ne hc, update_of_ne he]
    rw [hstate] at hr
    have hcost : 1 + (5 * d + 3) + (1 + 4 * d + 5 * d.choose 2) =
        1 + 4 * (d + 1) + 5 * (d + 1).choose 2 := by rw [choose_succ_two d]; omega
    simpa only [triangleLoop, hcost] using hr

/-- Exact deterministic tick count. The output updates only the destination. -/
theorem triangleAdd_runs (src dst counter tmp : K)
    (hsc : src ≠ counter) (hst : src ≠ tmp) (hdc : dst ≠ counter) (hdt : dst ≠ tmp)
    (hct : counter ≠ tmp) (s : State K) (hc : s counter = 0) (ht : s tmp = 0) :
    (triangleAdd src dst counter tmp).Runs (3 + 9 * s src + 5 * (s src).choose 2) (encode s)
      (encode (update s dst (s dst + (s src + 1).choose 2))) := by
  let copied := update s counter (s counter + s src)
  have ha := copyAdd_runs src counter tmp hsc hst hct s ht
  have hc' : copied counter = s src := by simp [copied, hc]
  have ht' : copied tmp = 0 := (update_of_ne hct.symm _ _).trans ht
  have hreset : update copied counter 0 = s := by
    rw [show copied = _ from rfl, update_idem, ← hc, update_eq_self]
  have hd' : copied dst = s dst := update_of_ne hdc _ _
  have hb := triangleLoop_runs counter dst tmp hdc.symm hct hdt (s src) copied hc' ht'
  rw [hreset, hd'] at hb
  have hcost : 5 * s src + 2 + (1 + 4 * s src + 5 * (s src).choose 2) =
      3 + 9 * s src + 5 * (s src).choose 2 := by omega
  simpa only [triangleAdd, hcost] using ha.followedBy hb

/-- A quadratic bound for the fixed routine, valid also on a zero source. -/
theorem triangleAdd_cost_le (d : ℕ) : 3 + 9 * d + 5 * d.choose 2 ≤ 20 * (d + 1) ^ 2 := by
  have h : d.choose 2 ≤ d * d := by
    rw [Nat.choose_two_right]
    exact (Nat.div_le_self ..).trans (Nat.mul_le_mul_left _ (Nat.sub_le ..))
  nlinarith

end RAMTape.Tally

end VPVNP
end Computability
end OAI
