import OAI.Computability.NearSquareRoot.InterchangeBQuestReindex
import OAI.Computability.NearSquareRoot.InterchangeRequestHeader
import OAI.Computability.NearSquareRoot.InterchangeLeaf

/-!
# Dispatching bounded recursive programs on the field width

The flag is read from a tagged copy of the input. The dispatcher uses one
fixed command and enters the selected branch on the original input. Its
absolute space bounds can be shared with full-volume tail calls.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Space

open IntegerMultiplication.Code

/-- Compute a branch flag on tape and enter one of two fixed bodies. -/
def dispatch (prepare low high : Cmd) : Cmd := prepare.join (decodeBit low high)

/-- The preparatory scan shares the absolute data cap with either branch.
Only its own pending return address is needed while it runs. -/
theorem BoundedFits.dispatch {env : Env} {prepare low high : Cmd} {flag : Bool} {x : Tree}
    {initial parked final : Deck} {t u cap d depth : ℕ}
    (tag : BoundedFits env prepare initial (pile 0 (.fork (.atom flag) x) parked) t cap d)
    (body : BoundedFits env (bif flag then high else low) (pile 0 x parked) final u cap depth)
    (reserve : d+1 ≤ depth) :
    BoundedFits env (Space.dispatch prepare low high) initial final (t+u+10) cap depth := by
  have valid : DeckCap cap (pile 0 (.fork (.atom flag) x) parked) := by
    obtain ⟨_,_,tagRun⟩ := tag
    exact tagRun.finish
  have result := tag.join (body.decodeBit valid (by omega)) reserve
  exact result.mono (by omega) le_rfl le_rfl

end Space

namespace InterchangeSpace

open IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom NearSquareRoot.Space

variable {I Y : Type} {job : Job Y} {w : I → ℕ} {uses : I → List Y} {p q : I → Tree}

/-- Branch programs on the two subtypes share the parent allocation and
preserve the actual ledger of the selected input. -/
theorem Body.branch (test : I → Bool)
    (flag : BoundedTask w w p (fun i => Tree.fork (.atom (test i)) (p i)))
    (low : Body job (fun i : {i // test i = false} => w i) (fun i => uses i)
      (fun i => p i) (fun i => q i))
    (high : Body job (fun i : {i // test i = true} => w i) (fun i => uses i)
      (fun i => p i) (fun i => q i)) : Body job w uses p q := by
  obtain ⟨cmd,C,prepare⟩ := flag
  obtain ⟨left,L,small⟩ := low.build
  obtain ⟨right,H,large⟩ := high.build
  refine ⟨Space.dispatch cmd left right,C+(L+H)+10,?_⟩
  intro i parent env price s d child stack base hs
  let K := C+(L+H)+10
  let cap := base+K*(w i+1)+s
  let depth := K*(w i+1)+d
  have major : C*(w i+1)+(L+H)*(w i+1)+10 ≤ K*(w i+1) := by
    dsimp only [K]
    simp only [Nat.add_mul]
    omega
  have tag := (prepare i (parent::env) stack base hs).mono le_rfl
    (show base+C*(w i+1) ≤ cap by dsimp only [cap]; omega) le_rfl
  have result :
      BoundedFits (parent::env) (bif test i then right else left)
        (pile 0 (p i) stack) (pile 0 (q i) stack)
        ((L+H)*(w i+1)+((uses i).map price).sum) cap depth := by
    cases t : test i with
    | false =>
      have main := small ⟨i,t⟩ parent env price s d child stack base hs
      dsimp only at main
      have hmax := Nat.mul_le_mul_right (w i+1) (Nat.le_add_right L H)
      exact main.mono (by omega) (by dsimp only [cap]; omega) (by dsimp only [depth]; omega)
    | true =>
      have main := large ⟨i,t⟩ parent env price s d child stack base hs
      dsimp only at main
      have hmax := Nat.mul_le_mul_right (w i+1) (Nat.le_add_left H L)
      exact main.mono (by omega) (by dsimp only [cap]; omega) (by dsimp only [depth]; omega)
  change BoundedFits _ _ _ _ (K*(w i+1)+_) cap depth
  exact (tag.dispatch result (by dsimp only [depth]; omega)).mono (by omega) le_rfl le_rfl

end InterchangeSpace

namespace InterchangeAddress.Request

open IntegerMultiplication.Code IntegerMultiplication.Strip IntegerMultiplication.Loom NearSquareRoot.Space
  NearSquareRoot.InterchangeSpace

variable {I Y : Type} {b : ℕ}

/-- A common preparatory command works with any pair of absolute-cap branch
bodies. The larger child's full data and return bounds are available as
soon as the field-width test has finished. -/
theorem prepare_width_dispatch (xs : I → Request b) (n : ℕ) {w : I → ℕ}
    (ripe : (regime xs).ripe (fun i => (w i : ℝ)))
    (stored : Volume (fun i => (w i : ℝ)) ((job b).issue ∘ xs)) :
    ∃ (prepare : Cmd) (K : ℕ), ∀ (low high : Cmd) (i : I) (env : Env) (deck : Deck)
      (base time cap depth : ℕ), DeckCap base deck →
      base + K*(w i+1) ≤ cap → K*(w i+1)+1 ≤ depth →
      ((xs i).width ≤ n → BoundedFits env low (pile 0 ((job b).issue (xs i)) deck)
        (pile 0 ((job b).reply (xs i)) deck) time cap depth) →
      (n < (xs i).width → BoundedFits env high (pile 0 ((job b).issue (xs i)) deck)
        (pile 0 ((job b).reply (xs i)) deck) time cap depth) →
      BoundedFits env (Space.dispatch prepare low high) (pile 0 ((job b).issue (xs i)) deck)
        (pile 0 ((job b).reply (xs i)) deck) (K*(w i+1)+time+10) cap depth := by
  have tagged : BoundedTask w w ((job b).issue ∘ xs) (fun i =>
      Tree.fork (.atom (decide (n < (xs i).width))) ((job b).issue (xs i))) := by
    simpa only [Nat.ceil_natCast] using carries_bounded (branch_tag xs n ripe stored)
  obtain ⟨prepare,K,exec⟩ := tagged
  refine ⟨prepare,K,?_⟩
  intro low high i env deck base time cap depth hd hc hr small large
  have prep := (exec i env deck base hd).mono le_rfl hc le_rfl
  apply prep.dispatch _ hr
  by_cases he : n < (xs i).width
  · simpa only [he, decide_true, Bool.cond_true] using large he
  · simpa only [he, decide_false, Bool.cond_false] using small (le_of_not_gt he)

/-- A bounded-width leaf inherits both of its linear resource estimates from
the volume of the live request. The command reads the supplied header. -/
theorem leaf_of_issue_volume (xs : I → Request b) (n : ℕ) {w : I → ℕ} (hb : 1 ≤ b)
    (solid : ∀ i, solidShape (xs i)) (stored : Volume (fun i => (w i : ℝ)) ((job b).issue ∘ xs)) :
    BoundedTask (fun i : {i // (xs i).width ≤ n} => w i) (fun i => w i)
      (fun i => (job b).issue (xs i)) (fun i => (job b).reply (xs i)) := by
  let leaf (i : {i // (xs i).width ≤ n}) := xs i.val
  have run := bounded_leaf_space b n hb leaf (fun i => solid i.val) (fun i => i.property)
  obtain ⟨C,hC⟩ := stored
  have major (i : {i // (xs i).width ≤ n}) :
      ((job b).issue (leaf i)).count+1 ≤ (C+1)*(w i.val+1) := by
    have hc := hC i.val
    change (((job b).issue (leaf i)).count : ℝ) ≤ (C : ℝ) * (w i.val : ℝ) at hc
    have bound : ((job b).issue (leaf i)).count ≤ C*w i.val := by exact_mod_cast hc
    exact (Nat.add_le_add_right bound 1).trans (by
      simp only [Nat.add_mul, Nat.one_mul, Nat.mul_add, Nat.mul_one]
      omega)
  exact run.bound (C+1) (C+1) major major

/-- Compute the width test of a recursive request and run the bounded leaf
or the internal body. The local allowance is integral and the emitted list
of child requests is exactly the internal branch ledger. -/
theorem branch_body (xs : I → Request b) (n : ℕ) {w : I → ℕ} {childJob : Job Y}
    (ripe : (regime xs).ripe (fun i => (w i : ℝ)))
    (stored : Volume (fun i => (w i : ℝ)) ((job b).issue ∘ xs))
    (uses : {i // n < (xs i).width} → List Y)
    (leaf : BoundedTask (fun i : {i // (xs i).width ≤ n} => w i) (fun i => w i)
      (fun i => (job b).issue (xs i)) (fun i => (job b).reply (xs i)))
    (step : Body childJob (fun i : {i // n < (xs i).width} => w i) uses
      (fun i => (job b).issue (xs i)) (fun i => (job b).reply (xs i))) :
    Body childJob w (branch_ledger xs n uses) ((job b).issue ∘ xs) ((job b).reply ∘ xs) := by
  let test (i : I) := decide (n < (xs i).width)
  have tagged : BoundedTask w w ((job b).issue ∘ xs)
      (fun i => Tree.fork (.atom (test i)) ((job b).issue (xs i))) := by
    simpa only [Nat.ceil_natCast] using carries_bounded (branch_tag xs n ripe stored)
  apply Body.branch test tagged
  · have h (i : {i // test i = false}) : ¬n < (xs i.val).width := of_decide_eq_false i.property
    let down (i : {i // test i = false}) : {i // (xs i).width ≤ n} := ⟨i.val, le_of_not_gt (h i)⟩
    simpa only [branch_ledger, h, ↓reduceDIte, down, Function.comp_def] using
      (Body.walkway (job:=childJob) (leaf.on down))
  · have h (i : {i // test i = true}) : n < (xs i.val).width := of_decide_eq_true i.property
    let up (i : {i // test i = true}) : {i // n < (xs i).width} := ⟨i.val, h i⟩
    simpa only [branch_ledger, h, ↓reduceDIte, up, Function.comp_def] using step.pull up

end InterchangeAddress.Request

end NearSquareRoot
end Computability
end OAI
