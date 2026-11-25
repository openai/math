import OAI.Computability.NearSquareRoot.InterchangeBQuestCore
import OAI.Computability.NearSquareRoot.InterchangeBQuestClock
import OAI.Computability.NearSquareRoot.InterchangeTailBatch
import Mathlib.Algebra.BigOperators.Ring.List

/-!
# Closing recursive calls on the bounded P192 stack machine

One fixed command serves all requests of a recursive family. The step proof
may call its body on lower-height requests with arbitrary parked decks.
The outer tie adds one transition and reuses the body's stack bounds.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeSpace

open IntegerMultiplication IntegerMultiplication.Code Space

variable {X : Type*}

/-- Close an open recursion body with exact per-instance time, data height,
and return-depth allowances. The local step pays for the recursive jumps and
for each frame still live during a child run. -/
theorem resolve_tie_exact (body : Cmd) (query reply : X → Tree)
    (time data depth height : X → ℕ) (children : X → List X)
    (order : ∀ x y, y ∈ children x → height y < height x)
    (step : ∀ x env,
      (∀ y ∈ children x, ∀ deck base, DeckCap base deck →
        BoundedFits (body :: env) body (pile 0 (query y) deck) (pile 0 (reply y) deck)
          (time y) (base + data y) (depth y)) →
      ∀ deck base, DeckCap base deck →
        BoundedFits (body :: env) body (pile 0 (query x) deck) (pile 0 (reply x) deck)
          (time x) (base + data x) (depth x)) :
    ∀ x env deck base, DeckCap base deck →
      BoundedFits env (.tie body) (pile 0 (query x) deck) (pile 0 (reply x) deck)
        (time x + 1) (base + data x) (depth x) := by
  intro x env deck base hcap
  apply BoundedFits.tie
  suffices run : ∀ z : X, ∀ d k, DeckCap k d →
      BoundedFits (body :: env) body (pile 0 (query z) d) (pile 0 (reply z) d)
        (time z) (k + data z) (depth z) from run x deck base hcap
  intro z
  induction z using (measure height).wf.induction with
  | h z ih => exact step z env fun y hy => ih y (order z y hy)

/-- Package an exact solution as a bounded task. Only the initial tie is
charged against the time increment. -/
theorem boundedTask_of_exact_run (cmd : Cmd) (query reply : X → Tree)
    (time cap depth : X → ℕ)
    (run : ∀ x env deck base, DeckCap base deck →
      BoundedFits env cmd (pile 0 (query x) deck) (pile 0 (reply x) deck)
        (time x + 1) (base + cap x) (depth x)) :
    BoundedTask time (fun x => max (cap x) (depth x)) query reply := by
  refine ⟨cmd, 1, fun x env deck base hcap => ?_⟩
  apply (run x env deck base hcap).mono
  · simp
  · simp only [Nat.one_mul]
    exact Nat.add_le_add_left ((le_max_left ..).trans (Nat.le_succ _)) _
  · simp only [Nat.one_mul]
    exact (le_max_right ..).trans (Nat.le_succ _)

open IntegerMultiplication.Loom

/-- The largest live child frame, or zero when a request is a leaf. -/
def childPeak (budget : X → ℕ) (children : List X) : ℕ :=
  children.foldr (fun y peak => max (budget y) peak) 0

theorem le_childPeak (budget : X → ℕ) {y : X} {children : List X}
    (hy : y ∈ children) : budget y ≤ childPeak budget children := by
  induction children with
  | nil => simp at hy
  | cons z rest ih =>
    change budget y ≤ max (budget z) (childPeak budget rest)
    rcases List.mem_cons.mp hy with rfl | hy
    · exact le_max_left ..
    · exact (ih hy).trans (le_max_right ..)

theorem childPeak_le (budget : X → ℕ) (children : List X) (bound : ℕ)
    (h : ∀ y ∈ children, budget y ≤ bound) : childPeak budget children ≤ bound := by
  induction children with
  | nil => exact Nat.zero_le _
  | cons z rest ih =>
    exact max_le (h z List.mem_cons_self) (ih fun y hy => h y (List.mem_cons_of_mem z hy))

open InterchangeBatch

/-- A full-stream batch calls the surrounding recursive body from underneath
its private loop. The pending headers and the single continuation are the
only local items charged on top of each child's occupied stacks. -/
theorem run_recursive_batch (header payload reply : X → Tree) (time data depth : X → ℕ)
    (parent : Cmd) (env : Env) (V cap ret : ℕ) {x y : Tree} {qs : List X}
    (chain : Chain payload reply x qs y)
    (hx : ∀ q ∈ qs, (payload q).count ≤ V) (hy : y.count ≤ V)
    (localCap : V + 100 * ((headers header qs).count + 1) ≤ cap)
    (localRet : 100 * ((headers header qs).count + 1) ≤ ret)
    (childCap : ∀ q ∈ qs, (headers header qs).count + data q ≤ cap)
    (childRet : ∀ q ∈ qs, depth q + 1 ≤ ret)
    (child : ∀ q ∈ qs, ∀ d base, DeckCap base d →
      BoundedFits (parent :: env) parent
        (pile 0 (.fork (header q) (payload q)) d) (pile 0 (reply q) d)
        (time q) (base + data q) (depth q))
    (deck : Deck) (base : ℕ) (hc : DeckCap base deck) :
    BoundedFits (parent :: env) (batch (.again 1))
      (pile 0 (.fork (headers header qs) x) deck) (pile 0 y deck)
      (((qs.map time).sum + qs.length) + 110 * ((headers header qs).count + 1))
      (base + cap) ret := by
  let H := (headers header qs).count
  have jump (q : X) (hq : q ∈ qs) (d : Deck) (b : ℕ) (hb : DeckCap b d) :
      BoundedFits (loop (.again 1) :: parent :: env) (.again 1)
        (pile 0 (.fork (header q) (payload q)) d) (pile 0 (reply q) d)
        (time q + 1) (b + childPeak data qs) (childPeak depth qs) := by
    obtain ⟨n, hn, run⟩ := (child q hq d b hb).mono le_rfl
      (Nat.add_le_add_left (le_childPeak data hq) b) (le_childPeak depth hq)
    exact ⟨1 + n, by omega, .again rfl run⟩
  have boundCap : childPeak data qs ≤ cap - H :=
    childPeak_le data qs _ fun q hq => by have := childCap q hq; dsimp only [H]; omega
  have boundRet : childPeak depth qs ≤ ret - 1 :=
    childPeak_le depth qs _ fun q hq => by have := childRet q hq; omega
  have price (l : List X) : (l.map fun q => time q + 1).sum = (l.map time).sum + l.length := by
    induction l with
    | nil => simp
    | cons z rest ih => simp only [List.map_cons, List.sum_cons, List.length_cons, ih]; omega
  have run := run_batch header payload reply (fun q => time q + 1) (.again 1) (parent :: env)
    V (childPeak data qs) (childPeak depth qs) chain hx hy jump deck base hc
  apply run.mono (by rw [price])
  · apply Nat.add_le_add_left
    exact max_le localCap (by dsimp only [H] at boundCap; omega)
  · exact max_le localRet (by omega)

open IntegerMultiplication.Strip

/-- Generate the physical header forest beside a live stream, then hand the
stream to the successive recursive calls. The header generator's clock
bounds its temporary growth only while that generator runs. -/
theorem prepared_recursive_batch {I : Type} {r : Regime I}
    (header payload reply : X → Tree) (source target : I → Tree) (uses : I → List X)
    (small : r.Small (fun i => headers header (uses i)))
    (chain : ∀ i, Chain payload reply (source i) (uses i) (target i)) :
    ∃ u : I → ℕ, Dom r.scale u ∧ ∃ (prep : Cmd) (K : ℕ),
      ∀ (i : I) (parent : Cmd) (env : Env) (time data depth : X → ℕ) (V : ℕ),
        (∀ q ∈ uses i, (payload q).count ≤ V) → (target i).count ≤ V →
        (∀ q ∈ uses i, ∀ d b, DeckCap b d →
          BoundedFits (parent :: env) parent (pile 0 (.fork (header q) (payload q)) d)
            (pile 0 (reply q) d) (time q) (b + data q) (depth q)) →
        ∀ deck base, DeckCap base deck →
          let T := K * (u i + 1)
          let H := (headers header (uses i)).count
          let input := Tree.fork (r.header i) (source i)
          BoundedFits (parent :: env) (prep.join (batch (.again 1)))
            (pile 0 input deck) (pile 0 (target i) deck)
            (T + (((uses i).map time).sum + (uses i).length + 110 * (H + 1)) + 2)
            (base + max (input.count + T) (dataSpace V H (childPeak data (uses i))))
            (max (T + 1) (returnSpace H (childPeak depth (uses i)))) := by
  obtain ⟨u, hu, headProgram⟩ := small
  obtain ⟨prep, K, hp⟩ := headProgram.left source
  refine ⟨u, hu, prep, K, ?_⟩
  intro i parent env time data depth V hv hy child deck base hc
  let T := K * (u i + 1)
  let H := (headers header (uses i)).count
  let input := Tree.fork (r.header i) (source i)
  let cap := max (input.count + T) (dataSpace V H (childPeak data (uses i)))
  let ret := max (T + 1) (returnSpace H (childPeak depth (uses i)))
  have pre := BoundedFits.of_fits (hp i (parent :: env) deck)
    (cap := base + cap) (depth := T) (fun j => ?_) le_rfl
  · have ready := run_recursive_batch header payload reply time data depth parent env V
      (dataSpace V H (childPeak data (uses i))) (returnSpace H (childPeak depth (uses i)))
      (chain i) hv hy (le_max_left ..) (le_max_left ..)
      (fun q hq => (Nat.add_le_add_left (le_childPeak data hq) H).trans (le_max_right ..))
      (fun q hq => (Nat.succ_le_succ (le_childPeak depth hq)).trans (le_max_right ..))
      child deck base hc
    have inside := ready.mono (cap' := base + cap) (depth' := ret) le_rfl (Nat.add_le_add_left (le_max_right ..) base) (le_max_right ..)
    exact pre.join inside (le_max_left ..)
  · have size := hc.pile 0 input j
    have low : input.count + T ≤ cap := le_max_left ..
    change (letters (pile 0 input deck) j).length + T ≤ base + cap
    omega

namespace Body

variable {X : Type} {job : Job X} {w : X → ℕ} {uses : X → List X}

/-- The command and its local constant are fixed before the clock and both
stack budgets are chosen. During the inductive call each child is charged
its own clock; the same frame allowance can serve all siblings. -/
theorem resolve (h : Body job w uses job.issue job.reply) (height : X → ℕ)
    (order : ∀ x y, y ∈ uses x → height y < height x) :
    ∃ (body : Cmd) (K : ℕ), ∀ (time data depth childData childDepth : X → ℕ),
      (∀ x, K * (w x + 1) + ((uses x).map time).sum ≤ time x) →
      (∀ x, K * (w x + 1) + childData x ≤ data x) →
      (∀ x, K * (w x + 1) + childDepth x ≤ depth x) →
      (∀ x y, y ∈ uses x → data y ≤ childData x) →
      (∀ x y, y ∈ uses x → depth y ≤ childDepth x) →
      ∀ x env deck base, DeckCap base deck →
        BoundedFits env (.tie body) (pile 0 (job.issue x) deck) (pile 0 (job.reply x) deck)
          (time x + 1) (base + data x) (depth x) := by
  obtain ⟨body, K, run⟩ := h.build
  refine ⟨body, K, ?_⟩
  intro time data depth childData childDepth ht hs hd childS childD
  apply resolve_tie_exact body _ _ time data depth height uses order
  intro x env ih deck base hc
  have runChild := run x body env time (childData x) (childDepth x)
    (fun y hy d k hk => (ih y hy d k hk).mono le_rfl
      (Nat.add_le_add_left (childS x y hy) k) (childD x y hy)) deck base hc
  exact runChild.mono (ht x) (by simpa [Nat.add_assoc] using Nat.add_le_add_left (hs x) base) (hd x)

/-- Independent sibling clocks add, while the largest child space suffices.
One common constant scales each recurrence once, independently of height. -/
theorem resolve_task (h : Body job w uses job.issue job.reply) (height : X → ℕ)
    (order : ∀ x y, y ∈ uses x → height y < height x) (time space : X → ℕ)
    (clock : ∀ x, w x + 1 + ((uses x).map time).sum ≤ time x)
    (frame : ∀ x, w x + 1 + childPeak space (uses x) ≤ space x) :
    BoundedTask time space job.issue job.reply := by
  obtain ⟨body, K, solve⟩ := h.resolve height order
  have localFrame (x : X) :
      K * (w x + 1) + K * childPeak space (uses x) ≤ K * space x := by
    rw [← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (frame x)
  have childFrame (x y : X) (hy : y ∈ uses x) :
      K * space y ≤ K * childPeak space (uses x) :=
    Nat.mul_le_mul_left _ (le_childPeak space hy)
  have run := solve (fun x => K * time x) (fun x => K * space x)
    (fun x => K * space x) (fun x => K * childPeak space (uses x))
    (fun x => K * childPeak space (uses x)) (fun x => ?_)
    localFrame localFrame childFrame childFrame
  · refine ⟨.tie body, K + 1, fun x env deck base hc => ?_⟩
    apply (run x env deck base hc).mono
    · simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
      omega
    · exact Nat.add_le_add_left (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)) _
    · exact Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)
  · rw [List.sum_map_mul_left, ← Nat.mul_add]
    exact Nat.mul_le_mul_left _ (clock x)

/-- Fractional contraction of the real child fares gives a recursive bounded
task at their ceiling. The clock scale is independent of the recursion depth. -/
theorem resolve_fare (h : Body job w uses job.issue job.reply) (height : X → ℕ)
    (order : ∀ x y, y ∈ uses x → height y < height x) (fare : X → ℝ) (space : X → ℕ)
    (positive : ∀ x, 0 ≤ fare x) (C ε : ℝ) (he : 0 < ε)
    (localCost : ∀ x, (w x : ℝ) + 1 ≤ C * fare x)
    (slack : ∀ x, ((uses x).map fare).sum + ε * fare x ≤ fare x)
    (frame : ∀ x, w x + 1 + childPeak space (uses x) ≤ space x) :
    BoundedTask (fun x => ⌈fare x⌉₊) space job.issue job.reply := by
  obtain ⟨D, clock⟩ := exists_floor_clock w uses fare positive C ε he localCost slack
  apply (h.resolve_task height order (fun x => ⌊(D : ℝ) * fare x⌋₊) space clock frame).bound
    (D + 1) 1
  · intro x
    have := floor_clock_le_mul_ceil D (positive x)
    simp only [Nat.add_mul, Nat.mul_add, Nat.one_mul, Nat.mul_one]
    omega
  · simp

end Body
end InterchangeSpace

end NearSquareRoot
end Computability
end OAI
