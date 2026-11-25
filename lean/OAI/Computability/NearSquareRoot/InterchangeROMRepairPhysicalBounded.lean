import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalPark
import OAI.Computability.NearSquareRoot.InterchangeROMRepairPhysicalScript

/-! # Bounded execution of the ground repair script on P192 packets -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMRepair.Physical

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  CommonRegisters Space InterchangeROM InterchangeROM.Parking

/-- Literal P192 compilation, retaining the prefix specified by each step. -/
def command (leaf : Leaf → Cmd) (ss : List Step) : Cmd :=
  ss.foldr (fun s c => (parkPrefix s.1 (leaf s.2)).join c) .pass

theorem command_within {R : ℕ} (hR : 4 ≤ R) (leaf : Leaf → Cmd) (h : ∀ a, Within R (leaf a)) (ss : List Step) :
    Within R (command leaf ss) := by
  induction ss with
  | nil => trivial
  | cons s ss ih => exact ⟨parkPrefix_within hR (h s.2) s.1, ih⟩

structure Allowance where
  time : ℕ
  cap : ℕ
  depth : ℕ

/-- The cost measures the active suffix. The clock includes every leaf once,
and the cap takes the maximum over consecutive tape configurations. -/
def stageAllowance (leaf : Leaf → List Tree → List Tree) (charge : Leaf → List Tree → Allowance)
    (h : Tree) (xs : List Tree) (s : Step) : Allowance :=
  let inner := charge s.2 (xs.drop s.1)
  let v := max (packet h xs).count (packet h (applyStep leaf xs s)).count
  let overhead := 256*(v+1)
  ⟨inner.time + s.1*overhead, inner.cap+overhead, inner.depth+overhead⟩

def allowance (leaf : Leaf → List Tree → List Tree) (charge : Leaf → List Tree → Allowance)
    (h : Tree) : List Step → List Tree → Allowance
  | [],xs => ⟨1,(packet h xs).count,0⟩
  | s::ss,xs =>
    let a := stageAllowance leaf charge h xs s
    let b := allowance leaf charge h ss (applyStep leaf xs s)
    ⟨a.time+b.time+2,max a.cap b.cap,max (a.depth+1) b.depth⟩

/-- Which inputs are covered by the individual compiled leaf implementations. -/
def Ready {E : Type} (leaf : Leaf → List E → List E) (dom : Leaf → List E → Prop) :
    List Step → List E → Prop
  | [], _ => True
  | s::ss, xs => s.1 ≤ xs.length ∧ dom s.2 (xs.drop s.1) ∧ Ready leaf dom ss (applyStep leaf xs s)

def Realizes (leaf : Leaf → List Tree → List Tree) (dom : Leaf → List Tree → Prop)
    (charge : Leaf → List Tree → Allowance) (prog : Leaf → Cmd) (h : Tree) (env : Env) : Prop :=
  ∀ s x, dom s x → ∀ r base, DeckCap base r →
    let a := charge s x
    BoundedFits env (prog s) (pile 0 (packet h x) r) (pile 0 (packet h (leaf s x)) r)
      a.time (base+a.cap) a.depth

private theorem bounded_step {leaf dom charge prog h env} (hc : Realizes leaf dom charge prog h env)
    (s : Step) (xs : List Tree) (hlen : s.1 ≤ xs.length) (hd : dom s.2 (xs.drop s.1))
    (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let a := stageAllowance leaf charge h xs s
    BoundedFits env (parkPrefix s.1 (prog s.2)) (pile 0 (packet h xs) r)
      (pile 0 (packet h (applyStep leaf xs s)) r) a.time (base+a.cap) a.depth := by
  have a := parkPrefix_linear (xs.take s.1) (xs.drop s.1) (leaf s.2 (xs.drop s.1))
    h (prog s.2) env _ _ _ (hc s.2 _ hd) r base hr
  simpa only [List.take_append_drop, List.length_take_of_le hlen, stageAllowance, applyStep, Nat.add_assoc] using a

/-- Run the compiled list on its packet with arbitrary parked background
register contents and the caller's continuation environment. -/
theorem command_bounded {leaf dom charge prog h env} (hc : Realizes leaf dom charge prog h env)
    (ss : List Step) (xs : List Tree) (ok : Ready leaf dom ss xs) (r : Deck) (base : ℕ) (hr : DeckCap base r) :
    let a := allowance leaf charge h ss xs
    BoundedFits env (command prog ss) (pile 0 (packet h xs) r)
      (pile 0 (packet h (runSteps leaf ss xs)) r) a.time (base+a.cap) a.depth := by
  induction ss generalizing xs with
  | nil => exact BoundedFits.pass (hr.pile 0 (packet h xs))
  | cons s ss ih =>
    let a := stageAllowance leaf charge h xs s
    let b := allowance leaf charge h ss (applyStep leaf xs s)
    change BoundedFits env _ _ _ (a.time+b.time+2) (base+max a.cap b.cap) (max (a.depth+1) b.depth)
    have first := bounded_step hc s xs ok.1 ok.2.1 r base hr
    have rest := ih _ ok.2.2
    have c₁ : base+a.cap ≤ base+max a.cap b.cap := Nat.add_le_add_left (le_max_left ..) _
    have c₂ : base+b.cap ≤ base+max a.cap b.cap := Nat.add_le_add_left (le_max_right ..) _
    exact (first.mono le_rfl c₁ le_rfl).join (rest.mono le_rfl c₂ (le_max_right ..)) (le_max_left ..)

/-- The leaf compiler needs to handle only the concrete arities and data
representations on which the Hermite schedule calls it. -/
structure LeafDomains {E W S : Type} (dom : Leaf → List E → Prop) (wide : W → List E)
    (short : S → List E) : Prop where
  duplicate x : dom .duplicate (wide x)
  stage x : dom .stage (wide x)
  extract x y : dom .extract (wide x ++ wide y)
  forward a b : dom .forward (short a ++ short b)
  correct a b : dom .correct (short a ++ short b)
  backward a b : dom .backward (short a ++ short b)
  restore x a b : dom .restore (wide x ++ (short a ++ short b))
  copyCube x y z : dom .copyCube ((wide x ++ wide y) ++ wide z)
  finish x y z w : dom .finish (((wide x ++ wide y) ++ wide z) ++ wide w)

theorem ready_append {E : Type} (leaf : Leaf → List E → List E) (dom : Leaf → List E → Prop)
    (a b : List Step) (x : List E) :
    Ready leaf dom (a++b) x ↔ Ready leaf dom a x ∧ Ready leaf dom b (runSteps leaf a x) := by
  induction a generalizing x with
  | nil => simp [Ready,runSteps]
  | cons s a ih => simp [Ready,runSteps,ih,and_assoc]

private structure Segment {E : Type} (leaf : Leaf → List E → List E) (dom : Leaf → List E → Prop)
    (ss : List Step) (x y : List E) : Prop where
  ready : Ready leaf dom ss x
  out : runSteps leaf ss x = y

private theorem Segment.then {E : Type} {l : Leaf → List E → List E} {dom : Leaf → List E → Prop}
    {a b : List Step} {x y z : List E} (u : Segment l dom a x y) (v : Segment l dom b y z) :
    Segment l dom (a++b) x z := by
  refine ⟨(ready_append ..).mpr ⟨u.ready, ?_⟩, ?_⟩
  · rw [u.out]; exact v.ready
  · rw [run_append,u.out,v.out]

private theorem segment_one {E : Type} {l : Leaf → List E → List E} {d : Leaf → List E → Prop}
    (pre x : List E) (n : ℕ) (hn : pre.length = n) (b : Leaf) {z : List E}
    (hx : d b x) (hz : l b x = z) : Segment l d [(n,b)] (pre++x) (pre++z) := by
  subst n
  constructor
  · simp [Ready,hx]
  · change applyStep l (pre++x) (pre.length,b) = pre++z
    rw [active_step,hz]

private theorem segment_bare {E : Type} {l : Leaf → List E → List E} {d : Leaf → List E → Prop}
    (b : Leaf) (x : List E) {z : List E} (hx : d b x) (hz : l b x = z) : Segment l d [(0,b)] x z := by
  simpa only [List.nil_append] using segment_one [] x 0 rfl b hx hz

private theorem segment_repeat {E W : Type} {l : Leaf → List E → List E} {dom : Leaf → List E → Prop}
    {enc : W → List E} (move : W → W) (step : ∀ x, l .stage (enc x) = enc (move x))
    (valid : ∀ x, dom .stage (enc x)) (pre : List E) (n : ℕ) (hn : pre.length = n)
    (k : ℕ) (x : W) :
    Segment l dom (List.replicate k (n,.stage)) (pre++enc x) (pre++enc (move^[k] x)) := by
  induction k generalizing x with
  | zero => exact ⟨trivial,rfl⟩
  | succ k ih =>
    rw [List.replicate_succ,Function.iterate_succ_apply]
    exact (segment_one pre _ n hn .stage (valid x) (step x)).then (ih (move x))

/-- The nine ordinary representation contracts imply the domain conditions
of every call, including all repeated pencil stages. -/
theorem ready_steps {E R V U L X : Type} [Field R] [Fintype V] [Fintype U] {m : ℕ}
    {l : Leaf → List E → List E} {t : Spec R V U m} {half : R}
    {tag : X → Fin m → Bool} {fw bw : (X → R) → X → R}
    {advance : Bank R L X V → Bank R L X V}
    {wide : Bank R L X V → List E} {short : Bank R L X U → List E}
    (a : LeafSemantics l t half tag fw bw advance wide short)
    {dom : Leaf → List E → Prop} (g : LeafDomains dom wide short)
    (n : ℕ) (hw : ∀ x, (wide x).length = n) (d : ℕ) (x : Bank R L X V) :
    Ready l dom (steps n d) (wide x) := by
  let P := advance^[d]
  let y := P x
  let a₁ := gather t.extract y
  let b₁ := gather t.extract x
  let a₂ := sweep fw a₁
  let b₂ := sweep fw b₁
  let a₃ := applyTag t tag false a₂ b₂
  let b₃ := applyTag t tag true a₂ b₂
  let v := sweep bw a₃
  let w := sweep bw b₃
  let e := gather t.restore w
  let f := gather t.restore v
  let head₂ := wide y ++ wide e
  let head₃ := head₂ ++ wide (P f)
  have h₂ : head₂.length = 2*n := by simp [head₂,hw,two_mul]
  have h₃ : head₃.length = 3*n := by simp [head₃,h₂,hw]; omega
  have dup := segment_bare .duplicate _ (g.duplicate x) (a.duplicate x)
  have pre := segment_repeat advance a.stage g.stage (wide x) n (hw x) d x
  have ext := segment_bare .extract _ (g.extract x y) (a.extract x y)
  have fw₁ := segment_one (wide y) _ n (hw y) .forward (g.forward a₁ b₁) (a.forward a₁ b₁)
  have fix := segment_one (wide y) _ n (hw y) .correct (g.correct a₂ b₂) (a.correct a₂ b₂)
  have bw₁ := segment_one (wide y) _ n (hw y) .backward (g.backward a₃ b₃) (a.backward a₃ b₃)
  have rest := segment_bare .restore _ (g.restore y v w) (a.restore y v w)
  have pred := segment_repeat advance a.stage g.stage head₂ (2*n) h₂ d f
  have copy := segment_bare .copyCube _ (g.copyCube y e (P f)) (a.copyCube y e (P f))
  have cube := segment_repeat advance a.stage g.stage head₃ (3*n) h₃ (2*d) y
  have endRow := segment_bare .finish _ (g.finish y e (P f) (advance^[2*d] y))
    (a.finish y e (P f) (advance^[2*d] y))
  have cert := dup.then (pre.then (ext.then (fw₁.then (fix.then (bw₁.then (rest.then
    (pred.then (copy.then (cube.then endRow)))))))))
  simpa only [steps, List.append_assoc, List.cons_append, List.nil_append] using cert.ready

end InterchangeROMRepair.Physical

end NearSquareRoot
end Computability
end OAI
