import OAI.Computability.NearSquareRoot.ScheduleInterpreterInit

/-!
# One signed fence-installation sweep

The gauge specifies when all heads have reached their endpoints. A stationary
write updates every endpoint, after which the gauge's origin tells every head
when to halt. Each physical head can move in its own fixed direction.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.InstallPass
open IntegerMultiplication TM

variable {A I : Type}

/-- Positive heads travel right from zero and negative heads travel left. -/
def gaugePos (positive : I → Bool) (j : I) (p : ℕ) : ℤ :=
  if positive j then (p : ℤ) else -(p : ℤ)

private def atHead (f : ℤ → A) (p : ℤ) : Tape A :=
  ⟨p, fun k => f (p+k)⟩

def layout (positive : I → Bool) (f : I → ℤ → A) (p : ℕ) (q : Bool) : Config A Bool I :=
  ⟨q,fun j => atHead (f j) (gaugePos positive j p)⟩

@[simp] theorem gaugePos_zero (positive : I → Bool) (j : I) : gaugePos positive j 0 = 0 := by
  simp [gaugePos]

@[simp] theorem layout_zero_tape (positive : I → Bool) (f : I → ℤ → A) (q : Bool) (j : I) :
    (layout positive f 0 q).tape j = ⟨0,f j⟩ := by simp [layout,atHead]

def mark (positive : I → Bool) (f : I → ℤ → A) (L : ℕ) (edit : I → A → A) : I → ℤ → A :=
  fun j => Function.update (f j) (gaugePos positive j L) (edit j (f j (gaugePos positive j L)))

private def direction (outward positive : Bool) : Move :=
  if outward == positive then .right else .left

/-- The Boolean state is false on the outward scan and true on the return. -/
def rule (positive : I → Bool) (gauge : I) (stop origin : A → Bool)
    (edit : I → A → A) : Rule A Bool I := fun q heads =>
  if q then
    if origin (heads gauge) then none
    else some (true,fun j => (heads j,direction false (positive j)))
  else
    if stop (heads gauge) then some (true,fun j => (edit j (heads j),.stay))
    else some (false,fun j => (heads j,direction true (positive j)))

private theorem move (f : ℤ → A) (p : ℤ) (d : Move) :
    (atHead f p).apply (f p,d) = atHead f (p+d.shift) := by
  simp only [Tape.apply,atHead,Tape.mk.injEq,true_and]
  funext k
  split <;> congr 1 <;> omega

private theorem paint (f : ℤ → A) (p : ℤ) (z : A) :
    (atHead f p).apply (z,.stay) = atHead (Function.update f p z) p := by
  simp only [atHead,Tape.apply,Move.shift,Int.add_zero,Tape.mk.injEq,true_and]
  funext k
  by_cases h : k = 0 <;> simp [h]

private theorem reading (f : ℤ → A) (p : ℤ) : (atHead f p).view 0 = f p := by
  simp [atHead]

variable (positive : I → Bool) (gauge : I) (stop origin : A → Bool) (edit : I → A → A)
local notation "M" => rule positive gauge stop origin edit

private theorem outward (f : I → ℤ → A) (k : ℕ)
    (h : stop (f gauge (gaugePos positive gauge k)) = false) :
    advance M (layout positive f k false) = some (layout positive f (k+1) false) := by
  simp only [advance,rule,reading,layout,h,Bool.false_eq_true,ite_false,
    Option.map_some,Option.some.injEq,Config.mk.injEq,true_and]
  funext j
  simp only [move,gaugePos,direction]
  cases positive j <;> simp [Move.shift,add_comm]

private theorem outward_run (f : I → ℤ → A) (L : ℕ)
    (h : ∀ k : ℕ, k < L → stop (f gauge (gaugePos positive gauge k)) = false) :
    Trace (advance M) (layout positive f 0 false) L (layout positive f L false) := by
  induction L with
  | zero => exact .nil _
  | succ L ih =>
    exact (ih (fun j hj => h j (by omega))).trans (.single (outward positive gauge stop origin edit f L (h L (by omega))))

private theorem turn (f : I → ℤ → A) (L : ℕ) (h : stop (f gauge (gaugePos positive gauge L)) = true) :
    advance M (layout positive f L false) = some (layout positive (mark positive f L edit) L true) := by
  simp only [advance,rule,reading,layout,h,Bool.false_eq_true,ite_false,ite_true,
    Option.map_some,Option.some.injEq,Config.mk.injEq,true_and]
  funext j
  exact paint _ _ _

private theorem inbound (f : I → ℤ → A) (k : ℕ)
    (h : origin (f gauge (gaugePos positive gauge (k+1))) = false) :
    advance M (layout positive f (k+1) true) = some (layout positive f k true) := by
  simp only [advance,rule,reading,layout,h,ite_true,Bool.false_eq_true,ite_false,
    Option.map_some,Option.some.injEq,Config.mk.injEq,true_and]
  funext j
  simp only [move,gaugePos,direction]
  cases positive j <;> simp [Move.shift]

private theorem inbound_run (f : I → ℤ → A) (L : ℕ)
    (h : ∀ k : ℕ, 0 < k → k ≤ L → origin (f gauge (gaugePos positive gauge k)) = false) :
    Trace (advance M) (layout positive f L true) L (layout positive f 0 true) := by
  induction L with
  | zero => exact .nil _
  | succ L ih =>
    simpa [Nat.add_comm] using (Trace.cons (inbound positive gauge stop origin edit f L (h (L+1) (by omega) le_rfl))
      (ih (fun j hj hL => h j hj (by omega))))

/-- The two passes restore all head coordinates. The stationary endpoint edit
costs one transition, including for a sweep of length zero. -/
theorem run (f : I → ℤ → A) (L : ℕ)
    (hbefore : ∀ k : ℕ, k < L → stop (f gauge (gaugePos positive gauge k)) = false)
    (hend : stop (f gauge (gaugePos positive gauge L)) = true)
    (hback : ∀ k : ℕ, 0 < k → k ≤ L →
      origin (mark positive f L edit gauge (gaugePos positive gauge k)) = false)
    (hzero : origin (mark positive f L edit gauge (gaugePos positive gauge 0)) = true) :
    Trace (advance M) (layout positive f 0 false) (2*L+1) (layout positive (mark positive f L edit) 0 true) ∧
    advance M (layout positive (mark positive f L edit) 0 true) = none := by
  constructor
  · rw [show 2*L+1 = L+1+L by omega]
    exact ((outward_run positive gauge stop origin edit f L hbefore).trans
      (.single (turn positive gauge stop origin edit f L hend))).trans
      (inbound_run positive gauge stop origin edit _ L hback)
  · simp only [advance,rule,reading,layout,hzero,ite_true,Option.map_none]

end Uniform.InstallPass

end NearSquareRoot
end Computability
end OAI
