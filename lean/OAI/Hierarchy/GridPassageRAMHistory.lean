import OAI.Hierarchy.GridPassageRAMState
import Mathlib.Logic.Equiv.Fin.Basic
import Mathlib.Tactic.Linarith

namespace OAI
/-! # Prefix invariants for the physical first-passage counters, marks and chosen slots -/

namespace Hierarchy.GridPassageRAMRow
open Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing

/-- The counter and output-address columns are dense. All immutable inputs lie below `counter`. -/
structure Columns where
  counter : ℕ
  chosen : ℕ
  mark : ℕ

structure Columns.Separated (c : Columns) (bins B : ℕ) : Prop where
  counts : c.counter + bins ≤ c.chosen
  choices : c.chosen + bins*B ≤ c.mark

/-- `prior key active b i` counts visits to bucket `b` strictly before candidate `i`. -/
def prior (key : ℕ → ℕ) (active : ℕ → Bool) (b : ℕ) : ℕ → ℕ
  | 0 => 0
  | i+1 => prior key active b i + if active i = true ∧ key i = b then 1 else 0

theorem prior_mono (key : ℕ → ℕ) (active : ℕ → Bool) (b : ℕ) : Monotone (prior key active b) :=
  monotone_nat_of_le_succ (fun i => by simp [prior])

private theorem slot_eq {x y a b B : ℕ} (ha : a < B) (hb : b < B) (h : x*B+a=y*B+b) : x=y ∧ a=b := by
  let m := x+y+1
  let u : Fin m × Fin B := (⟨x,by dsimp [m]; omega⟩,⟨a,ha⟩)
  let v : Fin m × Fin B := (⟨y,by dsimp [m]; omega⟩,⟨b,hb⟩)
  have same : finProdFinEquiv u = finProdFinEquiv v := Fin.ext (by
    change a+B*x=b+B*y
    simpa only [Nat.mul_comm, Nat.add_comm] using h)
  have eq := finProdFinEquiv.injective same
  exact ⟨congrArg (fun z : Fin m × Fin B => z.1.val) eq, congrArg (fun z : Fin m × Fin B => z.2.val) eq⟩

private theorem slot_lt {x a bins B : ℕ} (hx : x < bins) (ha : a < B) : x*B+a < bins*B :=
  (Nat.add_lt_add_left ha _).trans_le <| (Nat.succ_mul x B).symm.le.trans (Nat.mul_le_mul_right B hx)

def selected (B : ℕ) (key : ℕ → ℕ) (active : ℕ → Bool) (i : ℕ) : Prop :=
  active i = true ∧ prior key active (key i) i < B

/-- These observations describe every counter, every occupied chosen slot, the mark for every earlier
candidate, and the exact contents of the immutable part of memory. -/
structure StateOK {w : ℕ} (cols : Columns) (bins B : ℕ) (key rail : ℕ → ℕ) (active : ℕ → Bool)
    (initial m : Memory w) (i : ℕ) : Prop where
  counter : ∀ b < bins, (m (cols.counter+b)).val = min B (prior key active b i)
  chosen : ∀ s < i, selected B key active s →
    m (cols.chosen+key s*B+prior key active (key s) s) = (rail s : Word w)
  mark : ∀ s < i, m (cols.mark+s) = if selected B key active s then 1 else 0
  input : ∀ addr < cols.counter, m addr = initial addr
  above : ∀ addr, cols.mark+i ≤ addr → m addr = initial addr

/-- Zero counters suffice at the start. Chosen slots and marks are first written on demand. -/
theorem StateOK.zero {w bins B : ℕ} {c : Columns} {key rail : ℕ → ℕ} {active : ℕ → Bool}
    {input m : Memory w} (zero : ∀ b < bins, m (c.counter+b) = 0) (keep : ∀ a < c.counter, m a = input a)
    (high : ∀ a, c.mark ≤ a → m a = input a) :
    StateOK c bins B key rail active input m 0 := by
  refine ⟨fun b hb => by simp [zero b hb,prior], by simp, by simp, keep, by simpa using high⟩

/-- A physical write increments only its selected counter and never destroys an earlier chosen slot. -/
theorem StateOK.step {w bins B i : ℕ} {c : Columns} {key rail : ℕ → ℕ} {active : ℕ → Bool}
    {input m : Memory w} (old : StateOK c bins B key rail active input m i)
    (sep : c.Separated bins B) (fits : B < 2^w) (here : key i < bins)
    (bounds : ∀ s < i, key s < bins) :
    StateOK c bins B key rail active input
      (natStep c.counter c.chosen c.mark B (key i) (rail i) i (active i) m) (i+1) := by
  classical
  let b := key i
  let r := prior key active b i
  have hb : b < bins := here
  have count := old.counter b hb
  have nonempty : 0 < bins := Nat.zero_lt_of_lt here
  have region₁ := sep.counts
  have region₂ := sep.choices
  have selected_iff : (active i = true ∧ (m (c.counter+b)).val < B) ↔ selected B key active i := by
    simp [selected, count,b,min_lt_iff]
  by_cases take : selected B key active i
  · have act := take.1
    have hr := take.2
    change r < B at hr
    have before : (m (c.counter+b)).val = r := by rw [count]; exact Nat.min_eq_right hr.le
    have small : b*B+r < bins*B := slot_lt hb hr
    have choice_lt : c.chosen+b*B+r < c.mark := by omega
    have after_mem : natStep c.counter c.chosen c.mark B (key i) (rail i) i (active i) m =
        Function.update (Function.update (Function.update m (c.chosen+b*B+r) (rail i : Word w))
          (c.counter+b) ((r+1:ℕ):Word w)) (c.mark+i) 1 := by
      change (if active i = true ∧ (m (c.counter+b)).val < B then _ else _) = _
      rw [ite_eq_left (selected_iff.mpr take),before]
    rw [after_mem]
    constructor
    · intro j hj
      rw [Function.update_of_ne (by omega : c.counter+j ≠ c.mark+i)]
      by_cases same : j=b
      · subst j
        rw [Function.update_self, Fin.val_cast_of_lt (by omega : r+1 < 2^w)]
        rw [prior, ite_eq_left ⟨act,rfl⟩]
        exact (Nat.min_eq_right (show r+1 ≤ B by omega)).symm
      · rw [Function.update_of_ne (by omega : c.counter+j ≠ c.counter+b),
          Function.update_of_ne (by omega : c.counter+j ≠ c.chosen+b*B+r),old.counter j hj]
        have nope : ¬ (active i = true ∧ key i=j) := fun h => same h.2.symm
        simp [prior, nope]
    · intro s hs good
      by_cases now : s=i
      · subst s
        change Function.update (Function.update (Function.update m (c.chosen+b*B+r) (rail i : Word w))
          (c.counter+b) ((r+1:ℕ):Word w)) (c.mark+i) 1 (c.chosen+b*B+r) = (rail i : Word w)
        simp [Function.update_of_ne, show c.chosen+b*B+r ≠ c.mark+i by omega,
          show c.chosen+b*B+r ≠ c.counter+b by omega]
      · have si : s < i := by omega
        obtain ⟨actS,prS⟩ := good
        let rs := prior key active (key s) s
        have sl : key s*B+rs < bins*B := slot_lt (bounds s si) prS
        have distinct : c.chosen+key s*B+rs ≠ c.chosen+b*B+r := by
          intro eq
          obtain ⟨same,rankEq⟩ := slot_eq prS hr (by omega : key s*B+rs=b*B+r)
          have later := prior_mono key active (key s) (show s+1 ≤ i by omega)
          rw [prior, ite_eq_left ⟨actS,rfl⟩] at later
          change rs = prior key active b i at rankEq
          rw [← same] at rankEq
          dsimp [rs] at rankEq
          omega
        change Function.update (Function.update (Function.update m (c.chosen+b*B+r) (rail i : Word w))
          (c.counter+b) ((r+1:ℕ):Word w)) (c.mark+i) 1 (c.chosen+key s*B+rs) = (rail s : Word w)
        rw [Function.update_of_ne (by omega : c.chosen+key s*B+rs ≠ c.mark+i),
          Function.update_of_ne (by omega : c.chosen+key s*B+rs ≠ c.counter+b), Function.update_of_ne distinct]
        exact old.chosen s si ⟨actS,prS⟩
    · intro s hs
      by_cases same : s=i
      · subst s; simp [take]
      · have si : s < i := by omega
        rw [Function.update_of_ne (by omega : c.mark+s ≠ c.mark+i),
          Function.update_of_ne (by omega : c.mark+s ≠ c.counter+b),
          Function.update_of_ne (by omega : c.mark+s ≠ c.chosen+b*B+r), old.mark s si]
    · intro s hs
      rw [Function.update_of_ne (by omega : s ≠ c.mark+i), Function.update_of_ne (by omega : s ≠ c.counter+b),
        Function.update_of_ne (by omega : s ≠ c.chosen+b*B+r), old.input s hs]
    · intro s hs
      rw [Function.update_of_ne (by omega : s ≠ c.mark+i),
        Function.update_of_ne (by omega : s ≠ c.counter+b),
        Function.update_of_ne (by omega : s ≠ c.chosen+b*B+r),old.above s (by omega)]
  · have after_mem : natStep c.counter c.chosen c.mark B (key i) (rail i) i (active i) m =
        Function.update m (c.mark+i) 0 := by
      exact ite_eq_right (mt selected_iff.mp take)
    rw [after_mem]
    constructor
    · intro j hj
      rw [Function.update_of_ne (by omega : c.counter+j ≠ c.mark+i), old.counter j hj,prior]
      by_cases add : active i = true ∧ key i=j
      · rw [ite_eq_left add]
        have full : B ≤ prior key active j i := by
          by_contra! h
          exact take ⟨add.1, by simpa [add.2] using h⟩
        omega
      · simp [add]
    · intro s hs good
      have ne : s ≠ i := fun eq => take (eq ▸ good)
      have si : s < i := by omega
      have small := slot_lt (bounds s si) good.2
      rw [Function.update_of_ne (by omega : c.chosen+key s*B+prior key active (key s) s ≠ c.mark+i)]
      exact old.chosen s si good
    · intro s hs
      by_cases same : s=i
      · subst s; simp [take]
      · rw [Function.update_of_ne (by omega : c.mark+s ≠ c.mark+i), old.mark s (by omega)]
    · intro s hs
      rw [Function.update_of_ne (by omega : s ≠ c.mark+i), old.input s hs]

    · intro s hs
      rw [Function.update_of_ne (by omega : s ≠ c.mark+i),old.above s (by omega)]

end Hierarchy.GridPassageRAMRow

end OAI
