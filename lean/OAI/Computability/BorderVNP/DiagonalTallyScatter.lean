import OAI.Computability.BorderVNP.DiagonalResidueRAMFrame
import OAI.Computability.BorderVNP.RoutingISADeterministic

/-!
# Native accumulation of the team's private monomial exponents

The input stream alternates a coordinate with its nonnegative increment. Registers
48, 49, 50, 51, and 63 hold the tally base, dimension, current record pointer,
end pointer, and one. The fragment uses registers 52 through 56 for scratch.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyScatter

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA
open DiagonalResidueRAM (word word_val word_add TraceOK effect effect_runs)

/-- The pair of instructions reading a word at the record cursor and advancing it. -/
def readNext (dst : Reg) : Code := .seq (.load dst 50) (.binary .add 50 50 63)

/-- Compute the prospective new value before the unsigned overflow test. -/
def sumStep : Code := .seq (.load 55 54) (.binary .add 56 55 53)

/-- Read a complete record, check its coordinate and both additions, then store
the new tally. Each check occupies an actual instruction in the fixed ISA. -/
def body : Code := .seq (readNext 52) (.ifLt 50 51
  (.seq (readNext 53) (.ifLt 52 49
    (.seq (.binary .add 54 48 52) (.ifLt 54 48 .reject
      (.seq sumStep (.ifLt 56 55 .reject (.store 54 56)))))
    .reject))
  .reject)

/-- Fall through only after the record cursor reaches the precise end pointer. -/
def scatter : Code := .seq (.whileLt 50 51 body) (.ifEq 50 51 .nop .reject)

/-- All registers outside the designated writable scratch/cursor range are preserved. -/
def Preserved {w : ℕ} (s t : Bank w) : Prop :=
  ∀ j, j ≠ 50 → j ≠ 52 → j ≠ 53 → j ≠ 54 → j ≠ 55 → j ≠ 56 → t j = s j

/-- The input and preserved registers identify a valid scatter call. -/
def Loaded {w : ℕ} (s : Bank w) (base dim cursor stop : ℕ) : Prop :=
  (s 48).val = base ∧ (s 49).val = dim ∧ (s 50).val = cursor ∧
    (s 51).val = stop ∧ (s 63).val = 1

/-- Coordinate and increment words at the successive record addresses. -/
def RecordsAt {w : ℕ} (m : Memory w) : ℕ → List (ℕ × ℕ) → Prop
  | _, [] => True
  | p, r :: rs => (m p).val = r.1 ∧ (m (p+1)).val = r.2 ∧ RecordsAt m (p+2) rs

/-- Total natural increment delivered to one physical tally address. -/
def incrementAt (base a : ℕ) : List (ℕ × ℕ) → ℕ
  | [] => 0
  | r :: rs => (if base+r.1 = a then r.2 else 0) + incrementAt base a rs

/-- Initial tally values plus the specified increments, as a word-addressed memory.
An address outside the record coordinates receives zero total increment. -/
def after {w : ℕ} (base : ℕ) (rs : List (ℕ × ℕ)) (m : Memory w) : Memory w :=
  fun a => m a + word w (incrementAt base a rs)

/-- Every tally address is disjoint from the contiguous advice records. -/
def Separate (base dim cursor stop : ℕ) : Prop :=
  ∀ i < dim, base+i < cursor ∨ stop ≤ base+i

private theorem add_val {w : ℕ} (x y : Word w) (h : x.val + y.val < 2^w) :
    (x+y).val = x.val+y.val := Nat.mod_eq_of_lt h

/-- Register preservation composes across successive records. -/
theorem Preserved.trans {w : ℕ} {s t u : Bank w} (h : Preserved s t)
    (h' : Preserved t u) : Preserved s u :=
  fun i a b c d e f => (h' i a b c d e f).trans (h i a b c d e f)

/-- One complete in-range record consumes twelve ticks, including all three
arithmetic/coordinate guards and the check that the second record word exists. -/
theorem body_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) {base dim p stop i v : ℕ} (hs : Loaded s base dim p stop)
    (hend : p+2 ≤ stop) (hi : i < dim) (haddr : base+i < 2^w)
    (hv : (m (base+i)).val + v < 2^w) (hrec : (m p).val = i) (hinc : (m (p+1)).val = v) :
    ∃ es t, Runs pub mac body s m es t (Function.update m (base+i) (m (base+i) + m (p+1))) ∧
      Loaded t base dim (p+2) stop ∧ Preserved s t ∧ TraceOK es [] 12 := by
  rcases hs with ⟨hb,hd,hp,he,hone⟩
  have hstop : stop < 2^w := he ▸ (s 51).isLt
  let u := Function.update (Function.update s (52 : Reg) (m p)) (50 : Reg) (s 50+s 63)
  let t := Function.update (Function.update u (53 : Reg) (m (p+1))) (50 : Reg) (u 50+u 63)
  let y := Function.update t (54 : Reg) (t 48+t 52)
  let z := Function.update (Function.update y (55 : Reg) (m (base+i))) (56 : Reg) (m (base+i)+m (p+1))
  let e₁ := (effect false s m (readNext 52)).trace
  let e₂ := (effect false u m (readNext 53)).trace
  let e₃ := (effect false y m sumStep).trace
  have up : (u 50).val = p+1 := by
    simp only [u, Function.update_self]
    rw [add_val _ _ (by omega),hp,hone]
  have tp : (t 50).val = p+2 := by
    have ho : (u 63).val = 1 := by simpa [u,Function.update] using hone
    simp only [t, Function.update_self]
    rw [add_val _ _ (by omega), up, ho]
  have ya : (y 54).val = base+i := by
    simp only [y, Function.update_self]
    have a : (t 48).val = base := by simpa [t,u,Function.update] using hb
    have c : (t 52).val = i := by simpa [t,u,Function.update] using hrec
    rw [add_val _ _ (by omega),a,c]
  have run₁ : Runs pub mac (readNext 52) s m e₁ u m := by
    simpa [readNext, effect, u, e₁, hp, BinaryOp.eval, Function.update] using
      effect_runs pub mac false s m (readNext 52) (by decide)
  have run₂ : Runs pub mac (readNext 53) u m e₂ t m := by
    simpa [readNext, effect, t, e₂, up, BinaryOp.eval, Function.update] using
      effect_runs pub mac false u m (readNext 53) (by decide)
  have run₃ : Runs pub mac (.binary .add 54 48 52) t m [tick w] y m :=
    Runs.localStep m rfl rfl
  have run₄ : Runs pub mac sumStep y m e₃ z m := by
    have yi : y 53 = m (p+1) := by simp [y,t,Function.update]
    simpa [sumStep, effect, z, e₃, ya, yi, Function.update, BinaryOp.eval] using
      effect_runs pub mac false y m sumStep (by decide)
  have guard₁ : u 50 < u 51 := by
    change (u 50).val < (u 51).val
    have h : (u 51).val = stop := by simpa [u, Function.update] using he
    omega
  have guard₂ : t 52 < t 49 := by
    change (t 52).val < (t 49).val
    simp [t,u,Function.update,hrec,hd,hi]
  have guard₃ : ¬ y 54 < y 48 := by
    change ¬ (y 54).val < (y 48).val
    have h : (y 48).val = base := by simpa [y,t,u,Function.update] using hb
    omega
  have guard₄ : ¬ z 56 < z 55 := by
    change ¬ (z 56).val < (z 55).val
    simp only [z, Function.update_self]
    have hsum := add_val (m (base+i)) (m (p+1)) (by omega)
    simp [Function.update, hsum]
  let e₄ : TeamRAM.Event w := ⟨.ordinary (some (base+i, some (m (base+i)+m (p+1)))), [m (base+i)], [], .plus⟩
  have store : Runs pub mac (.store 54 56) z m [e₄] z (Function.update m (base+i) (m (base+i)+m (p+1))) := by
    have za : (z 54).val = base+i := by simpa [z,Function.update] using ya
    have zv : z 56 = m (base+i)+m (p+1) := by simp [z]
    simpa only [za, zv, e₄] using Runs.store pub mac 54 56 z m
  have branch₄ := Runs.ifLt (pub := pub) (macros := mac) (s := z) (m := m) (x := 56) (y := 55) (a := .reject) (b := .store 54 56)
    (by simpa only [ite_eq_right guard₄] using store)
  have branch₃ := Runs.ifLt (pub := pub) (macros := mac) (s := y) (m := m) (x := 54) (y := 48) (a := .reject) (b := .seq sumStep _)
    (by simpa only [ite_eq_right guard₃] using Runs.seq run₄ branch₄)
  have branch₂ := Runs.ifLt (pub := pub) (macros := mac) (s := t) (m := m) (x := 52) (y := 49) (a := .seq (.binary .add 54 48 52) _) (b := .reject)
    (by simpa only [ite_eq_left guard₂] using Runs.seq run₃ branch₃)
  have branch₁ := Runs.ifLt (pub := pub) (macros := mac) (s := u) (m := m) (x := 50) (y := 51) (a := .seq (readNext 53) _) (b := .reject)
    (by simpa only [ite_eq_left guard₁] using Runs.seq run₂ branch₂)
  refine ⟨_, z, Runs.seq run₁ branch₁, ?_, ?_, ?_⟩
  · simp [Loaded,z,y,t,u,Function.update,hb,hd,he,hone] at tp ⊢
    exact tp
  · intro j h₀ h₂ h₃ h₄ h₅ h₆
    simp [z,y,t,u,Function.update,h₀,h₂,h₃,h₄,h₅,h₆]
  · simp [TraceOK, e₁,e₂,e₃,e₄, effect, readNext, sumStep, tick]

end DiagonalTallyScatter

end BorderVNP
end Computability
end OAI
