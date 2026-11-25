import OAI.Computability.NearSquareRoot.PhysicalWalshGridLeaves
import OAI.Computability.NearSquareRoot.PhysicalWalshBase
import OAI.Computability.NearSquareRoot.KernelScaleLayout

/-! # The rounded selected-piece transform on an ordered flat stream

A node has one contiguous active bit field, surrounded by arbitrary prefix
and suffix spectators. Only the quotient and remainder of the prefix by the
batch width are used when splitting and merging. Moving to a child merely
reclassifies the other slots as spectators of its active field.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshNode

open IntegerMultiplication Code KernelPass PhysicalWalsh PhysicalWalshGrid

structure Shape where
  level : ℕ
  pref : ℕ
  suff : ℕ
  w : ℕ
  pref_pos : 0 < pref
  suff_pos : 0 < suff

/-- Number of selected bits of a level-`j` piece. -/
def grow (A j : ℕ) := 2 * A^j

def groups (W : ℕ) (s : Shape) := max 1 (s.pref / W)

def inner (A : ℕ) (s : Shape) := 2^(grow A s.level) * s.suff

def count (A : ℕ) (s : Shape) := s.pref * inner A s

/-- Label the physical records in one lane by ascending natural ordinals. -/
def coords (a W : ℕ) : KernelScaleBank.Layout a Shape ℕ :=
  KernelScaleLayout.ordinal a (fun s => (a+1)^(s.level-1)) (groups W) Shape.suff
    (fun _ => Nat.zero_lt_one.trans_le (Nat.le_max_left ..)) Shape.suff_pos

/-- Child `axis` of an `A`-slot node, in high-to-low slot order. -/
def descend (A W : ℕ) (axis : Fin A) (s : Shape) : Shape where
  level := s.level-1
  pref := groups W s * 2^(axis.val * grow A (s.level-1))
  suff := 2^((A-1-axis.val) * grow A (s.level-1)) * s.suff
  w := s.w
  pref_pos := Nat.mul_pos (Nat.zero_lt_one.trans_le (Nat.le_max_left ..)) (by positivity)
  suff_pos := Nat.mul_pos (by positivity) s.suff_pos

/-- A total array model. Tape storage reads the initial `count` entries. -/
abbrev Data (s : Shape) := ℕ → Dusk.Grain s.w

def lane (A W : ℕ) (s : Shape) (x : Data s) (b : Fin W) (n : ℕ) : Dusk.Grain s.w :=
  x ((n / inner A s * W + b.val) * inner A s + n % inner A s)

def unlane {W : ℕ} (A : ℕ) (hW : 0 < W) (s : Shape) (x : Fin W → Data s) (n : ℕ) : Dusk.Grain s.w :=
  x ⟨n / inner A s % W, Nat.mod_lt _ hW⟩ (n / inner A s / W * inner A s + n % inner A s)

theorem unlane_lane {A W : ℕ} (hW : 0 < W) (s : Shape) (x : Data s) :
    unlane A hW s (lane A W s x) = x := by
  funext n
  let R := inner A s
  have pos : 0 < R := Nat.mul_pos (by positivity : 0 < 2^grow A s.level) s.suff_pos
  let p := n/R
  let z := n%R
  have small : z < R := Nat.mod_lt _ pos
  have divide : (p/W*R+z)/R = p/W := by rw [Nat.mul_comm (p/W), Nat.mul_add_div pos, Nat.div_eq_of_lt small, Nat.add_zero]
  have remain : (p/W*R+z)%R = z := by rw [Nat.mul_comm (p/W), Nat.mul_add_mod, Nat.mod_eq_of_lt small]
  change x ((((p/W*R+z)/R * W + p%W) * R + (p/W*R+z)%R)) = x n
  rw [divide, remain, Nat.div_add_mod' p W]
  exact congrArg x (Nat.div_add_mod' n R)

/-- Physical input ordinal supplying the permutation's output at `n`. The
active address uses precisely the paired-column order of the scale table. -/
def xorIndex (a : ℕ) (g : Fin (a+1) × Fin (a+1)) (s : Shape) (n : ℕ) : ℕ :=
  let h := (a+1)^(s.level-1)
  let m := 2^((a+1)*(2*h))
  let x := KernelScaleLayout.coord a h s.suff n
  (n/s.suff/m*m + (KernelScaleLayout.rank (xorColumn g ∘ x)).val)*s.suff + n%s.suff

def xor (a : ℕ) (g : Fin (a+1) × Fin (a+1)) (s : Shape) (x : Data s) : Data s := x ∘ xorIndex a g s

/-- Four-point base transform at the actual suffix stride, including all spectators. -/
def base (s : Shape) (x : Data s) (n : ℕ) : Dusk.Grain s.w :=
  PhysicalWalshBase.transform (fun b => x ((n/s.suff/4*4 + b.val)*s.suff + n%s.suff))
    ⟨n/s.suff%4, Nat.mod_lt _ (by decide)⟩

/-- The level counter decreases at every template child. The result is a
function of the original single input row in its original address order. -/
def runWith {a W : ℕ} (hW : 0 < W) (p : Plan (a+1) W W) : ℕ → (s : Shape) → Data s → Data s
  | 0, s, x => base s x
  | j+1, s, x =>
    let f := ops (coords a W) Shape.w (xor a) (fun axis u => runWith hW p j (descend (a+1) W axis u))
    unlane (a+1) hW s (f.applyPlan p s (lane (a+1) W s x))

def run {a W : ℕ} (hW : 0 < W) (p : Plan (a+1) W W) (s : Shape) : Data s → Data s :=
  runWith hW p s.level s

def nodeOps {a W : ℕ} (hW : 0 < W) (p : Plan (a+1) W W) :=
  ops (coords a W) Shape.w (xor a) (fun axis s => run hW p (descend (a+1) W axis s))

/-- Every admissible nonterminal gets a whole positive number of work batches. -/
theorem groups_eq_div {W : ℕ} {s : Shape} (hl : 0 < s.level) (hd : W^s.level ∣ s.pref) :
    groups W s = s.pref/W := by
  have hdiv : W ∣ s.pref := (dvd_pow_self _ hl.ne').trans hd
  have pos : 0 < s.pref / W := Nat.div_pos (Nat.le_of_dvd s.pref_pos hdiv)
    (Nat.pos_of_dvd_of_pos hdiv s.pref_pos)
  exact max_eq_right pos

theorem groups_mul {W : ℕ} {s : Shape} (hl : 0 < s.level) (hd : W^s.level ∣ s.pref) :
    groups W s * W = s.pref := by
  rw [groups_eq_div hl hd]
  exact Nat.div_mul_cancel ((dvd_pow_self _ hl.ne').trans hd)

theorem child_divisible {A W : ℕ} (s : Shape) (a : Fin A) (hl : 0 < s.level)
    (hd : W^s.level ∣ s.pref) : W^(descend A W a s).level ∣ (descend A W a s).pref := by
  change W^(s.level-1) ∣ groups W s * _
  apply dvd_mul_of_dvd_left _ _
  rw [groups_eq_div hl hd]
  apply Nat.dvd_div_of_mul_dvd
  rwa [← pow_succ', Nat.sub_add_cancel hl]

/-- Inactive slots stay complete spectators when restricting to one active slot. -/
theorem child_count {A W : ℕ} (s : Shape) (a : Fin A) (hl : 0 < s.level) :
    count A (descend A W a s) = groups W s * inner A s := by
  have h := a.isLt
  have axes : a.val + 1 + (A-1-a.val) = A := by omega
  have size : a.val*grow A (s.level-1) + grow A (s.level-1) + (A-1-a.val)*grow A (s.level-1) = grow A s.level := by
    rw [← Nat.succ_mul, ← Nat.add_mul, axes, grow, grow]
    rw [Nat.mul_left_comm A 2, ← pow_succ', Nat.sub_add_cancel hl]
  change (groups W s * 2^(a.val * _)) * (2^(grow A (s.level-1)) * (2^((A-1-a.val)*_) * s.suff)) = _
  rw [show groups W s * 2^(a.val * grow A (s.level-1)) *
      (2^grow A (s.level-1)*(2^((A-1-a.val)*grow A (s.level-1))*s.suff)) =
      groups W s*((2^(a.val*grow A (s.level-1))*2^grow A (s.level-1))*2^((A-1-a.val)*grow A (s.level-1))*s.suff) by ring,
    ← pow_add, ← pow_add, size]
  rfl

/-- The recursive command sees exactly one `W`th of the parent records. -/
theorem volume_split {A W : ℕ} (s : Shape) (a : Fin A) (hl : 0 < s.level) (hd : W^s.level ∣ s.pref) :
    W * count A (descend A W a s) = count A s := by
  rw [child_count _ _ hl, ← Nat.mul_assoc, Nat.mul_comm W, groups_mul hl hd]; rfl

private theorem child_congr {a W i o : ℕ} (p : Plan (a+1) i o) (s : Shape)
    (b c : Fin (a+1) → (v : Shape) → Data v → Data v)
    (agree : ∀ axis x, b axis s x = c axis s x)
    (x : Rows (layout (coords a W) Shape.w) s i) :
    (ops (coords a W) Shape.w (xor a) b).applyPlan p s x =
      (ops (coords a W) Shape.w (xor a) c).applyPlan p s x := by
  induction p with
  | mix _ | xor _ | scale _ _ _ => rfl
  | child axis => exact funext fun _ => agree axis _
  | seq p q hp hq => simp only [Ops.applyPlan, hp, hq]
  | parallel p q hp hq => simp only [Ops.applyPlan, hp, hq]

theorem run_base {a W : ℕ} (hW : 0 < W) (p : Plan (a+1) W W) (s : Shape) (h : s.level=0) :
    run hW p s = base s := by simp [run, h, runWith]

theorem run_step {a W : ℕ} (hW : 0 < W) (p : Plan (a+1) W W) (s : Shape) (hl : 0 < s.level) (x : Data s) :
    run hW p s x = unlane (a+1) hW s ((nodeOps hW p).applyPlan p s (lane (a+1) W s x)) := by
  obtain ⟨j,hj⟩ := Nat.exists_eq_succ_of_ne_zero hl.ne'
  rw [run, hj, runWith]
  apply congrArg (unlane (a+1) hW s)
  apply child_congr
  intro axis y
  simp only [run, descend, hj, Nat.succ_sub_one]

end PhysicalWalshNode

end NearSquareRoot
end Computability
end OAI
