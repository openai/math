import OAI.Computability.MultitapeWeakETH.Machine
import Mathlib.Analysis.SpecialFunctions.BinaryEntropy
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Algebra.Order.Floor.Div

/-! # Finite programmable relations and the outstanding table and trace bounds -/

namespace OAI.Computability.MultitapeWeakETH

/-- Block zero contains the least significant bits of the big-endian word. -/
def block {n : ℕ} (b : ℕ) (i : Fin n) := (n - 1 - i.val) / b

structure Network (n b : ℕ) where
  vertices : ℕ
  edges : ℕ
  src : Fin edges → Fin vertices
  dst : Fin edges → Fin vertices
  width : Fin edges → ℕ
  input : Fin (n ⌈/⌉ b) ↪ Fin vertices
  output : Fin (n ⌈/⌉ b) ↪ Fin vertices

namespace Network

variable {n b : ℕ} (G : Network n b)

def degree (v : Fin G.vertices) : ℕ :=
  (Finset.univ.filter fun e => G.src e = v).card +
  (Finset.univ.filter fun e => G.dst e = v).card

def Bounded (D : ℕ) := (∀ v, G.degree v ≤ D) ∧ ∀ e, G.width e ≤ D * b

def localBits (terminal : Fin (n ⌈/⌉ b) ↪ Fin G.vertices) (v : Fin G.vertices) :=
  { i : Fin n // ∃ j, j.val = block b i ∧ terminal j = v }

/-- A local relation sees only incident labels and bits attached to its vertex.
The two ends of a loop receive the same edge label. -/
abbrev Relation := ∀ v : Fin G.vertices,
  ((e : { e // G.src e = v ∨ G.dst e = v }) → Word (G.width e.val)) →
  (G.localBits G.input v → Bool) → (G.localBits G.output v → Bool) → Prop

def Attains (tables : G.Relation) (x out : Word n) : Prop :=
  ∃ labels : (e : Fin G.edges) → Word (G.width e), ∀ v,
    tables v (fun e => labels e.val) (fun i => x i.val) (fun i => out i.val)

def Good (tables : Word n → G.Relation) (x y : Word n) : Prop :=
  ∃ out, G.Attains (tables y) x out ∧ (∀ other, G.Attains (tables y) x other → other = out) ∧
    100 * errors out (lowProduct x y) ≤ n

end Network

noncomputable def entropyBits (e : ℝ) := Real.binEntropy e / Real.log 2

/-- Slack for the loss of good rows when a coarse trace is chosen. -/
theorem trace_density_margin :
    11 / 1000 + entropyBits (1/100) / Real.sqrt 2 < (1 - 1 / Real.sqrt 2) / 4 := by
  have log100 : Real.log 100 ≤ 7 * Real.log 2 := by
    convert Real.log_le_log (by norm_num : (0 : ℝ) < 100)
      (by norm_num : (100 : ℝ) ≤ 2^7) using 1
    rw [Real.log_pow]; norm_num
  have small := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 100/99)
  have ent : entropyBits (1/100) ≤ 17/200 := by
    unfold entropyBits Real.binEntropy
    norm_num only [show (1-(1/100:ℝ)) = 99/100 by norm_num,
      show ((1/100:ℝ))⁻¹ = 100 by norm_num, show ((99/100:ℝ))⁻¹ = 100/99 by norm_num]
    apply (div_le_iff₀ (Real.log_pos (by norm_num))).mpr
    linarith [Real.log_two_gt_d9]
  have hroot : (141 : ℝ)/100 < Real.sqrt 2 := by
    nlinarith [Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), Real.sqrt_nonneg 2]
  field_simp [show Real.sqrt 2 ≠ 0 by positivity]
  nlinarith

/-- The char-zero relation-network specialization of Theorem 2.2(1), with
the odd multiplier equal to one and a fixed strict density margin. -/
def PartialTableBound : Prop := ∀ D : ℕ, ∃ c : ℝ, 0 < c ∧ ∃ m₀ : ℕ,
  ∀ n b, 0 < b → m₀ ≤ n ⌈/⌉ b → ∀ G : Network n b, G.Bounded D →
    ∀ tables : Word n → G.Relation,
      (2 : ℝ)^(-(11/1000 : ℝ) * n) ≤ density (G.Good tables) →
        c * scale (n ⌈/⌉ b) ≤ G.vertices

def retained (M : Machine) (n T : ℕ) : Prop :=
  (∃ seed, threshold n ≤ accurateDensity M n T seed) ∨
    (Sound M ∧ threshold n ≤ nondetDensity M n T)

/-- Lemma 2.3 specialized to length-(sqrt n + 1) epochs. The trace-count
loss is still present in the density exponent and the constants precede the cutoff. -/
def CoarseTraceBound : Prop := ∀ M : Machine, ∃ D A : ℕ, 0 < A ∧ ∃ n₀ : ℕ,
  ∀ n ≥ n₀, ∀ T, retained M n T →
    let b := n.sqrt + 1
    ∃ G : Network n b, G.Bounded D ∧ (G.vertices : ℝ) * b ≤ A * ((b : ℝ) + T + n) ∧
      ∃ tables : Word n → G.Relation,
        (2 : ℝ)^(-(n : ℝ)/100 - A * (1 + (T : ℝ)/b)) ≤ density (G.Good tables)

end OAI.Computability.MultitapeWeakETH
