import OAI.Computability.VPVNP.PairSimulationRouteWord
import OAI.Computability.VPVNP.PairTraversalStageSize
import OAI.Computability.VPVNP.CompressorDescriptorBranchSpace

/-!
# The persistent traversal controller ordinal

Both the role pass and the row pass use the same radix for site ordinals.
The radix reserves one more digit than the initial number of sites, so the
end of any layer is represented even if that layer has the maximum count.
The final return at phase-level twice the number of layers also fits the
word, uniformly over the selected compressor branches.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TraversalControllerOrdinal

open BurstRAM PrivateRAM
open scoped Fin.CommRing

variable {w L initialSites phaseLevel site : ℕ}

/-- Numerical encoding of the phase-level and the current site. -/
def pack (initialSites phaseLevel site : ℕ) : ℕ := phaseLevel * (initialSites + 1) + site

theorem pack_lt (phase : phaseLevel < 2 * L) (digit : site ≤ initialSites) :
    pack initialSites phaseLevel site < 2 * L * (initialSites + 1) := by
  calc
    _ < phaseLevel * (initialSites + 1) + (initialSites + 1) :=
      Nat.add_lt_add_left (Nat.lt_succ_of_le digit) _
    _ = (phaseLevel + 1) * (initialSites + 1) := (Nat.succ_mul ..).symm
    _ ≤ _ := Nat.mul_le_mul_right _ phase

private theorem quotient {a b : ℕ} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    BinaryOp.div.eval (a : Word w) (b : Word w) = ((a / b : ℕ) : Word w) := by
  change Fin.ofNat _ ((a % (2^w)) / (b % (2^w))) = _
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rfl

private theorem remainder {a b : ℕ} (ha : a < 2 ^ w) (hb : b < 2 ^ w) :
    BinaryOp.mod.eval (a : Word w) (b : Word w) = ((a % b : ℕ) : Word w) := by
  change Fin.ofNat _ ((a % (2^w)) % (b % (2^w))) = _
  rw [Nat.mod_eq_of_lt ha, Nat.mod_eq_of_lt hb]
  rfl

/-- The site and phase-level reads, including at an empty layer. -/
theorem decode_of_fit (digit : site ≤ initialSites) (fit : pack initialSites phaseLevel site < 2 ^ w)
    (radixFit : initialSites + 1 < 2 ^ w) :
    let st := (pack initialSites phaseLevel site : Word w)
    let pitch := ((initialSites + 1 : ℕ) : Word w)
    BinaryOp.div.eval st pitch = (phaseLevel : Word w) ∧
      BinaryOp.mod.eval st pitch = (site : Word w) := by
  dsimp only
  rw [quotient fit radixFit, remainder fit radixFit]
  have d : site < initialSites + 1 := Nat.lt_succ_of_le digit
  simp only [pack, Nat.mul_comm phaseLevel (initialSites + 1), Nat.mul_add_div (Nat.succ_pos _),
    Nat.div_eq_of_lt d, Nat.add_zero, Nat.mul_add_mod, Nat.mod_eq_of_lt d, and_self]

theorem decode (phase : phaseLevel < 2 * L) (digit : site ≤ initialSites)
    (fit : 2 * L * (initialSites + 1) < 2 ^ w) :
    let st := (pack initialSites phaseLevel site : Word w)
    let pitch := ((initialSites + 1 : ℕ) : Word w)
    BinaryOp.div.eval st pitch = (phaseLevel : Word w) ∧
      BinaryOp.mod.eval st pitch = (site : Word w) :=
  decode_of_fit digit ((pack_lt phase digit).trans fit)
    ((Nat.le_mul_of_pos_left _ (Nat.zero_lt_of_lt phase)).trans_lt fit)

/-- The terminal sentinel decodes to phase-level twice the number of layers. -/
theorem decode_stop (hL : 0 < L) (fit : 2 * L * (initialSites + 1) < 2 ^ w) :
    let st := (pack initialSites (2 * L) 0 : Word w)
    let pitch := ((initialSites + 1 : ℕ) : Word w)
    BinaryOp.div.eval st pitch = ((2 * L : ℕ) : Word w) ∧ BinaryOp.mod.eval st pitch = 0 := by
  exact decode_of_fit (Nat.zero_le _) (by simpa [pack] using fit)
    ((Nat.le_mul_of_pos_left _ (Nat.mul_pos (by decide) hL)).trans_lt fit)

/-- A level count of one selects the terminal site's count. -/
theorem one_div_levels (hL : 0 < L) (fit : L < 2 ^ w) :
    BinaryOp.div.eval (1 : Word w) (L : Word w) = if L = 1 then 1 else 0 := by
  rw [show (1 : Word w) = ((1 : ℕ) : Word w) from rfl, quotient (lt_of_le_of_lt hL fit) fit]
  by_cases h : L = 1
  · subst L; rfl
  · rw [ite_eq_right h, Nat.div_eq_of_lt (show 1 < L by omega)]
    rfl

/-- The level, its nonzero flag, and its predecessor with saturation at zero. -/
theorem index_words (hL : 0 < L) (fitL : L < 2 ^ w) (fitPhase : phaseLevel < 2 ^ w) :
    let j := BinaryOp.mod.eval (phaseLevel : Word w) (L : Word w)
    let nz := BinaryOp.div.eval j j
    j = ((phaseLevel % L : ℕ) : Word w) ∧
      nz = (if phaseLevel % L = 0 then 0 else 1) ∧
      BinaryOp.sub.eval j nz = ((phaseLevel % L - 1 : ℕ) : Word w) := by
  dsimp only
  rw [remainder fitPhase fitL, RouteWord.div_self ((Nat.mod_lt _ hL).trans fitL)]
  by_cases h : phaseLevel % L = 0
  · simp only [h, ite_eq_left, Nat.zero_sub, Nat.cast_zero, BinaryOp.eval, sub_self, and_self]
  · simp only [ite_eq_right h, true_and]
    exact RouteWord.sub_cast (Nat.pos_of_ne_zero h)

/-- Advancing within the current layer adds one to the packed word. -/
theorem next_site (phase : phaseLevel < 2 * L) (active : site < initialSites)
    (fit : 2 * L * (initialSites + 1) < 2 ^ w) :
    let next := BinaryOp.add.eval (pack initialSites phaseLevel site : Word w) 1
    next.val = pack initialSites phaseLevel (site + 1) := by
  have eq : BinaryOp.add.eval (pack initialSites phaseLevel site : Word w) 1 =
      (pack initialSites phaseLevel (site + 1) : Word w) := by
    simp only [BinaryOp.eval, pack, Nat.cast_add, Nat.cast_one, add_assoc]
  dsimp only
  rw [eq, Fin.val_natCast, Nat.mod_eq_of_lt ((pack_lt phase active).trans fit)]

/-- Skipping to the next layer resets the site digit, including the final
transition to the terminal sentinel. -/
theorem next_level (phase : phaseLevel < 2 * L) (fit : 2 * L * (initialSites + 1) < 2 ^ w) :
    let next := BinaryOp.mul.eval (BinaryOp.add.eval (phaseLevel : Word w) 1)
      ((initialSites + 1 : ℕ) : Word w)
    next.val = pack initialSites (phaseLevel + 1) 0 := by
  have eq : BinaryOp.mul.eval (BinaryOp.add.eval (phaseLevel : Word w) 1)
      ((initialSites + 1 : ℕ) : Word w) = (pack initialSites (phaseLevel + 1) 0 : Word w) := by
    simp only [BinaryOp.eval, pack, Nat.add_zero, Nat.cast_mul, Nat.cast_add, Nat.cast_one]
  dsimp only
  rw [eq, Fin.val_natCast, Nat.mod_eq_of_lt]
  simpa only [pack, Nat.add_zero] using (Nat.mul_le_mul_right (initialSites + 1) phase).trans_lt fit

open CompressorRecords CursorBounds CursorNetwork Compression Filter
open private bounded_blockCount from OAI.Computability.VPVNP.CompressorDescriptorSpace

/-- The controller's two full passes and the terminal sentinel fit one host
word at a common threshold preceding all choices of specialization and branch. -/
theorem eventually_selected_fit {k : Type*} [Field k] {S : BlockSchedule k}
    (B : S.Templates) (u : PairExponents B.growthConstant) (b : ℕ) (hb : 1 ≤ b) :
    ∀ᶠ n : ℕ in atTop, ∀ {base lanes : ℕ} (labels : Fin (virtualBits b n) ≃ Fin base ⊕ Fin lanes)
      (hD : 1 < virtualBits b n) (hT : blockCount (u.θ : ℝ) n * S.laneBits ≤ lanes)
      (A : Type*) [CommRing A] (f : B.Entry → A) (hf : B.IsSolution f),
      let T := blockCount (u.θ : ℝ) n
      let X := pairInput S labels hD
      ∀ z : (B.execute f hf T hT X).Choices,
        2 * ((executeLevels B f hf T hT X z).length + 1) * (X.positions + 1) < 2 ^ wordBits b n := by
  have hθ : (u.θ : ℝ) ≤ 1 := by
    have := (Rat.cast_lt (K := ℝ)).mpr u.theta_lt
    norm_num at this
    linarith
  let levels := ((PolynomiallyBounded.const (S.steps + 1)).mul (bounded_blockCount hθ)).add
    (PolynomiallyBounded.const 1)
  have cap := ((PolynomiallyBounded.const 2).mul levels).mul
    ((CursorRAM.bounded_positions b).add (PolynomiallyBounded.const 1))
  filter_upwards [CursorRAM.eventual_word_room b hb cap] with n hn
  intro base lanes labels hD hT A _ f hf T X z
  have hp : X.positions = initialPositions b n := pairInput_positions S labels hD
  rw [hp]
  exact (Nat.mul_le_mul_right _ (Nat.mul_le_mul_left 2
    (Nat.succ_le_succ (executeLevels_length B f hf T hT X z)))).trans_lt hn

end PairSimulation.TraversalControllerOrdinal

end VPVNP
end Computability
end OAI
