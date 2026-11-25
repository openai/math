import OAI.Computability.NearSquareRoot.InterchangeCompiledAtlas

/-!
# Finite verification of native P192 address programs

Interpret each signed ratio and each opcode over the rationals. Two lists induce
the same address map at every prime-power width exactly when their rational
actions agree on the finitely many coordinate vectors.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Interchange.AddressROM

open IntegerMultiplication.Port

variable {J : Type} [DecidableEq J] {b : ℕ}

/-- Agreement at every width detects the numerator of a rational difference. -/
theorem separated (hb : 1 < b) {r s : ℚ} {v : (f : ℕ) → Tower b f}
    (hr : ∀ f, Token r (v f)) (hs : ∀ f, Token s (v f)) : r = s := by
  let q := r-s
  have zero (f : ℕ) : Token q (0 : Tower b f) := by simpa [q] using (hr f).sub (hs f)
  have residue (f : ℕ) : (q.num : Tower b f) = 0 := by
    have h := (Token.nat (R:=Tower b f) q.den).mul (zero f)
    rw [Rat.den_mul_eq_num, mul_zero] at h
    exact (Token.whole q.num).unique h
  have hd (f : ℕ) : b^f ∣ q.num.natAbs := by
    simpa only [Int.natAbs_natCast] using Int.natAbs_dvd_natAbs.mpr
      ((ZMod.intCast_zmod_eq_zero_iff_dvd q.num (b^f)).mp (residue f))
  apply sub_eq_zero.mp
  apply Rat.num_eq_zero.mp
  by_contra hn
  exact (not_lt_of_ge (Nat.le_of_dvd (Int.natAbs_pos.mpr hn) (hd _))) (Nat.lt_pow_self hb)

/-- Rational value actually encoded in the native scale operand. -/
def ratio (s : Span b) : ℚ :=
  (if s.neg then -1 else 1) * s.top.count * (s.down.count : ℚ)⁻¹

def scalar (s : Pinpoint b) : ℚ := s.elim 0 ratio

theorem ratio_token (s : Span b) (f : ℕ) : Token (ratio s) (s.land f) := by
  have sign : Token (if s.neg then -1 else 1 : ℚ) ((Span.polarity b f s.neg : (Tower b f)ˣ) : Tower b f) := by
    cases s.neg <;> simp [Span.polarity, Token.unit, Token.neg Token.unit]
  have hn : (s.down.count : ℚ) ≠ 0 := Nat.cast_ne_zero.mpr s.down.pos
  exact (sign.mul (Token.nat s.top.count)).mul <|
    (Token.nat s.down.count).inv (s.down.own f) rfl hn

theorem scalar_token (s : Pinpoint b) (f : ℕ) : Token (scalar s) (s.stamp f) := by
  cases s with
  | none => exact Token.zero
  | some s => exact ratio_token s f

/-- Rational evaluation uses the same instruction order and physical coordinates. -/
def fire (x : Spot J → ℚ) : Lag J b → Spot J → ℚ
  | .width a s => Function.update x a (ratio s * x a)
  | .gather a k s => Function.update x a (x a + scalar s * x k)
  | .pivot h d => fun t => x ((Equiv.swap (false,h) (true,d)) t)

def applyWord (ops : List (Lag J b)) (x : Spot J → ℚ) : Spot J → ℚ :=
  ops.foldl fire x

theorem fire_token (op : Lag J b) (f : ℕ) {x : Spot J → ℚ} {y : Duplex J (Tower b f)}
    (h : ∀ j, Token (x j) (hear y j)) (t : Spot J) :
    Token (fire x op t) (hear (op.fire f y) t) := by
  cases op with
  | width a s =>
    by_cases e : t = a
    · subst t
      simpa [fire,Lag.fire] using (ratio_token s f).mul (h a)
    · simpa [fire,Lag.fire,e] using h t
  | gather a k s =>
    by_cases e : t = a
    · subst t
      simpa [fire,Lag.fire] using (h a).add ((scalar_token s f).mul (h k))
    · simpa [fire,Lag.fire,e] using h t
  | pivot a d =>
    by_cases e : t = (false,a)
    · subst t
      simpa [fire,Lag.fire] using h (true,d)
    by_cases g : t = (true,d)
    · subst t
      simpa [fire,Lag.fire] using h (false,a)
    · simpa [fire,Lag.fire,e,g,Equiv.swap_apply_of_ne_of_ne e g] using h t

theorem applyWord_token (ops : List (Lag J b)) (f : ℕ) {x : Spot J → ℚ} {y : Duplex J (Tower b f)}
    (h : ∀ j, Token (x j) (hear y j)) (t : Spot J) :
    Token (applyWord ops x t) (hear (ops.foldl (Lag.fire f) y) t) := by
  induction ops generalizing x y with
  | nil => exact h t
  | cons op ops ih => exact ih (fire_token op f h)

end Interchange.AddressROM

end NearSquareRoot
end Computability
end OAI
