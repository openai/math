import OAI.LinearAlgebra.MatrixExponent.Lookup.Defs

/-!
# Binary counts

The first bit is least significant. Ripple carry and the unary field
weights both use a number of vertices linear in the number of bits.
-/

namespace OAI.LinearAlgebra.MatrixExponent

/-- Join one output bundle to an input without charging for identity gates
on the untouched exterior bundles. -/
theorem DNet.plug {F : Type} [Field F] {a b c d e : Wire} {m n : ℕ}
    {f : Val a → Val (.pair b c)} {g : Val (.pair c d) → Val e}
    (h : DNet F a (.pair b c) f m) (k : DNet F (.pair c d) e g n) :
    DNet F (.pair a d) (.pair b e) (fun x => ((f x.1).1, g ((f x.1).2, x.2))) (m + n) := by
  obtain ⟨v, hv, h⟩ := h
  obtain ⟨w, hw, k⟩ := k
  refine ⟨_, Nat.add_le_add hv hw, ?_⟩
  have rin := (Rewire.assoc a d c).comp ((Rewire.id a).par (Rewire.swap d c))
  have rout := ((Rewire.assoc b e c).comp
    ((Rewire.id b).par (Rewire.swap e c))).comp (Rewire.assoc' b c e)
  have ht := (((h.par k).pre rin).post rout).trace
  convert ht using 1
  funext x y
  simp only [Prod.ext_iff, ite_and, ite_mul, one_mul, zero_mul]
  by_cases he : (f x.1).1 = y.1 <;> simp [he]

namespace Lookup

private theorem value_zero (n : ℕ) : value n (zero n) = 0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [value, zero, ih]

private theorem value_inc (n : ℕ) (x : Val (word n)) (h : value n x + 1 < 2 ^ n) :
    value n (inc n x) = value n x + 1 := by
  induction n with
  | zero => simp [value] at h
  | succ n ih =>
    obtain ⟨b, y⟩ := x
    cases b
    · simp [inc, value, Nat.add_comm]
    · have hy : value n y + 1 < 2 ^ n := by
        simp [value, pow_succ] at h
        omega
      simp [inc, value, ih y hy]
      omega

theorem value_bits {n k : ℕ} (h : k < 2 ^ n) : value n (bits n k) = k := by
  induction k with
  | zero => exact value_zero n
  | succ k ih =>
    have he := ih (by omega)
    rw [bits, Function.iterate_succ_apply', ← bits, value_inc _ _ (by omega), he]

variable (F : Type) [Field F]

private theorem carry_net (n : ℕ) :
    DNet F (.pair .bit (word n)) (word n)
      (fun x => if x.1 then inc n x.2 else x.2) (4 * n + 1) := by
  induction n with
  | zero => exact DNet.table F _ _ _ (by decide)
  | succ n ih =>
    have sum := DNet.table F (.pair .bit .bit) .bit
      (fun x => if x.1 then !x.2 else x.2) (by decide)
    have carry := DNet.table F (.pair .bit .bit) .bit (fun x => x.1 && x.2) (by decide)
    have h := ((sum.pair carry).plug ih).pre (Rewire.assoc' .bit .bit (word n))
    convert h.mono (n := 4 * (n + 1) + 1) (by simp only [wd]; omega) using 1
    funext ⟨c, b, x⟩
    cases c <;> cases b <;> rfl

theorem inc_net (n : ℕ) : DNet F (word n) (word n) (inc n) (100 * (1 + n)) := by
  cases n with
  | zero => exact (DNet.table F _ _ _ (by decide)).mono (by decide)
  | succ n =>
    have h := DNet.table F .bit (.pair .bit .bit) (fun b => (!b, b)) (by decide)
    exact (h.plug (carry_net F n)).mono (by omega)

theorem weight_net (n : ℕ) (z : F) :
    Net F .unit (word n) (fun _ y => z ^ value n y) n := by
  induction n generalizing z with
  | zero => simpa [value] using (Net.empty (F := F))
  | succ n ih =>
    have h := Net.table (F := F) .unit .bit (fun _ b => z ^ b.toNat) (by decide)
    have hh := (h.par (ih (z ^ 2))).pre (Rewire.unit' .unit)
    simpa [value, pow_add, pow_mul, Nat.add_comm] using hh

end Lookup
end OAI.LinearAlgebra.MatrixExponent
