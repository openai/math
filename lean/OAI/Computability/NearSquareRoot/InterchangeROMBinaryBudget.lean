import OAI.Computability.NearSquareRoot.InterchangeROMBinaryHeader

/-! # Charges of the padded native rectangle in the binary geometry

The two moving axes each expand by at most one factor of the selected
radix. The numerical coefficient absorbs those factors and the unary
encoding of that radix, while the polynomial degree stays uniform.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMBinary.Ticket

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom

open private room_bounded from OAI.Computability.NearSquareRoot.InterchangeBeadThreshold

/-- The same coefficient suffices for both adapter passes and the native call. -/
def coefficient (b D : ℕ) := b^2*((2*b+3)^D+1)

theorem dense_count (x : Ticket) : x.rows.count = x.grid.denseVolume := by
  change ((layout x.P).cart ((line 2 x.n).cart ((layout x.G).cart
    ((line 2 x.n).cart (layout x.B))))).count = _
  simp only [Series.count_cart]
  rw [lineSize]
  simp only [space,grid,BinaryHalo.Shape.denseVolume]
  ring

theorem total_bound (x : Ticket) : x.total ≤ x.b^2*x.rows.count := by
  have h := (width_bounds x.radix_ok x.n).2.2.2
  rw [dense_count]
  change room x.P*(x.b^x.e)*room x.G*(x.b^x.e)*room x.B ≤
    x.b^2*(room x.P*(2^x.n)*room x.G*(2^x.n)*room x.B)
  calc
    _ ≤ room x.P*(x.b*2^x.n)*room x.G*(x.b*2^x.n)*room x.B := by gcongr
    _ = _ := by ring

/-- The chosen padding suffices for the thickness condition even when the
original payload is empty. -/
theorem pad_thick (k : ℕ) (x : Ticket) : (Nat.log 2 x.total+1)^k ≤ pad k x := by
  have p := room_bounded x.b x.P (fun d hd => (x.admissible d (by simp [hd])).2.trans x.large)
  have g := room_bounded x.b x.G (fun d hd => (x.admissible d (by simp [hd])).2.trans x.large)
  have z := room_bounded x.b x.B (fun d hd => (x.admissible d (by simp [hd])).2.trans x.large)
  have card : x.total ≤ x.b^(digitCount x) := by
    simp only [grid,total,BinaryHalo.Shape.volume,digitCount,pow_add]
    gcongr
  have exp : x.total ≤ 2^(x.b*digitCount x) := by
    rw [pow_mul]
    exact card.trans (Nat.pow_le_pow_left Nat.lt_two_pow_self.le _)
  have lg := Nat.log_mono_right (b:=2) exp
  rw [Nat.log_pow (by decide)] at lg
  exact Nat.pow_le_pow_left (Nat.succ_le_succ lg) _

private theorem tape_length (l : Tape) : l.length ≤ size (shape l) := by
  induction l with
  | nil => simp
  | cons x xs ih => rw [List.length_cons,shape_cons,size_cons]; omega

theorem digits_le (x : Ticket) : digitCount x ≤ x.description.count := by
  have p := tape_length x.P
  have g := tape_length x.G
  have z := tape_length x.B
  have e := (width_bounds x.radix_ok x.n).2.1
  change x.P.length + x.e + x.G.length + x.e + x.B.length ≤ size (tally x.n) +
    (size (shape x.P)+(size (shape x.G)+size (shape x.B)+1)+1)+1
  rw [size_tally,tally_length]
  change x.e ≤ x.n+1 at e
  omega

theorem pad_bound (k : ℕ) (x : Ticket) :
    pad k x ≤ (2*x.b+3)^k*(x.description.count+1)^k := by
  rw [← Nat.mul_pow]
  apply Nat.pow_le_pow_left
  have h := Nat.mul_le_mul_left x.b (digits_le x)
  rw [Nat.add_mul,Nat.mul_add,Nat.mul_one,Nat.mul_assoc]
  omega

theorem compact_bound (x : Ticket) :
    size x.compact+1 ≤ (2*x.b+3)*(x.description.count+1) := by
  change size (tally x.b)+x.description.count+1+1 ≤ _
  rw [size_tally,tally_length,Nat.mul_add,Nat.mul_one,Nat.add_mul]
  omega

private theorem absorb (N N' w H p A B : ℕ) (row : N'≤B*N) (hcost : p≤A*H)
    (one : 0<H) : N'*(w+p+1) ≤ B*(A+1)*(N*(w+H)) := calc
  _ ≤ (B*N)*((A+1)*(w+H)) := by
    apply Nat.mul_le_mul row
    rw [Nat.add_mul,Nat.one_mul,Nat.mul_add]
    omega
  _ = _ := by ring

theorem native_budget (k D : ℕ) (hk : k≤D) (x : Ticket) :
    x.total * (pad k x + x.w + 1) ≤ coefficient x.b D * x.toPacket.mass D := by
  let A := (2*x.b+3)^D
  let H := (x.description.count+1)^D
  have p := (pad_bound k x).trans (Nat.mul_le_mul
    (Nat.pow_le_pow_right (by omega : 0<2*x.b+3) hk)
    (Nat.pow_le_pow_right (Nat.succ_pos _) hk))
  rw [Nat.add_comm (pad k x) x.w]
  change x.total*(x.w+pad k x+1) ≤ (x.b^2*(A+1))*(x.rows.count*(x.w+H))
  exact
    absorb x.rows.count x.total x.w H (pad k x) A (x.b^2) (total_bound x) p
      (Nat.pow_pos (Nat.succ_pos _))

theorem adapter_budget (t D : ℕ) (ht : t≤D) (x : Ticket) :
    ⌈mass regime total (fun x => x.w) t x⌉₊ ≤ coefficient x.b D*x.toPacket.mass D := by
  have c : (size x.compact+1)^t ≤ (2*x.b+3)^D*(x.description.count+1)^D := by
    rw [← Nat.mul_pow]
    exact (Nat.pow_le_pow_left (compact_bound x) t).trans
      (Nat.pow_le_pow_right (Nat.mul_pos (by omega) (Nat.succ_pos _)) ht)
  have high := absorb x.rows.count x.total x.w _ ((size x.compact+1)^t) _
    (x.b^2) (total_bound x) c (Nat.pow_pos (Nat.succ_pos _))
  have low : x.total*(x.w+(size x.compact+1)^t) ≤ coefficient x.b D*x.toPacket.mass D :=
    (Nat.mul_le_mul_left x.total (Nat.le_succ _)).trans high
  apply Nat.ceil_le.mpr
  simpa only [mass,regime,Nat.cast_mul,Nat.cast_add,Nat.cast_pow,Nat.cast_one] using
    (Nat.cast_le.mpr low : ((x.total*(x.w+(size x.compact+1)^t):ℕ):ℝ) ≤ _)

/-- The native recursive clock uses the native field width, which also
covers a zero-width binary packet using one digit. -/
theorem native_time (k D : ℕ) (hk : k≤D) (ρ : ℝ) (hρ : 0≤ρ) (x : Ticket) :
    ⌈((x.total*(pad k x+x.w+1):ℕ):ℝ)*(x.e:ℝ)^ρ⌉₊ ≤
      coefficient x.b D*time ρ (x.toPacket.mass D) x.n := by
  have V := native_budget k D hk x
  have width := (width_bounds x.radix_ok x.n).2.1
  have expon : (x.e:ℝ)^ρ ≤ ((x.n+1:ℕ):ℝ)^ρ :=
    Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast width) hρ
  have value := mul_le_mul (Nat.cast_le.mpr V : ((x.total*(pad k x+x.w+1):ℕ):ℝ) ≤ _)
    expon (Real.rpow_nonneg (Nat.cast_nonneg _) _) (Nat.cast_nonneg _)
  apply Nat.ceil_le.mpr
  calc
    _ ≤ ((coefficient x.b D*x.toPacket.mass D:ℕ):ℝ)*((x.n+1:ℕ):ℝ)^ρ := value
    _ = (coefficient x.b D:ℝ)*((x.toPacket.mass D:ℝ)*((x.n+1:ℕ):ℝ)^ρ) := by rw [Nat.cast_mul,mul_assoc]
    _ ≤ (coefficient x.b D:ℝ)*(time ρ (x.toPacket.mass D) x.n:ℝ) :=
      mul_le_mul_of_nonneg_left (Nat.le_ceil _) (Nat.cast_nonneg _)
    _ = _ := (Nat.cast_mul ..).symm

theorem mass_le_time (D : ℕ) (ρ : ℝ) (hρ : 0 ≤ ρ) (x : Ticket) :
    x.toPacket.mass D ≤ time ρ (x.toPacket.mass D) x.n := by
  have rate : (1:ℝ) ≤ ((x.n+1:ℕ):ℝ)^ρ :=
    Real.one_le_rpow (by exact_mod_cast Nat.succ_le_succ (Nat.zero_le x.n)) hρ
  have bound := le_mul_of_one_le_right (Nat.cast_nonneg (α:=ℝ) (x.toPacket.mass D)) rate
  exact_mod_cast bound.trans (Nat.le_ceil _)

theorem computable_coefficient {X : Type} [Primcodable X] (D : ℕ) {b : X → ℕ} (hb : Computable b) :
    Computable fun x => coefficient (b x) D := by
  have z := Primrec.nat_add.to_comp.comp (Primrec.nat_mul.to_comp.comp (.const 2) hb) (.const 3)
  have p (k : ℕ) : Computable (fun x => (2*b x+3)^k) := by
    induction k with
    | zero => simpa only [pow_zero] using (Computable.const (α:=X) 1)
    | succ k ih => simpa only [pow_succ] using Primrec.nat_mul.to_comp.comp ih z
  simpa only [coefficient,pow_two] using Primrec.nat_mul.to_comp.comp
    (Primrec.nat_mul.to_comp.comp hb hb) (Primrec.succ.to_comp.comp (p D))

end InterchangeROMBinary.Ticket

end NearSquareRoot
end Computability
end OAI
