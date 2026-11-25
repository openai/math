import OAI.LinearAlgebra.FiniteFourier.Circuit

/-! # Clearing rational coefficients in binary linear circuits

Store each rational wire multiplied by its own positive integer scale. Multiplying
by a literal adds its denominator to the scale. At a weighted sum, align the two
resulting scales by a common multiple. Both integer ratios become gate coefficients,
so every wire address and the exact number of binary gates are preserved.
-/

namespace OAI
namespace LinearAlgebra
namespace FiniteFourier

variable {I O W : Type*} {r : ℕ}

/-- Addresses of both parents at every gate, with the weights erased. -/
def Program.wiring {R : Type*} : {r : ℕ} → Program R I r → Program Unit I r
  | _, .nil => .nil
  | _, .step p g => .step p.wiring ⟨g.left, g.right, (), ()⟩

/-- The address selected by an output, with its coefficient erased. -/
def Readout.wiring {R : Type*} : Readout R W → Readout Unit W
  | .zero => .zero
  | .scaled _ w => .scaled () w

/-- The wiring diagram includes the zero and selected readouts. -/
def Circuit.wiring {R : Type*} (p : Circuit R I O r) : Circuit Unit I O r :=
  ⟨p.program.wiring, fun o => (p.output o).wiring⟩

/-- Every weight used by the program has its reduced denominator in `S`. -/
def Program.DenominatorsIn : {r : ℕ} → Program ℚ I r → Submonoid ℕ → Prop
  | _, .nil, _ => True
  | _, .step p g, S => p.DenominatorsIn S ∧ g.leftCoeff.den ∈ S ∧ g.rightCoeff.den ∈ S

def Readout.DenominatorsIn (z : Readout ℚ W) (S : Submonoid ℕ) : Prop :=
  match z with
  | .zero => True
  | .scaled c _ => c.den ∈ S

def Circuit.DenominatorsIn (p : Circuit ℚ I O r) (S : Submonoid ℕ) : Prop :=
  p.program.DenominatorsIn S ∧ ∀ o, (p.output o).DenominatorsIn S

/-- A common-multiple rule for aligning scales within the permitted submonoid. -/
structure WireAlignment (S : Submonoid ℕ) where
  common : ℕ → ℕ → ℕ
  left_dvd (a b) : a ∣ common a b
  right_dvd (a b) : b ∣ common a b
  positive {a b} : 0 < a → 0 < b → 0 < common a b
  supported {a b} : a ∈ S → b ∈ S → common a b ∈ S

/-- Products work for arbitrary multiplicative submonoids. -/
def WireAlignment.product (S : Submonoid ℕ) : WireAlignment S where
  common := (· * ·)
  left_dvd := Nat.dvd_mul_right
  right_dvd a b := Nat.dvd_mul_left b a
  positive := Nat.mul_pos
  supported := S.mul_mem

/-- The manuscript's least-common-multiple scale at each sum. -/
def WireAlignment.lcm (S : Submonoid ℕ) (hlcm : ∀ {a b}, a ∈ S → b ∈ S → a.lcm b ∈ S) :
    WireAlignment S where
  common := Nat.lcm
  left_dvd := Nat.dvd_lcm_left
  right_dvd := Nat.dvd_lcm_right
  positive := Nat.lcm_pos
  supported := hlcm

private def alignedWeight (c : ℚ) (d t : ℕ) : ℤ := (t / (c.den * d) : ℕ) * c.num

private theorem alignedWeight_spec (c : ℚ) {d t : ℕ} (h : c.den * d ∣ t) :
    (alignedWeight c d t : ℚ) * d = t * c := by
  have hnum : (c.num : ℚ) = c * c.den :=
    (div_eq_iff (Nat.cast_ne_zero.mpr c.den_ne_zero)).mp c.num_div_den
  have ht := Nat.div_mul_cancel h
  have ht' : (↑(t / (c.den * d)) : ℚ) * (↑c.den * ↑d) = ↑t := by exact_mod_cast ht
  simp only [alignedWeight, Int.cast_mul, Int.cast_natCast, hnum]
  rw [← ht']
  ring

private structure ClearedProgram (p : Program ℚ I r) (S : Submonoid ℕ) (D : I → ℕ) where
  program : Program ℤ I r
  wiring : program.wiring = p.wiring
  scale : Fin r → ℕ
  supported (j) : 0 < scale j ∧ scale j ∈ S
  agrees (x : I → ℤ) (j) :
    (program.value x j : ℚ) = scale j * p.value (fun i => (x i : ℚ) / D i) j

private def clearProgram (S : Submonoid ℕ) (L : WireAlignment S)
    (D : I → ℕ) (hD : ∀ i, 0 < D i ∧ D i ∈ S) :
    {r : ℕ} → (p : Program ℚ I r) → p.DenominatorsIn S → ClearedProgram p S D
  | _, .nil, _ => ⟨.nil, rfl, Fin.elim0, (fun j => j.elim0), fun _ j => j.elim0⟩
  | _, .step p g, hg => by
    let q := clearProgram S L D hD p hg.1
    let d := Sum.elim D q.scale
    have hd (w) : 0 < d w ∧ d w ∈ S := by cases w with
      | inl i => exact hD i
      | inr j => exact q.supported j
    let a := g.leftCoeff.den * d g.left
    let b := g.rightCoeff.den * d g.right
    let t := L.common a b
    let k : BinaryGate ℤ _ := ⟨g.left, g.right,
      alignedWeight g.leftCoeff (d g.left) t, alignedWeight g.rightCoeff (d g.right) t⟩
    refine ⟨q.program.step k, ?_, Fin.cases t q.scale, ?_, ?_⟩
    · change Program.step q.program.wiring _ = Program.step p.wiring _
      rw [q.wiring]
    · refine Fin.cases ?_ q.supported
      exact ⟨L.positive (Nat.mul_pos g.leftCoeff.den_pos (hd _).1)
        (Nat.mul_pos g.rightCoeff.den_pos (hd _).1),
        L.supported (S.mul_mem hg.2.1 (hd _).2) (S.mul_mem hg.2.2 (hd _).2)⟩
    · intro x
      refine Fin.cases ?_ (q.agrees x)
      let y (i : I) := (x i : ℚ) / D i
      have hw (w) : ((Sum.elim x (q.program.value x) w : ℤ) : ℚ) =
          d w * Sum.elim y (p.value y) w := by cases w with
        | inl i => exact (mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (hD i).1.ne')).symm
        | inr j => exact q.agrees x j
      change ((k.eval (Sum.elim x (q.program.value x)) : ℤ) : ℚ) =
        t * g.eval (Sum.elim y (p.value y))
      simp only [BinaryGate.eval, k, Int.cast_add, Int.cast_mul, hw, ← mul_assoc, mul_add]
      rw [alignedWeight_spec g.leftCoeff (d := d g.left) (t := t) (L.left_dvd a b),
        alignedWeight_spec g.rightCoeff (d := d g.right) (t := t) (L.right_dvd a b)]

private structure ClearedReadout (z : Readout ℚ W) (S : Submonoid ℕ) (D : W → ℕ) where
  readout : Readout ℤ W
  wiring : readout.wiring = z.wiring
  scale : ℕ
  supported : 0 < scale ∧ scale ∈ S
  agrees (x : W → ℤ) (y : W → ℚ) (h : ∀ w, (x w : ℚ) = D w * y w) :
    (readout.eval x : ℚ) = scale * z.eval y

private def clearReadout (S : Submonoid ℕ) (D : W → ℕ) (hD : ∀ i, 0 < D i ∧ D i ∈ S) :
    (z : Readout ℚ W) → z.DenominatorsIn S → ClearedReadout z S D
  | .zero, _ => ⟨.zero, rfl, 1, ⟨by decide, S.one_mem⟩, by intros; simp [Readout.eval]⟩
  | .scaled c w, hc => by
    refine ⟨.scaled c.num w, rfl, c.den * D w,
      ⟨Nat.mul_pos c.den_pos (hD w).1, S.mul_mem hc (hD w).2⟩, ?_⟩
    intro x y h
    have hnum : (c.num : ℚ) = c * c.den :=
      (div_eq_iff (Nat.cast_ne_zero.mpr c.den_ne_zero)).mp c.num_div_den
    simp only [Readout.eval, Int.cast_mul, Nat.cast_mul]
    rw [h w, hnum]
    ring

/-- The scale and agreement statement holds separately for every stored register. -/
theorem Program.clearDenominatorsWith (p : Program ℚ I r) (S : Submonoid ℕ)
    (L : WireAlignment S) (hp : p.DenominatorsIn S) (D : I → ℕ)
    (hD : ∀ i, 0 < D i ∧ D i ∈ S) :
    ∃ (q : Program ℤ I r) (T : Fin r → ℕ), q.wiring = p.wiring ∧
      (∀ j, 0 < T j ∧ T j ∈ S) ∧ ∀ (x : I → ℤ) (j : Fin r),
        (q.value x j : ℚ) = T j * p.value (fun i => (x i : ℚ) / D i) j := by
  let q := clearProgram S L D hD p hp
  exact ⟨q.program, q.scale, q.wiring, q.supported, q.agrees⟩

/-- A scaled readout clears with the product of the wire scale and its literal
denominator. A zero readout uses scale one. -/
theorem Readout.clearDenominators (z : Readout ℚ W) (S : Submonoid ℕ)
    (hz : z.DenominatorsIn S) (D : W → ℕ) (hD : ∀ w, 0 < D w ∧ D w ∈ S) :
    ∃ (z' : Readout ℤ W) (t : ℕ), z'.wiring = z.wiring ∧ (0 < t ∧ t ∈ S) ∧
      ∀ (x : W → ℤ) (y : W → ℚ), (∀ w, (x w : ℚ) = D w * y w) →
        (z'.eval x : ℚ) = t * z.eval y := by
  let z' := clearReadout S D hD z hz
  exact ⟨z'.readout, z'.scale, z'.wiring, z'.supported, z'.agrees⟩

/-- Clear all rational gate and readout weights, preserving every wire address.
The chosen alignment controls how both parent scales combine at each gate. -/
theorem Circuit.clearDenominatorsWith (p : Circuit ℚ I O r) (S : Submonoid ℕ)
    (L : WireAlignment S) (hp : p.DenominatorsIn S) (D : I → ℕ)
    (hD : ∀ i, 0 < D i ∧ D i ∈ S) :
    ∃ (q : Circuit ℤ I O r) (T : O → ℕ), q.wiring = p.wiring ∧
      (∀ o, 0 < T o ∧ T o ∈ S) ∧ ∀ (x : I → ℤ) (o : O),
        (q.eval x o : ℚ) = T o * p.eval (fun i => (x i : ℚ) / D i) o := by
  let u := clearProgram S L D hD p.program hp.1
  let d := Sum.elim D u.scale
  have hd (w) : 0 < d w ∧ d w ∈ S := by cases w with
    | inl i => exact hD i
    | inr j => exact u.supported j
  let v (o) := clearReadout S d hd (p.output o) (hp.2 o)
  refine ⟨⟨u.program, fun o => (v o).readout⟩, fun o => (v o).scale, ?_,
    fun o => (v o).supported, ?_⟩
  · exact congrArg₂ Circuit.mk u.wiring (funext fun o => (v o).wiring)
  · intro x o
    apply (v o).agrees
    intro w
    cases w with
    | inl i => exact (mul_div_cancel₀ _ (Nat.cast_ne_zero.mpr (hD i).1.ne')).symm
    | inr j => exact u.agrees x j

/-- The product alignment preserves any multiplicative support condition. -/
theorem Circuit.clearDenominators (p : Circuit ℚ I O r) (S : Submonoid ℕ)
    (hp : p.DenominatorsIn S) (D : I → ℕ) (hD : ∀ i, 0 < D i ∧ D i ∈ S) :
    ∃ (q : Circuit ℤ I O r) (T : O → ℕ),
      (∀ o, 0 < T o ∧ T o ∈ S) ∧ ∀ (x : I → ℤ) (o : O),
        (q.eval x o : ℚ) = T o * p.eval (fun i => (x i : ℚ) / D i) o := by
  obtain ⟨q, T, _, hT, he⟩ := p.clearDenominatorsWith S (WireAlignment.product S) hp D hD
  exact ⟨q, T, hT, he⟩

end FiniteFourier
end LinearAlgebra
end OAI
