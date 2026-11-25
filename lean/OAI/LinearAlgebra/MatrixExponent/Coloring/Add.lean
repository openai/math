import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import OAI.LinearAlgebra.MatrixExponent.Coloring.Shift

section
/-! # Ripple-carry addition of addresses modulo `2^n` -/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

private abbrev args (n : ℕ) := Wire.pair .bit (.pair (word n) (word n))
private abbrev two := Wire.pair .bit .bit

private def full (x : Val (.pair .bit two)) : Val two :=
  let k := x.1.toNat + x.2.1.toNat + x.2.2.toNat
  (decide (k % 2 = 1), decide (2 ≤ k))

private theorem full_sum (b p q : Bool) :
    b.toNat + p.toNat + q.toNat = (full (b, p, q)).1.toNat + 2 * (full (b, p, q)).2.toNat := by
  cases b <;> cases p <;> cases q <;> decide

private def addBits : (n : ℕ) → Val (args n) → Val (word n)
  | 0, _ => ()
  | n + 1, x =>
    let z := full (x.1, x.2.1.1, x.2.2.1)
    (z.1, addBits n (z.2, x.2.1.2, x.2.2.2))

private theorem add_value (n : ℕ) (b : Bool) (x y : Val (word n)) :
    ∃ k, b.toNat + Lookup.value n x + Lookup.value n y =
      Lookup.value n (addBits n (b, x, y)) + k * 2 ^ n := by
  induction n generalizing b with
  | zero => exact ⟨b.toNat, by simp [Lookup.value]⟩
  | succ n ih =>
    let z := full (b, x.1, y.1)
    obtain ⟨k, hk⟩ := ih z.2 x.2 y.2
    refine ⟨k, ?_⟩
    simp only [Lookup.value, addBits, pow_succ, ← mul_assoc]
    have := full_sum b x.1 y.1
    unfold z at hk
    omega

variable (F : Type) [Field F]

private theorem addBits_net (n : ℕ) : DNet F (args n) (word n) (addBits n) (256 * n + 1) := by
  induction n with
  | zero => exact DNet.table F _ _ _ (by decide)
  | succ n ih =>
    have gate : DNet F (.pair .bit two) two full 256 := by
      obtain ⟨m, hm, hle⟩ := Net.dense (.pair .bit two) two (fun x y => if full x = y then (1 : F) else 0)
      exact ⟨m, hle, hm⟩
    have r := ((Rewire.id .bit).par (.middle .bit (word n) .bit (word n))).comp (.assoc' _ _ _)
    exact ((gate.plug ih).pre r).mono (by omega)

theorem numeric_add (n : ℕ) :
    Circuit F (.pair (.addr n) (.addr n)) (.addr n) (fun x => x.1 + x.2) (10000 * (1 + n)) := by
  have seed := ((Lookup.const_net F .bit false).par (DNet.id F (.pair (word n) (word n)))).pre
    ((Rewire.unit' _).comp (.swap _ _))
  have h := seed.comp (addBits_net F n)
  apply Circuit.of_dnet (.refl _) (.refl _) (h.mono (n := 10000 * (1 + n)) (by simp [wd]; omega))
  intro x
  simp only [Equiv.coe_refl, Function.comp_id]
  rw [decode_pair, ← code_addr]
  congr 1
  apply Fin.ext
  change Lookup.value n (addBits n (false, x)) = (Lookup.value n x.1 + Lookup.value n x.2) % 2 ^ n
  obtain ⟨k, hk⟩ := add_value n false x.1 x.2
  simp only [Bool.toNat_false, zero_add] at hk
  rw [hk, Nat.add_mul_mod_self_right, Nat.mod_eq_of_lt (Control.value_lt ..)]

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

section
/-!
# A circuit for alternating colours

Keep the orbit minimum and the next pointer at every position.
Two gathers and a pointwise minimum double the range in one step.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

private abbrev tables (h : ℕ) := Format.pair (Perm h) (Perm h)

private def tick (h : ℕ) (x : (tables h).obj) : (tables h).obj :=
  (x.1 ∘ x.1, fun i => min (x.2 i) (x.2 (x.1 i)))

private theorem ticks (h k : ℕ) (P : B h → B h) :
    (tick h)^[k] (P, id) = (jump P k, low P k) := by
  induction k with
  | zero => rfl
  | succ k ih => rw [Function.iterate_succ_apply', ih]; rfl

variable (F : Type) [Field F]

theorem cheap_colour (h : ℕ) :
    Cheap F h h (.pair (Perm h) (Perm h)) (.vec h .bit) (fun x => colour h x.1 x.2) 50 := by
  have hw : (tables h).width ≤ 2 ^ h * (100 + h) ^ 2 := by
    simp only [Format.width_pair, Format.width_vec, Format.width_addr, ← mul_add]
    gcongr
    nlinarith
  have hv : (Perm h).width ≤ 2 ^ h * (100 + h) ^ 2 :=
    le_trans (by rw [Format.width_pair]; omega) hw
  have base := Cheap.id F hw
  have first := base.fst
  have second := base.snd
  have minimum : Cheap F 0 h (.pair (.addr h) (.addr h)) (.addr h) (fun x => min x.1 x.2) 3 :=
    ⟨_, numeric_min F h, by simp only [Format.width_addr, Format.width_pair]; ring_nf; omega⟩
  have cmp : Cheap F 0 h (.pair (.addr h) (.addr h)) .bit (fun x => decide (x.1 < x.2)) 3 :=
    ⟨_, numeric_lt F h, by
      simp only [Format.width_addr, Format.width_pair]
      have := Format.width_bit
      ring_nf
      omega⟩
  have gather := Cheap.lookup F h h (.addr h) le_rfl (Format.width_addr h).le
  have stride := (first.pair first).comp gather
  have next := (second.pair first).comp gather
  have merge := (second.pair next).zip.comp (Cheap.map _ (fun _ : B h => minimum))
  have step : Cheap F h h (tables h) (tables h) (tick h) 15 :=
    (stride.pair merge).mono (by decide)
  have start := next.pair (Cheap.const F hw hv id)
  have scan := (start.comp (step.iterate le_rfl)).snd
  have mins : Cheap F h h (tables h) (Perm h) (fun x => low (x.2 ∘ x.1) h) 20 := by
    convert scan.mono (d := 20) (by decide) using 1
    funext x
    exact (congrArg Prod.snd (ticks h h (x.2 ∘ x.1))).symm
  have mirror := (mins.pair first).comp gather
  exact ((mins.pair mirror).zip.comp (Cheap.map _ (fun _ : B h => cmp))).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

section
/-!
# Computing balanced edge splits

Sort edges by endpoint and activity. At every active edge, use the
inverse order to find its rank, pair neighboring ranks, and retrieve
the partner. The two resulting arrays determine the colouring.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

abbrev GraphInput (h k : ℕ) := Format.pair (.pair (.vec h (.addr k)) (.vec h (.addr k))) (.vec h .bit)

theorem graph_width (h k : ℕ) : (GraphInput h k).width = 2 ^ h * (2 * k + 1) := by
  simp only [Format.width_pair, Format.width_vec, Format.width_addr]
  rw [Format.width_bit]; ring

variable (F : Type) [Field F]

theorem cheap_select (n : ℕ) :
    Cheap F 0 n (.pair (.pair (.addr n) (.addr n)) .bit) (.addr n)
      (fun x => if x.2 then x.1.1 else x.1.2) 3 :=
  ⟨_, numeric_select F n, by
    simp only [Format.width_pair, Format.width_addr]
    rw [Format.width_bit]; ring_nf; omega⟩

private abbrev endInput (h k : ℕ) := Format.pair (.vec h (.addr k)) (.vec h .bit)

theorem cheap_partner (h k : ℕ) :
    Cheap F h (h + k) (.pair (.vec h (.addr k)) (.vec h .bit)) (Perm h)
      (fun x => partner x.1 x.2) 120 := by
  have hi : (endInput h k).width ≤ 2 ^ h * (100 + (h + k)) ^ 1 := by
    simp only [Format.width_pair, Format.width_vec, Format.width_addr, ← mul_add, pow_one]
    rw [Format.width_bit]; apply Nat.mul_le_mul_left; omega
  have hp : (Perm h).width ≤ 2 ^ h * (100 + (h + k)) ^ 1 := by
    simp only [Format.width_vec, Format.width_addr, pow_one]; apply Nat.mul_le_mul_left; omega
  have base := Cheap.id F hi
  have self := Cheap.const F hi hp id
  have flip := Cheap.const F hi hp (toggle h)
  have get := Cheap.lookup F h (h + k) (.addr h) (by omega) (by rw [Format.width_addr]; omega)
  have perm := cheap_permutation F h k
  obtain ⟨f, hf, he⟩ := cheap_inverse F h
  have inv' : Cheap F h (h + k) (endInput h k) (Perm h)
      (fun x => ⇑(permutation x.1 x.2).symm) 101 := by
    convert (perm.comp (hf.widen (l := h + k) (by omega))).mono (d := 101) (by decide) using 1
    funext x
    exact (he _).symm
  have other := (perm.pair ((flip.pair inv').comp get)).comp get
  have args := ((other.pair self).zip.pair base.snd).zip
  have choose := Cheap.map _ (fun _ : B h => (cheap_select F h).widen (l := h + k) (by omega))
  exact (args.comp choose).mono (by decide)

theorem cheap_split (h k : ℕ) :
    Cheap F h (h + k) (GraphInput h k) (.vec h .bit) (fun x => split x.1.1 x.1.2 x.2) 130 := by
  have hw : (GraphInput h k).width ≤ 2 ^ h * (100 + (h + k)) ^ 2 := by
    rw [graph_width]; apply Nat.mul_le_mul_left; ring_nf; omega
  have base := Cheap.id F hw
  have other := cheap_partner F h k
  have left := (base.fst.fst.pair base.snd).comp other
  have right := (base.fst.snd.pair base.snd).comp other
  exact ((left.pair right).comp ((cheap_colour F h).widen (l := h + k) (by omega))).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Coloring
end
