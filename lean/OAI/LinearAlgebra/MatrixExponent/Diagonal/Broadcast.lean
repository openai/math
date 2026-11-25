import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Nat.Log
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Replay
import OAI.LinearAlgebra.MatrixExponent.Diagonal.TemplateSize
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Fixing
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Bounds
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import OAI.LinearAlgebra.MatrixExponent.Diagonal.Input
import OAI.LinearAlgebra.MatrixExponent.Tagged.Array
import OAI.LinearAlgebra.MatrixExponent.Transcript.Seats
import OAI.LinearAlgebra.MatrixExponent.Diagram.Present
import OAI.LinearAlgebra.MatrixExponent.Tagged.Reduction

section
/-! # Choosing processor, batch, and broadcast lengths -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

open Filter

/-- Simultaneous bounds for the cube layout, packet budget, and processor tape. -/
structure Scales (C k h I N r l b d D B : ℕ) : Prop where
  pos : 0 < r
  labels : r ^ k ≤ l
  tape : l + b + N / 4 ≤ N
  literal : 1024 * l ≤ N
  links : 64 * (3 * r) ^ 2 ≤ N
  cover : 3 * r ≤ B * d
  copies : B * d ≤ 4 * r
  degree : (D + 1) * (r ^ k) ^ 4 ≤ C * N * d
  padding : (r ^ k) ^ 2 * 2 ^ k * h ≤ C * N * d
  broadcast : Nat.clog 2 k + r ^ 3 * I * Nat.clog 2 (52 * C * N * r + 1) + 1 ≤ b

private theorem batch_size (d r : ℕ) (hd : 1 ≤ d) (hr : d ^ 2 ≤ r) :
    3 * r ≤ ((3 * r + d - 1) / d) * d ∧ ((3 * r + d - 1) / d) * d ≤ 4 * r := by
  have := (Nat.le_pow (by decide : 0 < 2)).trans hr
  have hm := Nat.mod_lt (3 * r + d - 1) hd
  have he := Nat.mod_add_div (3 * r + d - 1) d
  rw [Nat.mul_comm d] at he
  omega

private theorem scale_bounds {C k h I N r d D : ℕ} (hc : 4 ≤ C) (hk : 2 ≤ k)
    (hr : 6144 ≤ r) (hp : r ^ (8 * k) ≤ N) (hpad : 2 ^ k * h ≤ r)
    (hi : I ≤ r) (hk' : Nat.clog 2 k ≤ r) (hrep : Nat.clog 2 (52 * C * N * r + 1) ≤ r)
    (hd : 1 ≤ d) (hd' : d ^ 2 ≤ r) (hD : D ^ 2 ≤ N) :
    Scales C k h I N r (N / 2048) (N / 2048) d D ((3 * r + d - 1) / d) := by
  have pow_bound (j : ℕ) (hj : j ≤ 8 * k) : r ^ j ≤ N :=
    (Nat.pow_le_pow_right (by omega) hj).trans hp
  have hCN : 2 * N ≤ C * N * d := by
    exact (Nat.mul_le_mul_right N (by omega : 2 ≤ C)).trans (Nat.le_mul_of_pos_right _ hd)
  obtain ⟨hlo, hhi⟩ := batch_size d r hd hd'
  refine ⟨by omega, ?_, by omega, by omega, ?_, hlo, hhi, ?_, ?_, ?_⟩
  · apply (Nat.le_div_iff_mul_le (by decide)).mpr
    calc
      _ ≤ r ^ k * r := Nat.mul_le_mul_left _ (by omega)
      _ ≤ N := by rw [← pow_succ]; exact pow_bound _ (by omega)
  · calc
      _ = r ^ 2 * 576 := by ring
      _ ≤ r ^ 2 * r := Nat.mul_le_mul_left _ (by omega)
      _ ≤ N := pow_bound 3 (by omega)
  · let p := (r ^ k) ^ 4
    have hs : p ^ 2 ≤ N := by
      unfold p
      rw [← pow_mul, ← pow_mul]
      exact pow_bound _ (by omega)
    have hv : D * p ≤ N := by
      rcases le_total D p with h | h
      · exact (Nat.mul_le_mul_right p h).trans (by rwa [pow_two] at hs)
      · exact (Nat.mul_le_mul_left D h).trans (by rwa [pow_two] at hD)
    change (D + 1) * p ≤ _
    rw [Nat.add_mul, one_mul]
    have := (Nat.le_pow (by decide : 0 < 2)).trans hs
    omega
  · calc
      _ ≤ (r ^ k) ^ 2 * r := by rw [mul_assoc]; exact Nat.mul_le_mul_left _ hpad
      _ ≤ N := by rw [← pow_mul, ← pow_succ]; exact pow_bound _ (by omega)
      _ ≤ C * N * d := by omega
  · have hfive : r ≤ r ^ 5 := Nat.le_pow (by decide)
    have hb : Nat.clog 2 k + r ^ 3 * I * Nat.clog 2 (52 * C * N * r + 1) + 1 ≤ 3 * r ^ 5 := by
      have : r ^ 3 * I * Nat.clog 2 (52 * C * N * r + 1) ≤ r ^ 5 :=
        Nat.mul_le_mul (Nat.mul_le_mul_left _ hi) hrep
      omega
    apply (Nat.le_div_iff_mul_le (by decide)).mpr
    calc
      _ ≤ (3 * r ^ 5) * 2048 := Nat.mul_le_mul_right _ hb
      _ = r ^ 5 * 6144 := by ring
      _ ≤ r ^ 5 * r := Nat.mul_le_mul_left _ hr
      _ ≤ N := pow_bound 6 (by omega)

private theorem square_exp (m : ℕ) (hm : 4 ≤ m) : m ^ 2 ≤ 2 ^ m := by
  induction m, hm using Nat.le_induction with
  | base => decide
  | succ m hm ih => rw [pow_succ 2]; nlinarith

private theorem small_batch {d w K m : ℕ} (hk : 0 < K) (hw : w ≤ 2 * K * m)
    (hd : (d : ℝ) ≤ ((2 : ℝ) ^ w) ^ (1 / (4 * (K : ℝ)))) : d ^ 2 ≤ 2 ^ m := by
  have hk' : 0 < (K : ℝ) := by exact_mod_cast hk
  have he : (w : ℝ) * (1 / (4 * (K : ℝ))) * 2 ≤ (m : ℝ) := by
    rw [show (w : ℝ) * (1 / (4 * (K : ℝ))) * 2 = w / (2 * (K : ℝ)) by ring,
      div_le_iff₀ (by positivity)]
    rw [mul_comm]
    exact_mod_cast hw
  have h : (d : ℝ) ^ 2 ≤ (2 : ℝ) ^ m := calc
    _ ≤ (((2 : ℝ) ^ w) ^ (1 / (4 * (K : ℝ)))) ^ 2 := by gcongr
    _ = (2 : ℝ) ^ ((w : ℝ) * (1 / (4 * (K : ℝ))) * 2) := by
      rw [← Real.rpow_natCast_mul (by positivity), ← Real.rpow_mul_natCast (by positivity)]
      rfl
    _ ≤ _ := by rw [← Real.rpow_natCast]; exact Real.rpow_le_rpow_of_exponent_le (by norm_num) he
  exact_mod_cast h

/-- Choose the sizes before the batch and degree are known. A fixed
positive exponent suffices for the batch hypothesis. -/
theorem scales (C k h I : ℕ) (hc : 4 ≤ C) (hk : 2 ≤ k) :
    ∃ δ : ℝ, 0 < δ ∧ ∀ᶠ w : ℕ in atTop,
      let N : ℕ := 2 ^ w
      let r := 2 ^ (w / (16 * k))
      let l := N / 2048
      (∀ d : ℕ, (d : ℝ) ≤ (N : ℝ) ^ δ → d ^ 2 ≤ r) ∧
      (∀ d D : ℕ, 1 ≤ d → d ^ 2 ≤ r → D ^ 2 ≤ N →
        Scales C k h I N r l l d D ((3 * r + d - 1) / d)) := by
  let K := 16 * k
  have hK : 0 < K := by omega
  let T := 6144 + 2 ^ k * h + I + Nat.clog 2 k + 52 * C + 6 * K
  refine ⟨1 / (4 * (K : ℝ)), by positivity, ?_⟩
  filter_upwards [eventually_ge_atTop (T * K)] with w hw
  intro N r l
  let m := w / K
  have hm : T ≤ m := (Nat.le_div_iff_mul_le hK).mpr hw
  have hm' : 4 ≤ m := by omega
  have hw' : w ≤ 2 * K * m := by
    have he := Nat.mod_add_div w K
    have hd := Nat.mod_lt w hK
    change w % K + K * m = w at he
    have := Nat.le_mul_of_pos_right K (by omega : 0 < m)
    rw [mul_assoc]
    omega
  constructor
  · intro d hd
    apply small_batch hK hw'
    simpa only [N, Nat.cast_pow, Nat.cast_ofNat] using hd
  · have hr : m ^ 2 ≤ r := square_exp m hm'
    have hmr := (Nat.le_pow (by decide : 0 < 2)).trans hr
    have hp : r ^ (8 * k) ≤ N := by
      change (2 ^ m) ^ (8 * k) ≤ 2 ^ w
      rw [← pow_mul]
      exact Nat.pow_le_pow_right (by decide)
        ((Nat.mul_le_mul_left m (by omega : 8 * k ≤ K)).trans (Nat.div_mul_le_self w K))
    have hrN := (Nat.le_pow (by omega : 0 < 8 * k)).trans hp
    have hw3 : 3 * w ≤ r := calc
      _ ≤ 3 * (2 * K * m) := Nat.mul_le_mul_left _ hw'
      _ = (6 * K) * m := by ring
      _ ≤ m * m := Nat.mul_le_mul_right m (by omega)
      _ ≤ _ := by rwa [← pow_two]
    have hrep : Nat.clog 2 (52 * C * N * r + 1) ≤ 3 * w := by
      apply Nat.clog_le_of_le_pow
      rw [mul_comm 3, pow_mul]
      change _ ≤ N ^ 3
      have hz : 1 ≤ N * r := Nat.mul_pos (by omega) (by omega)
      calc
        _ ≤ 52 * C * N * r + N * r := Nat.add_le_add_left hz _
        _ = (52 * C + 1) * N * r := by ring
        _ ≤ N * N * N := by gcongr; omega
        _ = _ := by ring
    intro d D hd hd' hD
    exact scale_bounds hc hk (by omega) hp (by omega) (by omega) (by omega)
      (hrep.trans hw3) hd hd' hD

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

section
/-! # Balanced exterior labels shared across all copies -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

variable {N l b r n : ℕ}

/-- Balance literals separately so that rerouting them has a small cost
even on a tape dominated by communication bits. -/
theorem exterior (hr : 0 < r) (hl : r ^ n ≤ l) (hs : l + b + N / 4 ≤ N) :
    ∃ fa : Machine.Ports N l b → Label n r,
      (∀ g, multiplicity fa g * r ^ n ≤ 4 * N) ∧
      (∀ i g, multiplicity (fun t : Fin l => fa (.inl t) i) g * r ≤ 2 * l) := by
  have : Nonempty (Fin r) := ⟨⟨0, hr⟩⟩
  have bal (k : ℕ) : ∃ f : Fin k → Label n r, ∀ z, multiplicity f z * r ^ n ≤ k + r ^ n := by
    simpa [Label] using (even_labels (A := Fin k) (Z := Label n r))
  obtain ⟨x, hx⟩ := bal l
  obtain ⟨y, hy⟩ := bal b
  obtain ⟨z, hz⟩ := bal (N / 4)
  refine ⟨Sum.elim x (Sum.elim y z), ?_, fun i g => (project_bound x hx i g).trans (by omega)⟩
  intro g
  rw [multiplicity_elim, multiplicity_elim, add_mul, add_mul]
  have := hx g
  have := hy g
  have := hz g
  omega

theorem exterior_copies (fa : Machine.Ports N l b → Label n r)
    (hfa : ∀ g, multiplicity fa g * r ^ n ≤ 4 * N) (d : ℕ) (g : Label n r) :
    multiplicity (fun s : slots (copies (Machine.tape N l b) d) =>
      fa (Machine.address N l b (port (Machine.tape N l b) d s).2)) g * r ^ n ≤ 4 * N * d := by
  let e := (port (Machine.tape N l b) d).trans
    ((Equiv.refl _).prodCongr (Machine.address N l b))
  have he : multiplicity (fun s => fa (e s).2) g ≤ d * multiplicity fa g := by
    let f : {s // fa (e s).2 = g} → Fin d × {p // fa p = g} :=
      fun s => ((e s.1).1, ⟨(e s.1).2, s.2⟩)
    have hf : Function.Injective f := by
      intro x y h
      apply Subtype.ext
      apply e.injective
      exact congrArg (fun p => (p.1, p.2.1)) h
    simpa only [multiplicity, Fintype.card_prod, Fintype.card_fin] using
      Fintype.card_le_of_injective f hf
  calc
    _ ≤ d * multiplicity fa g * r ^ n := Nat.mul_le_mul_right _ he
    _ ≤ 4 * N * d := by rw [mul_assoc, mul_comm d]; exact Nat.mul_le_mul_right _ (hfa g)

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

section
/-!
# Communication budget for literal pins

Each worker sends at most one copy of its own literal string. For
incoming literals a single label coordinate bounds the number of
relevant positions, shared across all processors.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

variable {F : Type} [Field F] {n h d r N l b : ℕ}
  (A : Expansion F n h) (hn : 2 ≤ n) (R : A.Report r d)

theorem Expansion.owner_coordinate (u : Worker r) :
    ∃ (i : Fin n) (g : Fin r), ∀ z, A.owner hn N R z = u → z i = g := by
  cases u with
  | home g =>
    refine ⟨R.1, g, ?_⟩
    intro z h
    unfold Expansion.owner at h
    split_ifs at h
    exact Worker.home.inj h
  | station g =>
    refine ⟨other hn R.1, g, ?_⟩
    intro z h
    unfold Expansion.owner at h
    split_ifs at h
    exact Worker.station.inj h
  | packet g =>
    refine ⟨R.1, g, ?_⟩
    intro z h
    unfold Expansion.owner at h
    split_ifs at h

theorem Pin.budget (fa : Machine.Ports N l b → Label n r)
    (hf : ∀ i g, multiplicity (fun t : Fin l => fa (.inl t) i) g * r ≤ 2 * l)
    (hl : 1024 * l ≤ N) (u : Worker r) :
    let f := A.owner hn N R ∘ fa
    128 * Fintype.card {e : Pin N l b r //
      Pin.src f e ≠ Pin.dst f e ∧ (Pin.src f e = u ∨ Pin.dst f e = u)} ≤ N := by
  classical
  intro f
  obtain ⟨i, g, hg⟩ := A.owner_coordinate (N := N) hn R u
  let E := {e : Pin N l b r // Pin.src f e ≠ Pin.dst f e ∧ (Pin.src f e = u ∨ Pin.dst f e = u)}
  let T := Fin l ⊕ (Fin (3 * r) × {t : Fin l // fa (.inl t) i = g})
  let pin : T → Pin N l b r :=
    Sum.elim (fun t => .inl (Worker.index r u, t)) (fun x => .inl (x.1, x.2.val))
  have cover (e : E) : ∃ t, pin t = e.val := by
    rcases e with ⟨⟨v, t⟩|e, hn', he⟩
    · rcases he with h | h
      · exact ⟨.inl t, by simp [pin, ← h, Pin.src]⟩
      · exact ⟨.inr (v, ⟨t, hg _ h⟩), rfl⟩
    · exact (hn' rfl).elim
  choose pick hp using cover
  have hi : Function.Injective pick :=
    fun x y h => Subtype.ext ((hp x).symm.trans ((congrArg pin h).trans (hp y)))
  have he := Fintype.card_le_of_injective pick hi
  have hT : Fintype.card T ≤ 7 * l := by
    simp only [T, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
    have hh : Fintype.card {t : Fin l // fa (.inl t) i = g} * r ≤ 2 * l := hf i g
    rw [mul_assoc, mul_comm r]
    omega
  change 128 * Fintype.card E ≤ N
  omega

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

/-!
# Encoding the public report

The first bit distinguishes an ordinary report from the extra branch.
A binary cut index and fixed-width binary counts follow, in lexicographic
class order. All unused bits are zero.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion

private def binary (n : ℕ) : Fin n ↪ (Fin (Nat.clog 2 n) → Bool) where
  toFun := fun x i => x.val.testBit i
  inj' := by
    intro x y h
    apply Fin.ext
    apply Nat.eq_of_testBit_eq
    intro i
    by_cases hi : i < Nat.clog 2 n
    · exact congrFun h ⟨i, hi⟩
    · have hm : n ≤ 2 ^ i := (Nat.le_pow_clog (by decide : 1 < 2) n).trans
        (Nat.pow_le_pow_right (by decide) (le_of_not_gt hi))
      rw [Nat.testBit_lt_two_pow (x.isLt.trans_le hm), Nat.testBit_lt_two_pow (y.isLt.trans_le hm)]

variable {F : Type} [Field F] {n h : ℕ} (A : Expansion F n h)
  (hn : 2 ≤ n) (N r d : ℕ)

private abbrev Count (n r d : ℕ) := Fintype.card (Packet n r d) + 1

abbrev CountBit := (Class r × A.I) × Fin (Nat.clog 2 (Fintype.card (Packet n r d) + 1))

def countBits {r d : ℕ} (R : A.Report r d) (j : A.CountBit r d) : Bool :=
  (R.2 j.1).val.testBit j.2.val

abbrev Cell := Unit ⊕ Fin (Nat.clog 2 n) ⊕ A.CountBit r d

private def fields : Option (A.Accepted (r := r) (d := d) hn (A.budget hn N)) → A.Cell r d → Bool
  | none, _ => false
  | some _, .inl _ => true
  | some R, .inr (.inl i) => binary n R.1.1 i
  | some R, .inr (.inr (z, i)) => binary (Count n r d) (R.1.2 z) i

private theorem fields_injective : Function.Injective (A.fields hn N r d) := by
  intro x y he
  have hf := congrFun he (.inl ())
  cases x <;> cases y
  · rfl
  · exact (Bool.false_ne_true hf).elim
  · exact (Bool.false_ne_true hf.symm).elim
  · apply congrArg some
    apply Subtype.ext
    apply Prod.ext
    · exact (binary n).injective (funext fun i => congrFun he (.inr (.inl i)))
    · funext z
      exact (binary (Count n r d)).injective (funext fun i => congrFun he (.inr (.inr (z, i))))

variable (b : ℕ)
  (hb : Nat.clog 2 n + r ^ 3 * Fintype.card A.I *
    Nat.clog 2 (Fintype.card (Packet n r d) + 1) + 1 ≤ b)

def reportPort : A.Cell r d ↪ Fin b := by
  let e := Fintype.equivFin A.I
  letI : LinearOrder A.I := LinearOrder.lift' e e.injective
  let Z := Lex (Lex (Fin r × Lex (Fin r × Fin r)) × A.I)
  letI : LinearOrder (A.Cell r d) := inferInstanceAs
    (LinearOrder (Lex (Unit ⊕ Lex (Fin (Nat.clog 2 n) ⊕ Lex (Z × Fin (Nat.clog 2 (Count n r d)))))))
  have hc : Fintype.card (A.Cell r d) ≤ b := by
    have hr : Fintype.card (Class r) = r ^ 3 := by simp [Class]; ring
    rw [Fintype.card_sum, Fintype.card_sum, Fintype.card_prod, Fintype.card_prod, hr]
    simp only [Fintype.card_unit, Fintype.card_fin]
    omega
  exact (Fintype.orderIsoFinOfCardEq (A.Cell r d) rfl).toEquiv.symm.toEmbedding.trans (Fin.castLEEmb hc)

/-- Reports and the extra branch have disjoint broadcast strings. -/
def encodeReport : Option (A.Accepted (r := r) (d := d) hn (A.budget hn N)) ↪ (Fin b → Bool) := by
  let idx := A.reportPort r d b hb
  refine ⟨fun R => Function.extend idx (A.fields hn N r d R) (fun _ => false), ?_⟩
  intro R R' he
  apply A.fields_injective hn N r d
  funext i
  exact ((idx.injective.extend_apply _ _ i).symm.trans (congrFun he (idx i))).trans
    (idx.injective.extend_apply _ _ i)

private theorem encodeReport_at (R) (i : A.Cell r d) :
    A.encodeReport hn N r d b hb R (A.reportPort r d b hb i) = A.fields hn N r d R i :=
  (A.reportPort r d b hb).injective.extend_apply (A.fields hn N r d R) (fun _ => false) i

theorem encodeReport_pad (R) (i : Fin b) (hi : i ∉ Set.range (A.reportPort r d b hb)) :
    A.encodeReport hn N r d b hb R i = false :=
  Function.extend_apply' (A.fields hn N r d R) (fun _ => false) i hi

@[simp] theorem encodeReport_none (i : Fin b) : A.encodeReport hn N r d b hb none i = false := by
  by_cases hi : i ∈ Set.range (A.reportPort r d b hb)
  · obtain ⟨j, rfl⟩ := hi
    exact A.encodeReport_at hn N r d b hb none j
  · exact A.encodeReport_pad hn N r d b hb none i hi

variable (R : A.Accepted (r := r) (d := d) hn (A.budget hn N))

@[simp] theorem encodeReport_flag :
    A.encodeReport hn N r d b hb (some R) (A.reportPort r d b hb (.inl ())) = true :=
  A.encodeReport_at hn N r d b hb (some R) (.inl ())

@[simp] theorem encodeReport_cut (i : Fin (Nat.clog 2 n)) :
    A.encodeReport hn N r d b hb (some R) (A.reportPort r d b hb (.inr (.inl i))) =
      R.val.1.val.testBit i.val :=
  A.encodeReport_at hn N r d b hb (some R) (.inr (.inl i))

@[simp] theorem encodeReport_count (j : A.CountBit r d) :
    A.encodeReport hn N r d b hb (some R) (A.reportPort r d b hb (.inr (.inr j))) =
      A.countBits R.val j :=
  A.encodeReport_at hn N r d b hb (some R) (.inr (.inr j))

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Expansion

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Scheme

variable {F : Type} [Field F] {N l b n h d B r : ℕ}
  {A : Expansion F n h} {hn : 2 ≤ n} {G : MachineDiagram F N l b d}
  (S : Scheme A hn G r B)

/-- Specialize the public encoding to the batch dimensions of this scheme. -/
abbrev encodeReport
    (hb : Nat.clog 2 n + r ^ 3 * Fintype.card A.I *
      Nat.clog 2 (Fintype.card (Packet n r (B * S.layout.d)) + 1) + 1 ≤ b) :
    Option S.Report ↪ (Fin b → Bool) :=
  A.encodeReport hn N r (B * S.layout.d) b hb

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Scheme
end

section
/-! # Choosing a communication scheme with prescribed exterior labels -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

open Machine
variable {F : Type} [Field F] {N l b n h d B r C D : ℕ}

/-- The colors can be chosen by `exterior` before the diagram is known.
The two density bounds concern a single copy of the diagram. -/
theorem prepare (A : Expansion F n h) (hn : 2 ≤ n) (hh : 0 < h) (hr : 0 < r) (hC : 4 ≤ C)
    (hA : ∀ d', Fintype.card (Position n r d' h) ≤ 52 * C * r * N →
      ∀ (s : Packet n r d' → A.I) (u : Worker r), 128 * ∑ p, (A.plan hn N s).slotsAt h u p ≤ N)
    (fa : Ports N l b → Label n r) (hfa : ∀ g, multiplicity fa g * r ^ n ≤ 4 * N)
    (hlit : ∀ i g, multiplicity (fun t : Fin l => fa (.inl t) i) g * r ≤ 2 * l)
    (hl : 1024 * l ≤ N) (hlink : 64 * (3 * r) ^ 2 ≤ N) (hB : B * d ≤ 4 * r)
    (G : MachineDiagram F N l b d) (hc : G.cost ≤ C * N * d) (hd : ∀ v, G.arity v ≤ D)
    (hsize : (D + 1) * (r ^ n) ^ 4 ≤ C * N * d) (hpad : (r ^ n) ^ 2 * 2 ^ n * h ≤ C * N * d) :
    ∃ S : Scheme A hn G r B, S.colors = fa ∧
      S.layout.d = rounds n r h (12 * (C * N * d)) ∧
      Fintype.card (Position n r S.layout.d h) ≤ 13 * C * N * d ∧
      ∀ z, multiplicity S.layout.color z * r ^ n ≤ 16 * C * N * d := by
  let f := fun s => fa (address N l b (port (tape N l b) d s).2)
  let g : slots (copies .unit d) → Label n r := fun s => (port .unit d s).2.elim
  have hf (z) : multiplicity f z * r ^ n ≤ C * N * d :=
    (exterior_copies fa hfa d z).trans (by gcongr)
  have hg (z) : multiplicity g z * r ^ n ≤ C * N * d := by
    have : IsEmpty (slots (copies .unit d)) := ⟨fun s => (port .unit d s).2.elim⟩
    simp [multiplicity]
  obtain ⟨L, heq, hpos, hf', _, hv⟩ := layout G f g hc hd hr hh hf hg hsize hpad
  have hall : Fintype.card (Position n r (B * L.d) h) ≤ 52 * C * r * N := by
    calc
      _ = B * Fintype.card (Position n r L.d h) := by
        simp only [Position, Packet, Fintype.card_prod, Fintype.card_fin]
        ring
      _ ≤ B * (13 * (C * N * d)) := Nat.mul_le_mul_left B hpos
      _ = 13 * C * N * (B * d) := by ring
      _ ≤ 13 * C * N * (4 * r) := Nat.mul_le_mul_left _ hB
      _ = _ := by ring
  let S : Scheme A hn G r B :=
    ⟨hlink, L, fa, hf', fun s => A.report_budget hn N s (hA _ hall s),
      fun R u => Pin.budget A hn R fa hlit hl u⟩
  exact ⟨S, rfl, heq, by simpa only [S, mul_assoc] using hpos,
    fun z => by simpa only [S, mul_assoc] using hv z⟩

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

/-! # Diagonalization over a fixed coefficient field -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagonal.Scheme

open Classical Machine
variable {F : Type} [Field F] {N l b n h d B r : ℕ} {A : Expansion F n h}
  {hn : 2 ≤ n} {G : MachineDiagram F N l b d} (S : Scheme A hn G r B)
  (pad : Val (tape N l b)) (U : Val (tape N l b) → Val .unit → F)

/-- Each processor has a literal programming the unit branch and
the explicit local evaluation of the replacement graph. -/
def Programs (code : Option S.Report ↪ (Fin b → Bool)) : Prop :=
  ∃ serial : (R : S.Report) → S.Serial R, ∀ i : Fin (3 * r), ∃ ξ : Fin l → Bool,
    ∀ z y, U (feed ξ z y) () = branch code (fun R => S.simulate pad R (serial R) i ξ) z y

/-- No graph implementing a batch of these processors can have all
its replacement computations programmed back into the processors. -/
theorem diagonal (code : Option S.Report ↪ (Fin b → Bool))
    (hr : 0 < r) (hR : 3 * r ≤ B * d) (hx : U pad () = 1)
    (hU : S.Programs pad U code) : G.eval ≠ power U d := by
  intro hG
  obtain ⟨serial, hprog⟩ := hU
  choose ξ hξ using hprog
  have h := S.replay pad ξ U serial hR hx hG
  unfold scalar at h
  simp_rw [hξ] at h
  rw [branch_sum (by omega : 0 < 3 * r) code
    (fun i R => S.simulate pad R (serial R) i (ξ i))] at h
  exact one_ne_zero (add_eq_right.mp h)

end OAI.LinearAlgebra.MatrixExponent.Diagonal.Scheme
end

section
/-!
# Descent and tagged-permutation hardness

At each step the wide version of descent gives a lower bound on the
current per-copy cost. This absorbs the exterior cost of the trivalent
version. A fixed number of iterations then contradicts the lower bound.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal
open Filter

variable {F : Type} [Field F] {L : Set (Table F)}

theorem join {x y : Wire} {U : Val x → Val y → F} {t d m D : ℕ}
    (h : Wide F D L (copies (copies x t) d) (copies (copies y t) d) (power (power U t) d) m) :
    Wide F D L (copies x (t * d)) (copies y (t * d)) (power U (t * d)) m := by
  obtain ⟨f, hf, ef⟩ := (Rewire.joinCopies x t d).inverse
  obtain ⟨g, hg, eg⟩ := (Rewire.joinCopies y t d).inverse
  have he : (fun a b => power (power U t) d (f a) (g b)) = power U (t * d) := by
    funext a b
    rw [← power_join, (ef _ a).mpr rfl, (eg _ b).mpr rfl]
  exact he ▸ (h.pre hf).post hg

private theorem large {α : ℝ} (hα : 0 < α) (k : ℕ) :
    ∀ᶠ w : ℕ in atTop, 2 ≤ w ∧ 3 ≤ (w : ℝ) ^ (α / 4) ∧
      (w : ℝ) ^ ((k : ℝ) + 1) ≤ ((2 ^ w : ℕ) : ℝ) ^ (1 / 40 : ℝ) := by
  have ht : Tendsto (fun w : ℕ => (w : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have he := isLittleO_rpow_exp_pos_mul_atTop ((k : ℝ) + 1) (by positivity : 0 < Real.log 2 / 40)
  filter_upwards [eventually_ge_atTop 2, ((tendsto_rpow_atTop (by positivity : 0 < α / 4)).comp ht).eventually_ge_atTop 3,
    ht.eventually he.eventuallyLE] with w hw hb he'
  refine ⟨hw, hb, ?_⟩
  calc
    _ ≤ Real.exp (Real.log 2 / 40 * w) := by
      simpa only [Real.norm_of_nonneg (by positivity : 0 ≤ (w : ℝ) ^ ((k : ℝ) + 1)),
        Real.norm_of_nonneg (Real.exp_nonneg _)] using he'
    _ = _ := by
      rw [Nat.cast_pow, Nat.cast_ofNat, Real.rpow_def_of_pos (by positivity), Real.log_pow]
      congr 1
      ring

private theorem absorb {w α x y : ℝ} (hw : 0 < w) (hx : 0 ≤ x)
    (hlarge : 3 ≤ w ^ (α / 4)) (hy : y ≤ x * w ^ (-α)) :
    x * w ^ (-α) + y * w ^ (α / 4) + y ≤ x * w ^ (-(α / 2)) := by
  calc
    _ ≤ x * w ^ (-α) + (x * w ^ (-α)) * w ^ (α / 4) + x * w ^ (-α) := by gcongr
    _ = x * w ^ (-α) * (2 + w ^ (α / 4)) := by ring
    _ ≤ x * w ^ (-α) * (w ^ (α / 4) * w ^ (α / 4)) := by gcongr; nlinarith
    _ = _ := by
      rw [mul_assoc, ← Real.rpow_add hw, ← Real.rpow_add hw]
      congr 2
      ring

theorem hard_of_resists (hr : Resists F L) (hd : Descent F L) : Tagged.Hard F := by
  by_contra bad
  obtain ⟨C, hC, α, hα, step⟩ := hd bad
  obtain ⟨k, δ, hδ, resist⟩ := hr (2 * C) (by omega)
  let b := α / 2
  have hb : 0 < b := half_pos hα
  obtain ⟨J, hJ⟩ := exists_nat_gt (((k : ℝ) + 1) / b)
  have hstop : (k : ℝ) + 1 < J * b := (div_lt_iff₀ hb).mp hJ
  have hJpos : 0 < (J : ℝ) := lt_trans (by positivity) hJ
  let κ := min δ (1 / 40 : ℝ) / J
  have hκ : 0 < κ := by unfold κ; positivity
  obtain ⟨w, hstep, ⟨hw, hlarge, hexp⟩, a, U, v, ha, hv, hcost, hard⟩ :=
    ((step κ hκ).and_eventually ((large hα k).and resist)).exists
  let N : ℕ := 2 ^ w
  have hw₁ : 1 < (w : ℝ) := by exact_mod_cast (by omega : 1 < w)
  have hN : 1 ≤ (N : ℝ) := by exact_mod_cast (one_le_pow₀ (by decide : 1 ≤ 2) : 1 ≤ 2 ^ w)
  have hN₀ : 0 < (N : ℝ) := zero_lt_one.trans_le hN
  have budget {j : ℕ} (hj : j ≤ J) : (j : ℝ) * κ ≤ min δ (1 / 40 : ℝ) := by
    calc
      _ ≤ (J : ℝ) * κ := by gcongr
      _ = _ := by unfold κ; field_simp
  have iterate (j : ℕ) (hj : j ≤ J) :
      ∃ t u : ℕ, 1 ≤ t ∧ (t : ℝ) ≤ (N : ℝ) ^ ((j : ℝ) * κ) ∧
        Net F (copies a t) (copies .unit t) (power U t) u ∧
        (u : ℝ) + t * (N : ℝ) ≤ t * N * (w : ℝ) ^ ((k : ℝ) + 1 - j * b) := by
    induction j with
    | zero =>
      refine ⟨1, v, le_rfl, by simp, by simpa only [one_mul] using hv.power 1, ?_⟩
      have h : v + N ≤ N * w ^ (k + 1) := by
        calc
          _ ≤ N * w ^ k + N * 1 := by rw [mul_one]; exact Nat.add_le_add_right hcost _
          _ ≤ _ := by
            rw [← mul_add, pow_succ]
            gcongr
            nlinarith [Nat.one_le_pow k w (by omega)]
      simp only [Nat.cast_one, Nat.cast_zero, one_mul, zero_mul, sub_zero,
        ← Nat.cast_add_one, Real.rpow_natCast]
      exact_mod_cast h
    | succ j ih =>
      obtain ⟨t, u, ht, ht', hnet, hu⟩ := ih (by omega)
      let M := u + t * N
      let e := wd (copies a t) + wd (copies .unit t)
      have he : e ≤ t * N := by
        simp only [e, wd_copies, wd, Nat.mul_zero, Nat.add_zero]
        exact Nat.mul_le_mul_left t ha
      have hM : (M : ℝ) ≤ t * N * (w : ℝ) ^ ((k : ℝ) + 1 - j * b) := by simpa only [M, Nat.cast_add, Nat.cast_mul]
      have ht₀ := ht'.trans (Real.rpow_le_rpow_of_exponent_le hN
        ((budget (j := j) (by omega)).trans (min_le_right _ _)))
      have hsize : (M : ℝ) ≤ (N : ℝ) ^ (21 / 20 : ℝ) := by
        calc
          _ ≤ _ := hM
          _ ≤ (N : ℝ) ^ (1 / 40 : ℝ) * N * (N : ℝ) ^ (1 / 40 : ℝ) := by
            gcongr
            exact (Real.rpow_le_rpow_of_exponent_le hw₁.le (sub_le_self _ (by positivity))).trans hexp
          _ = _ := by
            rw [show (21 / 20 : ℝ) = 1 / 40 + 1 + 1 / 40 by norm_num,
              Real.rpow_add hN₀, Real.rpow_add hN₀, Real.rpow_one]
      have copies_le {d : ℕ} (hd : (d : ℝ) ≤ (N : ℝ) ^ κ) :
          ((t * d : ℕ) : ℝ) ≤ (N : ℝ) ^ ((j.succ : ℝ) * κ) := by
        rw [Nat.cast_mul, Nat.cast_succ, add_mul, one_mul, Real.rpow_add hN₀]
        exact mul_le_mul ht' hd (by positivity) (by positivity)
      obtain ⟨htri, hwide⟩ := hstep _ _ _ _ M hnet (by omega)
        ((Nat.le_mul_of_pos_left N ht).trans (Nat.le_add_left _ _)) hsize
      have he' : (e : ℝ) ≤ t * (N : ℝ) := by exact_mod_cast he
      have hl : (t : ℝ) * N ≤ M * (w : ℝ) ^ (-α) := by
        obtain ⟨d, D, m, hd, hdk, hD, hwide, hm⟩ := hwide
        have hc := (copies_le hdk).trans
          (Real.rpow_le_rpow_of_exponent_le hN ((budget hj).trans (min_le_left _ _)))
        have hlow := hard (t * d) D m (Nat.mul_pos ht hd) hc hD (join hwide)
        have hlo : 2 * (C : ℝ) * N * (t * (d : ℝ)) < m := by exact_mod_cast hlow
        have hc' : 0 < (C : ℝ) * d := by positivity
        have h : 2 * ((t : ℝ) * N) < M * (w : ℝ) ^ (-α) + (e : ℝ) :=
          (mul_lt_mul_iff_right₀ hc').mp (by
            calc
              _ = 2 * (C : ℝ) * N * (t * (d : ℝ)) := by ring
              _ < _ := hlo.trans_le hm)
        linarith
      obtain ⟨d, m, hd, hdk, ⟨u', hnet', hm'⟩, hm⟩ := htri
      have hvm : (u' : ℝ) ≤ m := by exact_mod_cast (show u' ≤ m by omega)
      refine ⟨t * d, u', Nat.mul_pos ht hd, copies_le hdk,
        hnet'.rewire (.joinCopies a t d) (.joinCopies .unit t d) (power_join U t d), ?_⟩
      calc
        _ ≤ (d : ℝ) * (M * (w : ℝ) ^ (-α) + (e : ℝ) * (w : ℝ) ^ (α / 4)) + (t * d : ℕ) * (N : ℝ) :=
          add_le_add_left (hvm.trans hm) _
        _ ≤ (d : ℝ) * (M * (w : ℝ) ^ (-α) + ((t : ℝ) * N) * (w : ℝ) ^ (α / 4) + (t : ℝ) * N) := by
          rw [Nat.cast_mul, mul_add (d : ℝ) _ ((t : ℝ) * N), mul_comm (t : ℝ) (d : ℝ), mul_assoc]
          gcongr
        _ ≤ (d : ℝ) * (M * (w : ℝ) ^ (-b)) := mul_le_mul_of_nonneg_left
          (absorb (by linarith) (by positivity) hlarge hl) (by positivity)
        _ ≤ (d : ℝ) * ((t * N * (w : ℝ) ^ ((k : ℝ) + 1 - j * b)) * (w : ℝ) ^ (-b)) := by gcongr
        _ = _ := by
          rw [Nat.cast_mul, Nat.cast_succ, show (k : ℝ) + 1 - (j + 1) * b =
            ((k : ℝ) + 1 - j * b) + -b by ring, Real.rpow_add (by linarith : 0 < (w : ℝ))]
          ring
  obtain ⟨t, u, ht, _, _, hu⟩ := iterate J le_rfl
  have hlt : (w : ℝ) ^ ((k : ℝ) + 1 - J * b) < 1 := Real.rpow_lt_one_of_one_lt_of_neg hw₁ (by linarith)
  have := mul_lt_mul_of_pos_left hlt (by positivity : 0 < (t : ℝ) * N)
  linarith

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

section
/-!
# A common batch size independent of the replacement

Repeat any proposed small network until it reaches the prescribed
power. Feed surplus copies an input of weight one. This allows all
processor array dimensions to be fixed before choosing a diagram.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

variable {F : Type} [Field F] {D : ℕ} {L : Set (Table F)} {a b : Wire} {m d : ℕ}

private theorem repeat_wide {k : Val a → Val b → F} (h : Wide F D L a b k m) (e : ℕ) :
    Wide F D L (copies a e) (copies b e) (power k e) (e * m) := by
  induction e with
  | zero => rw [Nat.zero_mul]; exact .empty
  | succ e ih => rw [Nat.succ_mul, Nat.add_comm (e * m) m]; exact h.par ih

variable {U : Val a → Val .unit → F} (pad : Val a) (hp : U pad () = 1)

include hp in
private theorem trim (hD : 3 ≤ D) {s : ℕ} (hs : s ≤ d)
    (h : Wide F D L (copies a d) (copies .unit d) (power U d) m) :
    ∃ v ≤ m + 4 * d * wd a, Wide F D L (copies a s) (copies .unit s) (power U s) v := by
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hs
  let z := bundle a j (fun _ => pad)
  have hz : power U j z (unitCopies j) = 1 := by
    rw [← eq_unitCopies j (bundle .unit j (fun _ => ()))]
    unfold z
    rw [power_bundle]
    simp only [hp, Finset.prod_const_one]
  have p := ((Tagged.literal_net F _ z).par (DNet.id F (copies a s))).pre
    ((Rewire.unit' _).comp (.swap _ _))
  obtain ⟨n, hn, g⟩ := p.post (.appendCopies a j s)
  obtain ⟨v, hv, hg⟩ := g.includeWide (L := L) hD
  have out := (Rewire.copiesUnit s).comp (Rewire.unitCopies (s + j))
  refine ⟨v + m, ?_, ?_⟩
  · simp only [wd_copies] at hn
    ring_nf at hn ⊢
    omega
  · convert hg.comp (h.post out) using 1
    funext y r
    simp only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
    rw [← eq_unitCopies _ (appendCopies .unit j s (unitCopies j, r)), power_append, hz, one_mul]

include hp in
theorem repeat_trim {N C e : ℕ} (hd : 1 ≤ d) (he : d ≤ 2 * e) (ha : wd a ≤ N)
    (h : Wide F D L (copies a d) (copies .unit d) (power U d) m) (hm : m ≤ C * N * d) :
    ∃ v ≤ (3 * C + 12) * N * e, Wide F (max D 3) L (copies a e) (copies .unit e) (power U e) v := by
  let k := e / d + 1
  have hcover : e ≤ d * k ∧ d * k ≤ 3 * e := by
    have := Nat.mod_lt e hd
    have := Nat.mod_add_div e d
    simp only [k, mul_add, mul_one]
    omega
  have hh := join (repeat_wide (h.mono (le_max_left D 3) (Set.Subset.refl _)) k)
  obtain ⟨v, hv, hnet⟩ := trim pad hp (le_max_right _ _) hcover.1 hh
  refine ⟨v, hv.trans ?_, hnet⟩
  calc
    _ ≤ k * (C * N * d) + 4 * (d * k) * N := by gcongr
    _ = (C + 4) * N * (d * k) := by ring
    _ ≤ (C + 4) * N * (3 * e) := Nat.mul_le_mul_left _ hcover.2
    _ = _ := by ring

/-- A power of two within a factor of two of the square root
of the number of homes. -/
theorem batch_floor (w n : ℕ) :
    let m := 2 ^ (w / (32 * n))
    let r := 2 ^ (w / (16 * n))
    0 < m ∧ m ^ 2 ≤ r ∧ ∀ d : ℕ, d ^ 2 ≤ r → d ≤ 2 * m := by
  have h : w / (32 * n) = w / (16 * n) / 2 := by
    rw [Nat.div_div_eq_div_mul, show 16 * n * 2 = 32 * n by ring]
  rw [h]
  generalize w / (16 * n) = j
  intro m r
  refine ⟨by unfold m; positivity, ?_, ?_⟩
  · unfold m r
    rw [← pow_mul]
    exact Nat.pow_le_pow_right (by decide) (by omega)
  · have hr : r ≤ 2 * m ^ 2 := by
      unfold m r
      rw [← pow_mul, ← pow_succ']
      exact Nat.pow_le_pow_right (by decide) (by omega)
    intro d hd
    nlinarith

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

section
/-!
# The local processor implementation requirement

The implementation must be chosen before any replacement diagram is
given. Only the literal settings, wire numbering and report code can
depend on the diagram. This requirement is a hypothesis.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal
open Filter Machine

variable {F : Type} [Field F] {n h r d N l B : ℕ} {A : Expansion F n h}
  {hn : 2 ≤ n} {G : MachineDiagram F N l l d}

def Scheme.compact (S : Scheme A hn G r B) (C : ℕ) :=
  Fintype.card (Position n r S.layout.d h) ≤ 13 * C * N * d ∧
    ∀ z, multiplicity S.layout.color z * r ^ n ≤ 16 * C * N * d

def Scheme.fits (S : Scheme A hn G r B) :=
  Nat.clog 2 n + r ^ 3 * Fintype.card A.I * Nat.clog 2 (Fintype.card (Packet n r (B * S.layout.d)) + 1)
    + 1 ≤ l

theorem Scheme.fits_of_compact (S : Scheme A hn G r B) {C D : ℕ} (hh : 0 < h)
    (scale : Scales C n h (Fintype.card A.I) N r l l d D B) (hc : S.compact C) :
    S.fits := by
  have hp : Fintype.card (Packet n r (B * S.layout.d)) ≤ 52 * C * N * r := by
    calc
      _ = B * Fintype.card (Packet n r S.layout.d) := by
        simp only [Packet, Fintype.card_prod, Fintype.card_fin]; ring
      _ ≤ B * Fintype.card (Position n r S.layout.d h) := by
        gcongr
        rw [Fintype.card_prod (Packet n r S.layout.d)]
        have : Nonempty (Fin h) := ⟨⟨0, hh⟩⟩
        exact Nat.le_mul_of_pos_right _ Fintype.card_pos
      _ ≤ B * (13 * C * N * d) := Nat.mul_le_mul_left _ hc.1
      _ = 13 * C * N * (B * d) := by ring
      _ ≤ 13 * C * N * (4 * r) := Nat.mul_le_mul_left _ scale.copies
      _ = _ := by ring
  refine le_trans ?_ scale.broadcast
  gcongr

/-- Every admissible diagram of the indicated size must have a local
program at each site, without any promise about the tensor it computes. -/
def Implements (L : Set (Table F)) (C k w : ℕ) (A : Expansion F n h) (hn : 2 ≤ n) : Prop :=
  let N := 2 ^ w
  let r := 2 ^ (w / (16 * n))
  let l := N / 2048
  ∀ fa : Ports N l l → Label n r,
    (∀ z, multiplicity fa z * r ^ n ≤ 4 * N) →
    (∀ i g, multiplicity (fun t : Fin l => fa (.inl t) i) g * r ≤ 2 * l) →
    ∃ (U : Val (tape N l l) → Val .unit → F) (pad : Val (tape N l l)) (v : ℕ),
      U pad () = 1 ∧ Net F (tape N l l) .unit U v ∧ v ≤ N * w ^ k ∧
      let d := 2 ^ (w / (32 * n))
      ∀ D : ℕ, D ^ 2 ≤ N →
        ∀ G : MachineDiagram F N l l d, G.cost ≤ C * N * d → G.Admits D L →
          ∀ S : Scheme A hn G r ((3 * r + d - 1) / d), S.colors = fa →
            S.layout.d = rounds n r h (12 * (C * N * d)) → S.compact C →
            ∀ hb : S.fits, S.Programs pad U (S.encodeReport hb)

/-- A quasi-linear universal processor for the concrete local evaluations. -/
def Programmable (F : Type) [Field F] (L : Set (Table F)) : Prop :=
  ∀ C : ℕ, 4 ≤ C → ∀ (n h : ℕ) (hn : 2 ≤ n), 0 < h → ∀ A : Expansion F n h,
    ∃ k : ℕ, ∀ᶠ w : ℕ in atTop, Implements L C k w A hn

theorem resists_of_programmable {L : Set (Table F)} (hU : Programmable F L) : Resists F L := by
  intro C₀ hC₀
  let C := 3 * C₀ + 12
  have hC : 4 ≤ C := by omega
  obtain ⟨n, hn, h, A, hh, ha⟩ := bounded_expansion F (52 * C)
  obtain ⟨k, hk⟩ := hU C hC n h hn hh A
  obtain ⟨δ, hδ, hscale⟩ := scales C n h (Fintype.card A.I) hC hn
  refine ⟨k, δ, hδ, ?_⟩
  filter_upwards [hk, hscale] with w impl scale
  let N := 2 ^ w
  let r := 2 ^ (w / (16 * n))
  let l := N / 2048
  have hN : 0 < N := by unfold N; positivity
  have hr : 0 < r := by unfold r; positivity
  obtain ⟨hδd, hs⟩ := scale
  have s := hs 1 0 (by decide) (by exact hr) (by exact hN.le)
  obtain ⟨fa, hfa, hfl⟩ := exterior s.pos s.labels s.tape
  obtain ⟨U, pad, v, hpad, hnet, hv, hp⟩ := impl fa hfa hfl
  have hwd : wd (tape N l l) ≤ N := by rw [wd_word]; exact s.tape
  refine ⟨tape N l l, U, v, hwd, hnet, hv, ?_⟩
  intro d D m hd hsmall hD hwide
  by_contra! hm
  let d₀ := 2 ^ (w / (32 * n))
  obtain ⟨hd₀, hsmall₀, hcmp⟩ := batch_floor w n
  have hmax : (max D 3) ^ 2 ≤ N := by
    rcases le_total 3 D with h | h
    · rw [max_eq_left h]; exact hD
    · rw [max_eq_right h]
      have hli : 64 * (3 * r) ^ 2 ≤ N := s.links
      have : 0 < (3 * r) ^ 2 := by positivity
      omega
  obtain ⟨v', hm', hfixed⟩ := repeat_trim pad hpad hd (hcmp d (hδd d hsmall)) hwd hwide hm
  obtain ⟨G, hG, had, hcost⟩ := hfixed.diagram
  have sc := hs d₀ (max D 3) hd₀ hsmall₀ hmax
  obtain ⟨S, hcolors, hshape, hcomp⟩ := prepare A hn hh hr hC (fun d' => ha r d' N hN)
    fa hfa hfl sc.literal sc.links sc.copies G (hcost.le.trans hm') (fun v => (had v).1)
    sc.degree sc.padding
  have hb := S.fits_of_compact hh sc hcomp
  have prog := hp (max D 3) hmax G (hcost.le.trans hm') had S hcolors hshape hcomp hb
  exact S.diagonal pad U (S.encodeReport hb) hr sc.cover hpad prog hG

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end

section
/-! # The remaining estimates for exact many-list hardness -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagonal

theorem manyList {F : Type} [Field F] {L : Set (Table F)}
    (hU : Programmable F L) (hD : Descent F L) : ManyList (Realizes F) :=
  Tagged.manyList_of_tag (hard_of_resists (resists_of_programmable hU) hD)

end OAI.LinearAlgebra.MatrixExponent.Diagonal
end
