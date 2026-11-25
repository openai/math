import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import OAI.LinearAlgebra.MatrixExponent.Coloring.Shift
import OAI.LinearAlgebra.MatrixExponent.Control.BucketNet
import OAI.LinearAlgebra.MatrixExponent.Coloring.Add
import OAI.LinearAlgebra.MatrixExponent.Coloring.Matching
import OAI.LinearAlgebra.MatrixExponent.Coloring.Edges
import OAI.LinearAlgebra.MatrixExponent.Coloring.Chart
import OAI.LinearAlgebra.MatrixExponent.Routing.Parameters

section
/-! # Comparing the sizes of two colour classes -/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

private def count (h : ℕ) (x : B h → Bool) : B (h + 1) :=
  ⟨Control.histogram x true none, (Control.histogram_le ..).trans_lt
    (Nat.pow_lt_pow_right (by decide) (by omega))⟩

variable (F : Type) [Field F]

private theorem cheap_count (h : ℕ) : Cheap F h h (.vec h .bit) (.addr (h + 1)) (count h) 3 := by
  obtain ⟨L, hL⟩ := Layout.exists_tree .bit h
  have hc := (Control.prefix_net F h).comp (DNet.snd F _ _)
  have hr : Circuit F (.vec h .bit) (.addr (h + 1)) (count h)
      (500 * 2 ^ h * (h + 1) + wd (.pair (tree h (word (h + 1))) (word (h + 1)))) := by
    apply Circuit.of_dnet L.positions (.refl _) hc
    intro x
    change bits (word (h + 1)) (Control.bitPrefix h x).2 =
      bits (word (h + 1)) (Lookup.bits (h + 1) (Control.histogram (L.read x) true none))
    rw [(Control.prefix_eq h x _ (hL _)).2]
  refine ⟨_, hr, ?_⟩
  rw [Format.width_vec, Format.width_bit, Format.width_addr]
  simp only [wd, wd_word, wd_tree]
  have hh := Nat.mul_le_mul_right (h + 1) (Nat.one_le_pow h 2 (by decide))
  ring_nf at hh ⊢
  omega

private abbrev masks (h : ℕ) := Format.pair (.pair (.vec h .bit) (.vec h .bit)) (.vec h .bit)
abbrev Triple := Format.pair (.pair .bit .bit) .bit

private def marked (b : Bool) (x : Triple.obj) : Bool :=
  decide (x.1.1 = true ∧ x.1.2 = true ∧ x.2 = b)

theorem cheap_triple (h : ℕ) (f : Triple.obj → Bool) : Cheap F 0 h Triple .bit f 2 := by
  refine ⟨_, small (F := F) (A := Triple) (by simp [Triple]) _, ?_⟩
  simp only [Format.width_pair]
  rw [Format.width_bit]
  ring_nf
  omega

private theorem cheap_cmp (h : ℕ) :
    Cheap F h h (.pair (.addr (h + 1)) (.addr (h + 1))) .bit
      (fun x => !(decide (x.1 < x.2))) 3 := by
  refine ⟨_, (numeric_lt F (h + 1)).comp (small (F := F) (A := .bit) (by simp) Bool.not), ?_⟩
  rw [Format.width_pair, Format.width_addr, Format.width_bit]
  apply le_trans _ (Nat.le_mul_of_pos_left _ (Nat.two_pow_pos h))
  ring_nf; omega

theorem cheap_minority (h : ℕ) :
    Cheap F h h (.pair (.pair (.vec h .bit) (.vec h .bit)) (.vec h .bit)) .bit
      (fun x => minority x.1.1 x.1.2 x.2) 30 := by
  have hw : (masks h).width ≤ 2 ^ h * (100 + h) ^ 1 := by
    simp only [Format.width_pair, Format.width_vec]
    rw [Format.width_bit, ← mul_add, ← mul_add, pow_one]
    apply Nat.mul_le_mul_left; omega
  have base := Cheap.id F hw
  have get := (base.fst.zip.pair base.snd).zip
  have hc (b : Bool) := (get.comp (Cheap.map _ (fun _ : B h => cheap_triple F h (marked b)))).comp
    (cheap_count F h)
  convert (((hc false).pair (hc true)).comp (cheap_cmp F h)).mono (d := 30) (by decide) using 1
  funext x
  apply Bool.eq_iff_iff.mpr
  simp [minority, count, Control.histogram_none, marked, Function.comp_def]

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

section
/-!
# Halving multiplicities with bounded counters

The counters never overflow. A unit is added only at an odd edge of
the chosen colour, after dividing the previous count by two.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

abbrev Weighted (h k r : ℕ) := Format.pair (GraphInput h k) (.vec h (.addr r))

private def reduce {r : ℕ} (v : B r) (b : Bool) : B r :=
  if b then half v + 1 else half v

private theorem reduce_val {r : ℕ} (v : B r) (b : Bool) (hb : b = true → odd v = true) :
    (reduce v b).val = v.val / 2 + if b then 1 else 0 := by
  cases b
  · rfl
  · have hv : v.val % 2 = 1 := of_decide_eq_true (hb rfl)
    have := v.isLt
    change (v.val / 2 + 1 % 2 ^ r) % 2 ^ r = v.val / 2 + 1
    rw [Nat.add_mod_mod, Nat.mod_eq_of_lt (by omega)]

variable {h k r : ℕ}

def halveStep (x : (Weighted h k r).obj) : (Weighted h k r).obj :=
  let a := fun i => odd (x.2 i)
  let c := split x.1.1.1 x.1.1.2 a
  (x.1, fun i => reduce (x.2 i) (a i && (c i == minority x.1.2 a c)))

private theorem halve_val (x : (Weighted h k r).obj) :
    Fin.val ∘ (halveStep x).2 = halve x.1.1.1 x.1.1.2 x.1.2 (Fin.val ∘ x.2) := by
  funext i
  exact reduce_val _ _ (fun h => (Bool.and_eq_true_iff.mp h).1)

theorem halve_steps (x : (Weighted h k r).obj) (d : ℕ) :
    (halveStep^[d] x).1 = x.1 ∧
    Fin.val ∘ (halveStep^[d] x).2 = (halve x.1.1.1 x.1.1.2 x.1.2)^[d] (Fin.val ∘ x.2) := by
  induction d with
  | zero => exact ⟨rfl, rfl⟩
  | succ d ih =>
    rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
    refine ⟨ih.1, ?_⟩
    rw [halve_val, ih.1, ih.2]

variable (F : Type) [Field F]

private theorem unary {r : ℕ} {A : Format} {f : B r → A.obj}
    (hw : A.width ≤ 1 + r) (hc : Circuit F (.addr r) A f (1000 * (1 + r))) :
    Cheap F 0 r (.addr r) A f 3 := by
  refine ⟨_, hc, ?_⟩
  rw [Format.width_addr]
  ring_nf
  omega

private theorem cheap_reduce (r : ℕ) :
    Cheap F 0 r (.pair (.addr r) .bit) (.addr r) (fun x => reduce x.1 x.2) 10 := by
  have hw : (Format.pair (.addr r) .bit).width ≤ 2 ^ 0 * (100 + r) ^ 1 := by
    rw [Format.width_pair, Format.width_addr, Format.width_bit]; simp
  have haddr : (Format.addr r).width ≤ 1 + r := by simp
  have base := Cheap.id F hw
  have a := base.fst.comp (unary F haddr (numeric_half F r))
  have b := a.comp (unary F haddr (numeric_inc F r))
  exact (((b.pair a).pair base.snd).comp (cheap_select F r)).mono (by decide)

private theorem broadcast (h t : ℕ) :
    Cheap F h t .bit (.vec h .bit) (fun b _ => b) 1 := by
  apply Cheap.project (c := 0) F _ _ Prod.snd (fun _ _ => rfl)
  · rw [Format.width_bit, pow_zero, mul_one]
    exact Nat.one_le_pow h 2 (by decide)
  · rw [Format.width_vec, Format.width_bit, pow_zero]

theorem cheap_halve (h k r : ℕ) :
    Cheap F h (h + k + r) (Weighted h k r) (Weighted h k r) halveStep 160 := by
  let t := h + k + r
  have hw : (Weighted h k r).width ≤ 2 ^ h * (100 + t) ^ 2 := by
    rw [Format.width_pair, graph_width, Format.width_vec, Format.width_addr, ← mul_add]
    apply Nat.mul_le_mul_left
    dsimp [t]; ring_nf; omega
  have base := Cheap.id F hw
  have m := base.snd
  have bit := unary F (A := .bit) (by rw [Format.width_bit]; omega) (numeric_odd F r)
  have a := m.comp (Cheap.map _ (fun _ : B h => bit.widen (l := t) (by omega)))
  have c := (base.fst.fst.pair a).comp ((cheap_split F h k).widen (l := t) (by omega))
  have hm := cheap_minority F h
  have b := ((base.fst.snd.pair a).pair c).comp (hm.widen (l := t) (by omega))
  have args := ((a.pair c).zip.pair (b.comp (broadcast F h t))).zip
  have mark := cheap_triple F t (fun x => x.1.1 && (x.1.2 == x.2))
  have flag := args.comp (Cheap.map _ (fun _ : B h => mark))
  have next := (m.pair flag).zip.comp
    (Cheap.map _ (fun _ : B h => (cheap_reduce F r).widen (l := t) (by omega)))
  exact (base.fst.pair next).mono (by decide)

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

/-!
# Computing a perfect matching

The degree and support are fixed. Append dummy edges, initialize bounded
counters, halve repeatedly, then retain real edges with final count one.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Coloring

variable (F : Type) [Field F] {h k r : ℕ}

private theorem cheap_join (A : Format) (ha : A.width ≤ r) :
    Cheap F h r (.pair (.vec h A) (.vec h A)) (.vec (h + 1) A)
      (fun x => join x.1 x.2) 3 := by
  have hw : 2 ^ h * (2 * A.width) ≤ 2 ^ h * (100 + r) ^ 2 := by
    apply Nat.mul_le_mul_left; nlinarith
  let p (ij : B (h + 1) × A.pins) :=
    Sum.map (fun i => (i, ij.2)) (fun i => (i, ij.2)) ((halves h).symm ij.1)
  apply Cheap.project (c := 2) F _ _ p
  · intro x ⟨i, j⟩
    obtain ⟨i | i, rfl⟩ := (halves h).surjective i <;>
      simp only [p, Equiv.symm_apply_apply, Sum.map_inl, Sum.map_inr] <;>
      change A.code (join x.1 x.2 _) j = _ <;>
      simp only [join, Function.comp_apply, Equiv.symm_apply_apply] <;> rfl
  · rw [Format.width_pair, Format.width_vec, ← mul_add, ← two_mul]
    exact hw
  · rw [Format.width_vec, pow_succ, mul_assoc]; exact hw

private theorem cheap_from_bit {A : Format} (ha : A.width ≤ r) (f : Bool → A.obj) :
    Cheap F 0 r .bit A f 2 := by
  have t : Install.Depends (A.code ∘ f ∘ Format.bit.code.symm) 1 := by
    intro i
    exact ⟨Finset.univ, by rfl, fun x y he => by rw [funext (fun j => he j (Finset.mem_univ _))]⟩
  refine ⟨_, t.bnet F, ?_⟩
  change 1 + A.width + (1 + 34 * A.width) ≤ _
  nlinarith

private def coeff (h d : ℕ) (rem : Bool) : B (h + 2) :=
  ⟨if rem then 2 ^ (h + 1) % d else 2 ^ (h + 1) / d, by
    have he : 2 ^ (h + 1) < 2 ^ (h + 2) := Nat.pow_lt_pow_right (by decide) (by omega)
    split
    · exact (Nat.mod_le ..).trans_lt he
    · exact (Nat.div_le_self ..).trans_lt he⟩

private abbrev extent (h k : ℕ) := (h + 1) + k + (h + 2)
private abbrev enlarged (h k : ℕ) := Weighted (h + 1) k (h + 2)

private def init (S : Finset (B k)) (d : ℕ) (x : (GraphInput h k).obj) : (enlarged h k).obj :=
  (((join x.1.1 (dummyLabel S), join x.1.2 (dummyLabel S)), dummy h),
    join (fun i => if x.2 i then coeff h d false else 0)
      (fun i => if i.val < S.card then coeff h d true else 0))

private theorem init_val (S : Finset (B k)) (d : ℕ) (x : (GraphInput h k).obj) :
    Fin.val ∘ (init S d x).2 = weights S d x.2 := by
  funext i
  obtain ⟨i | i, rfl⟩ := (halves h).surjective i <;>
    simp only [init, weights, join, Function.comp_apply, Equiv.symm_apply_apply,
      Sum.elim_inl, Sum.elim_inr] <;> split <;> rfl

private theorem cheap_init (h k : ℕ) (S : Finset (B k)) (d : ℕ) :
    Cheap F h (extent h k) (GraphInput h k) (enlarged h k) (init S d) 20 := by
  let r := extent h k
  have ha : (Format.addr k).width ≤ r := by rw [Format.width_addr]; unfold r extent; omega
  have hz : (Format.addr (h + 2)).width ≤ r := by rw [Format.width_addr]; unfold r extent; omega
  have hw : (GraphInput h k).width ≤ 2 ^ h * (100 + r) ^ 2 := by
    rw [graph_width]
    apply Nat.mul_le_mul_left
    dsimp [r, extent]; ring_nf; omega
  have vec (A : Format) (ha : A.width ≤ r) : (Format.vec h A).width ≤ 2 ^ h * (100 + r) ^ 2 := by
    rw [Format.width_vec]; apply Nat.mul_le_mul_left; nlinarith
  have flag : (Format.vec (h + 1) .bit).width ≤ 2 ^ h * (100 + r) ^ 2 := by
    rw [Format.width_vec, Format.width_bit, mul_one, pow_succ]
    apply Nat.mul_le_mul_left; nlinarith
  have base := Cheap.id F hw
  have label := Cheap.const F hw (vec _ ha) (dummyLabel S)
  have add := cheap_join (h := h) F (.addr k) ha
  have left := (base.fst.fst.pair label).comp add
  have right := (base.fst.snd.pair label).comp add
  have graph := (left.pair right).pair (Cheap.const F hw flag (dummy h))
  have pick := cheap_from_bit F hz (fun b => if b then coeff h d false else 0)
  have real := base.snd.comp (Cheap.map _ (fun _ : B h => pick))
  have fill := Cheap.const F hw (vec _ hz) (fun i => if i.val < S.card then coeff h d true else 0)
  have nums := (real.pair fill).comp (cheap_join (h := h) F (.addr (h + 2)) hz)
  exact (graph.pair nums).mono (by decide)

private theorem cheap_one (r : ℕ) :
    Cheap F 0 r (.addr r) .bit (fun i => decide (i.val = 1)) 3 := by
  refine ⟨10 * r + 1, ?_, by rw [Format.width_addr, Format.width_bit]; ring_nf; omega⟩
  apply Circuit.of_dnet (.refl _) (.refl _) (Control.quotient_test F r 0 1)
  intro i
  simp only [Equiv.coe_refl, Function.comp_id, pow_zero, Nat.div_one]
  exact congrArg (fun j : B r => bits .bit (decide (j.val = 1))) (decode_addr r i).symm

private def finish (x : (enlarged h k).obj) (i : B h) : Bool :=
  decide ((x.2 (halves h (.inl i))).val = 1)

private theorem cheap_finish (h k : ℕ) :
    Cheap F h (extent h k) (enlarged h k) (.vec h .bit) finish 5 := by
  let A := Format.vec h (.addr (h + 2))
  have hw : (enlarged h k).width ≤ 2 ^ h * (100 + extent h k) ^ 2 := by
    rw [Format.width_pair, graph_width, Format.width_vec, Format.width_addr,
      ← mul_add, pow_succ, mul_assoc]
    apply Nat.mul_le_mul_left
    dsimp [extent]; ring_nf; omega
  have hv : A.width ≤ 2 ^ h * (100 + extent h k) ^ 2 := by
    rw [Format.width_vec, Format.width_addr]
    apply Nat.mul_le_mul_left
    dsimp [extent]; ring_nf; omega
  have extract := Cheap.project (A := enlarged h k) (D := A) F hw hv (f := fun x i => x.2 (halves h (.inl i)))
    (fun ij => Sum.inr (halves h (.inl ij.1), ij.2)) (fun _ _ => rfl)
  have test := (cheap_one F (h + 2)).widen (l := extent h k) (by unfold extent; omega)
  exact (extract.comp (Cheap.map _ (fun _ : B h => test))).mono (by decide)

private theorem recost {A D : Format} {f : A.obj → D.obj} {c : ℕ}
    (hf : Cheap F (h + 1) r A D f c) : Cheap F h r A D f (c + 1) := by
  obtain ⟨m, hm, hw⟩ := hf
  refine ⟨m, hm, hw.trans ?_⟩
  rw [pow_succ, pow_succ', mul_assoc]
  exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))

private theorem extent_cost {A D : Format} {f : A.obj → D.obj} {c : ℕ}
    (hf : Cheap F h (extent h k) A D f c) : Cheap F h (h + k) A D f (2 * c) := by
  obtain ⟨m, hm, hw⟩ := hf
  refine ⟨m, hm, hw.trans ?_⟩
  rw [pow_mul]
  apply Nat.mul_le_mul_left
  apply Nat.pow_le_pow_left
  dsimp [extent]; ring_nf; omega

theorem cheap_matching (h k : ℕ) (S : Finset (B k)) (d : ℕ) :
    Cheap F h (h + k) (GraphInput h k) (.vec h .bit)
      (fun x => matching S d x.1.1 x.1.2 x.2) 400 := by
  have hc := cheap_halve F (h + 1) k (h + 2)
  have it := recost F (hc.iterate (r := h + 1) (by omega))
  have t := ((cheap_init F h k S d).comp it).comp (cheap_finish F h k)
  convert (extent_cost F t).mono (d := 400) (by decide) using 1
  funext x i
  have hv := (halve_steps (init S d x) (h + 1)).2
  rw [init_val] at hv
  exact congrArg (fun y : B (h + 1) → ℕ => decide (y (halves h (.inl i)) = 1)) hv.symm

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

section
/-!
# Circuits for the full edge colouring

Both halves of a bisection occupy one array. The circuit carries
only the two decision bits per edge around the recursive call. Each
level adds one bounded polynomial overhead to the total cost.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

variable (F : Type) [Field F]

private abbrev Mask (h : ℕ) := Format.vec h .bit
private abbrev Flags (h : ℕ) := Format.pair (Mask h) (Mask h)
private abbrev Local (h : ℕ) := Format.pair (.pair .bit .bit) (.addr h)
private abbrev Final (h : ℕ) := Format.pair (Flags h) (Perm h)

private theorem cheap_combine (h d : ℕ) : Cheap F 0 h (Local h) (.addr h)
    (fun x => combine d x.1.1 x.1.2 x.2) 30 := by
  have hw : (Local h).width ≤ 2 ^ 0 * (100 + h) ^ 1 := by simp [Local]
  have hw' : (Format.addr h).width ≤ 2 ^ 0 * (100 + h) ^ 1 := by simp
  have inp := Cheap.id F hw
  let z : B h := ⟨(d - 1) % 2 ^ h, Nat.mod_lt _ (Nat.two_pow_pos h)⟩
  have fixed := Cheap.const F hw hw' z
  have add : Cheap F 0 h (.pair (.addr h) (.addr h)) (.addr h) (fun x => x.1 + x.2) 3 :=
    ⟨_, numeric_add F h, by simp only [Format.width_pair, Format.width_addr]; ring_nf; omega⟩
  have inc : Cheap F 0 h (.addr h) (.addr h) (fun x => x + 1) 3 :=
    ⟨_, numeric_inc F h, by simp only [Format.width_addr]; ring_nf; omega⟩
  have dbl := (inp.snd.pair inp.snd).comp add
  have c := (((dbl.comp inc).pair dbl).pair inp.fst.snd).comp (cheap_select F h)
  have t := ((fixed.pair c).pair inp.fst.fst).comp (cheap_select F h)
  convert t.mono (d := 30) (by decide) using 1
  funext ⟨⟨p, q⟩, j⟩
  change combine d p q j = if p then z else if q then j + j + 1 else j + j
  cases p <;> cases q <;> apply Fin.ext <;> simp [combine, z, Fin.add_def, two_mul]

private def collect (h d : ℕ) (x : (Final h).obj) (i : B h) : B h :=
  combine d (x.1.1 i) (x.1.2 i) (x.2 i)

private theorem cheap_collect (h d : ℕ) :
    Cheap F h h (Final h) (Perm h) (collect h d) 32 := by
  have hw : (Final h).width ≤ 2 ^ h * (100 + h) ^ 1 := by
    simp only [Format.width_pair, Format.width_vec, Format.width_addr,
      pow_one, ← mul_add]
    rw [Format.width_bit]
    gcongr
    omega
  have inp := Cheap.id F hw
  have args := (inp.fst.zip.pair inp.snd).zip
  exact (args.comp (Cheap.map _ (fun _ : B h => cheap_combine F h d))).mono (by decide)

private theorem cheap_rest : Cheap F 0 0 (.pair .bit .bit) .bit
    (fun x => x.1 && !x.2) 1 := by
  have h := DNet.table F (.pair .bit .bit) .bit (fun x => x.1 && !x.2) (by decide)
  exact ⟨1, Circuit.of_dnet (.refl _) (.refl _) h (by intro x; rfl), by simp⟩

private theorem cheap_double (k : ℕ) : Cheap F 0 k (.pair (.addr k) .bit) (.addr (k + 1))
    (fun x => double x.1 x.2) 3 :=
  ⟨_, numeric_double F k, by
    rw [Format.width_pair, Format.width_addr, Format.width_addr, Format.width_bit]; ring_nf; omega⟩

private noncomputable def prepare (h k : ℕ) (S : Finset (B k)) (d : ℕ)
    (x : (GraphInput h k).obj) : (Flags h).obj × (GraphInput h (k + 1)).obj :=
  let y := retired S d x.1.1 x.1.2 x.2
  let a := rest x.2 y
  let b := split x.1.1 x.1.2 a
  ((y, b), (nextEnd x.1.1 b, nextEnd x.1.2 b), a)

private theorem width_input (h k : ℕ) : (GraphInput h k).width ≤ 2 ^ h * (100 + (h + k)) ^ 2 := by
  rw [graph_width]
  gcongr
  ring_nf
  omega

private theorem cheap_prepare (h k : ℕ) (S : Finset (B k)) (d : ℕ) :
    Cheap F h (h + k) (GraphInput h k) (.pair (Flags h) (GraphInput h (k + 1)))
      (prepare h k S d) 415 := by
  have hw := width_input h k
  have mask : (Mask h).width ≤ 2 ^ h * (100 + (h + k)) ^ 2 := by
    rw [Format.width_vec, Format.width_bit]
    gcongr
    ring_nf
    omega
  have inp := Cheap.id F hw
  have y : Cheap F h (h + k) (GraphInput h k) (Mask h)
      (fun x => retired S d x.1.1 x.1.2 x.2) 400 := by
    by_cases he : d % 2 = 0
    · simp only [retired, he, ite_true]
      exact (Cheap.const F hw mask (fun _ => false)).mono (by decide)
    · simp only [retired, he, ite_false]
      exact cheap_matching F h k S d
  have a := ((inp.snd.pair y).zip).comp
    (Cheap.map _ (fun _ : B h => (cheap_rest F).widen (l := h + k) (by omega)))
  have b := (inp.fst.pair a).comp (cheap_split F h k)
  have ext := Cheap.map _ (fun _ : B h => (cheap_double F k).widen (l := h + k) (by omega))
  have left := ((inp.fst.fst.pair b).zip).comp ext
  have right := ((inp.fst.snd.pair b).zip).comp ext
  exact ((y.pair b).pair ((left.pair right).pair a)).mono (by decide)

private theorem recurse_cost (fuel h k K : ℕ) (hk : h + k + fuel ≤ K) (S : Finset (B k)) (d : ℕ) :
    ∃ m, Circuit F (GraphInput h k) (Perm h) (fun x => recurse fuel S d x.1.1 x.1.2 x.2) m ∧
      (GraphInput h k).width + (Perm h).width + m ≤ (2 * fuel + 1) * (2 ^ h * (100 + K) ^ 415) := by
  induction fuel generalizing k d with
  | zero =>
    have ho : (Perm h).width ≤ 2 ^ h * (100 + (h + k)) ^ 2 := by
      rw [Format.width_vec, Format.width_addr]
      gcongr
      ring_nf
      omega
    have c := Cheap.const F (width_input h k) ho (fun _ => 0)
    obtain ⟨m, hm, le⟩ := (c.widen (l := K) (by omega)).mono (d := 415) (by decide)
    exact ⟨m, hm, by simpa only [mul_zero, zero_add, one_mul] using le⟩
  | succ n ih =>
    obtain ⟨a, ha, la⟩ := (cheap_prepare F h k S d).widen (l := K) (by omega)
    obtain ⟨b, hb, lb⟩ := ih (k + 1) (by omega) (enlarge S) (d / 2)
    obtain ⟨c, hc, lc⟩ := ((cheap_collect F h d).widen (l := K) (by omega)).mono
      (d := 415) (by decide)
    have net := (ha.comp ((Circuit.id F (Flags h)).par hb)).comp hc
    refine ⟨a + ((Flags h).width + b) + c, ?_, ?_⟩
    · simp only [recurse]
      exact net
    · rw [Format.width_pair (Flags h) _] at la
      rw [show 2 * (n + 1) + 1 = (2 * n + 1) + 2 by omega, add_mul]
      omega

private theorem total_cost (h k c d : ℕ) (le : 2 + 2 * c ≤ d) :
    (2 * (h + 1) + 1) * (2 ^ h * (100 + (h + k + (h + 1))) ^ c) ≤ 2 ^ h * (100 + (h + k)) ^ d := by
  let x := 100 + (h + k)
  have ha : 100 + (h + k + (h + 1)) ≤ x ^ 2 := by unfold x; ring_nf; omega
  have hb : 2 * (h + 1) + 1 ≤ x ^ 2 := by unfold x; ring_nf; omega
  have hx : 0 < x := by omega
  calc
    _ ≤ x ^ 2 * (2 ^ h * (x ^ 2) ^ c) := Nat.mul_le_mul hb (Nat.mul_le_mul_left _ (Nat.pow_le_pow_left ha _))
    _ = 2 ^ h * x ^ (2 + 2 * c) := by rw [pow_add, pow_mul, mul_left_comm]
    _ ≤ 2 ^ h * x ^ d := Nat.mul_le_mul_left (2 ^ h) (Nat.pow_le_pow_right hx le)

theorem cheap_colours (h k : ℕ) (S : Finset (B k)) (d : ℕ) :
    Cheap F h (h + k) (GraphInput h k) (Perm h)
      (fun x => colours S d x.1.1 x.1.2 x.2) 860 := by
  obtain ⟨m, hm, hc⟩ := recurse_cost F (h + 1) h k (h + k + (h + 1)) le_rfl S d
  refine ⟨m, hm, hc.trans ?_⟩
  exact total_cost h k 415 860 (by decide)

end OAI.LinearAlgebra.MatrixExponent.Coloring
end

section
/-!
# Cost of the three permutation controllers

Fixed chart tables are read in parallel. A colour determines an offset
in a fiber. Two permutation inversions and two more reads suffice to
construct all three factor lists.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Coloring

private theorem cheap_add (F : Type) [Field F] (h : ℕ) :
    Cheap F 0 h (.pair (.addr h) (.addr h)) (.addr h) (fun x => x.1 + x.2) 4 := by
  refine ⟨_, numeric_add F h, ?_⟩
  simp only [Format.width_pair, Format.width_addr]
  ring_nf
  omega

namespace Chart

variable (F : Type) [Field F] {h : ℕ} (p : Chart h)

private theorem width_perm : (Perm h).width ≤ 2 ^ h * (100 + h) ^ 1 := by
  simp [Perm]

private theorem width_mask : (Format.vec h .bit).width ≤ 2 ^ h * (100 + h) ^ 1 := by
  rw [Format.width_vec, Format.width_bit, pow_one]
  exact Nat.mul_le_mul_left _ (by omega)

private theorem read_table (h : ℕ) : Cheap F h h (.pair (Perm h) (Perm h)) (Perm h)
    (fun x => x.1 ∘ x.2) 8 :=
  Cheap.lookup F h h (.addr h) le_rfl (by rw [Format.width_addr])

private theorem route_cheap {b c : (Perm h).obj → (Perm h).obj} {n : ℕ}
    (hb : Cheap F h h (Perm h) (Perm h) b n) (hc : Cheap F h h (Perm h) (Perm h) c n) :
    Cheap F h h (Perm h) (Perm h) (fun y => p.route (b y) (c y)) (n + 20) := by
  have add := Cheap.map _ (fun _ : B h => cheap_add F h)
  have pos := ((hb.pair hc).zip).comp add
  have table := Cheap.const F (width_perm (h := h)) width_perm p.location
  have self := Cheap.const F (width_perm (h := h)) width_perm id
  have mask := Cheap.const F (width_perm (h := h)) width_mask p.mask
  have get := (table.pair pos).comp (read_table F h)
  have data := ((get.pair self).zip.pair mask).zip
  exact (data.comp (Cheap.map _ (fun _ : B h => cheap_select F h))).mono (by omega)

private theorem twice_height (h n m : ℕ) (hm : m = 2 * n) : (100 + (h + h)) ^ n ≤ (100 + h) ^ m := by
  rw [hm, pow_mul]
  exact Nat.pow_le_pow_left (by ring_nf; omega) n

theorem run_cheap (inv : (B h → B h) → (B h → B h))
    (hi : Cheap F h h (Perm h) (Perm h) inv 100)
    (hl : Cheap F h (h + h) (GraphInput h h) (Perm h)
      (fun x => colours p.support p.degree x.1.1 x.1.2 x.2) 860) :
    Cheap F h h (Perm h) (.pair (Perm h) (.pair (Perm h) (Perm h))) (p.run inv) 1800 := by
  have cheapLabel : Cheap F h h (GraphInput h h) (Perm h)
      (fun x => colours p.support p.degree x.1.1 x.1.2 x.2) 1720 := by
    obtain ⟨m, hm, hc⟩ := hl
    refine ⟨m, hm, hc.trans (Nat.mul_le_mul_left _ ?_)⟩
    exact twice_height h 860 1720 rfl
  have y := Cheap.id F (width_perm (h := h))
  have mask := Cheap.const F (width_perm (h := h)) width_mask p.mask
  have a := Cheap.const F (width_perm (h := h)) width_perm p.base
  have b := (a.pair y).comp (read_table F h)
  have c : Cheap F h h (Perm h) (Perm h) p.label 1721 :=
    ((a.pair b).pair mask).comp cheapLabel
  have L := route_cheap F p (a.mono (d := 1721) (by decide)) c
  have R := route_cheap F p (b.mono (d := 1721) (by decide)) c
  have u := (y.pair (R.comp hi)).comp (read_table F h)
  have v := (R.pair (L.comp hi)).comp (read_table F h)
  exact (u.pair (v.pair L)).mono (by decide)

end Chart

theorem factors (F : Type) [Field F] : Factors F 1800 := by
  intro h X C A D _ _ _ _ s e
  obtain ⟨inv, hcost, hi⟩ := cheap_inverse F h
  obtain ⟨p, hp⟩ := chart_exists h X C A D s e inv hi
  exact ⟨p.run inv, p.run_cheap F inv hcost (cheap_colours F h h p.support p.degree), hp⟩

end OAI.LinearAlgebra.MatrixExponent.Coloring
end
