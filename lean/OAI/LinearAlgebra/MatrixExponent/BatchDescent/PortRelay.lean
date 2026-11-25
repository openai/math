import OAI.LinearAlgebra.MatrixExponent.Coloring.Add
import OAI.LinearAlgebra.MatrixExponent.Tagged.Array
import OAI.LinearAlgebra.MatrixExponent.Assembly.Neighborhood
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Transform
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Header
import OAI.LinearAlgebra.MatrixExponent.Install.SumOut
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Pieces

section
/-! # Exclusive prefix sums of modular addresses -/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent

open Coloring Control

private def step (a : ℕ) (x : Val (.pair (word a) (word a))) :=
  (index a).symm (index a x.1 + index a x.2)

private theorem step_net (F : Type) [Field F] (a : ℕ) :
    DNet F (.pair (word a) (word a)) (word a) (step a) (10000 * (1 + a)) := by
  have k := numeric_add F a (.pair (word a) (word a)) (word a) (.refl _) (.refl _)
  convert k using 1
  funext x
  change step a x = (bits (word a)).symm ((Format.addr a).code
    (let p := (Format.pair (.addr a) (.addr a)).code.symm (bits (.pair (word a) (word a)) x); p.1 + p.2))
  rw [decode_pair]
  apply (bits _).injective
  rw [Equiv.apply_symm_apply, ← code_addr]
  simp [step]

private def scan (a : ℕ) :
    (n : ℕ) → Val (.pair (word a) (copies (word a) n)) → Val (copies (word a) n)
  | 0, _ => ()
  | n + 1, x => (x.1, scan a n (step a (x.1, x.2.1), x.2.2))

private theorem scan_net (F : Type) [Field F] (a n : ℕ) :
    DNet F (.pair (word a) (copies (word a) n)) (copies (word a) n)
      (scan a n) (a + 20000 * n * (1 + a)) := by
  induction n with
  | zero =>
    exact (DNet.discard F _).mono (by simp [wd])
  | succ n ih =>
    have k := (DNet.fst F (word a) (word a)).pair (step_net F a)
    refine ((k.plug ih).pre (.assoc' _ _ _)).mono ?_
    simp only [wd, wd_word]
    ring_nf
    omega

private theorem layout_scan (a n : ℕ) :
    ∃ L : Layout (word a) (copies (word a) n) (Fin n), ∀ u x j,
      index a (L.read (scan a n (u, x)) j) =
        index a u + ∑ i ∈ Finset.univ.filter (· < j), index a (L.read x i) := by
  induction n with
  | zero => exact ⟨⟨Equiv.equivEmpty _⟩, fun _ _ j => j.elim0⟩
  | succ n ih =>
    obtain ⟨L, hL⟩ := ih
    let M : Layout (word a) (copies (word a) (n + 1)) (Fin (n + 1)) :=
      ⟨((finSuccEquiv n).prodCongr (.refl _)).trans
        (optionProdEquiv.trans ((Equiv.refl _).sumCongr L.positions))⟩
    have h0 (x : Val (copies (word a) (n + 1))) : M.read x 0 = x.1 := by
      unfold Layout.read
      simp [M, bits]
    have hs (x : Val (copies (word a) (n + 1))) (i : Fin n) :
        M.read x i.succ = L.read x.2 i := by
      unfold Layout.read
      simp [M, bits]
    refine ⟨M, fun u x j => ?_⟩
    induction j using Fin.cases with
    | zero => simp [scan, h0]
    | succ i =>
      rw [Finset.sum_filter, Fin.sum_univ_succ]
      simp [scan, h0, hs, hL, step, Finset.sum_filter, add_assoc]

/-- Output the incoming accumulator at every position, then add the
current record modulo the address-space size. -/
theorem prefix_sum (F : Type) [Field F] (h a : ℕ) :
    Circuit F (.vec h (.addr a)) (.vec h (.addr a))
      (fun x j => ∑ i ∈ Finset.univ.filter (· < j), x i) (100000 * 2 ^ h * (1 + a)) := by
  let n := 2 ^ h
  let z := (index a).symm 0
  obtain ⟨L, hL⟩ := layout_scan a n
  have init := ((Lookup.const_net F (word a) z).par (DNet.id F (copies (word a) n))).pre
    ((Rewire.unit' _).comp (.swap _ _))
  have net := init.comp (scan_net F a n)
  refine Circuit.of_dnet L.positions L.positions (net.mono ?_) ?_
  · simp only [wd_word, wd_copies]
    have hn : 1 ≤ n := Nat.one_le_pow _ _ (by decide)
    change _ ≤ 100000 * n * (1 + a)
    nlinarith only [Nat.mul_le_mul_right a hn]
  · intro x
    funext ⟨i, k⟩
    have he := hL z x i
    rw [show index a z = 0 from (index a).apply_symm_apply _, zero_add] at he
    let y := scan a n (z, x)
    have hb := congrFun (code_addr a (L.read y i)) k
    rw [he] at hb
    unfold Layout.read at hb
    rw [Equiv.apply_symm_apply] at hb
    exact hb.symm

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

section
/-! # The exterior bits of each stack stay together in ordered units -/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent

variable {F A : Type} {S : Assembly.Scheme F} {r : S.format.obj} {z : ℕ}

/-- Each unit is one aligned interval of an exterior span. -/
def Strips (e : A × Fin z ≃ S.exposed r) : Prop :=
  ∀ i, ∃ (a : S.Span) (k : ℕ), ∀ t,
    (e (i, t)).val.1 = a ∧ (e (i, t)).val.2.val = t.val + z * k

theorem Strips.uniform {e : A × Fin z ≃ S.exposed r} (h : Strips e) (hz : 0 < z)
    (a : S.Span) (ha : S.peer r a = none) : z ∣ S.width r a := by
  by_cases hzero : S.width r a = 0
  · simp [hzero]
  let j : S.exposed r := ⟨⟨a, ⟨S.width r a - 1, by omega⟩⟩, ha⟩
  obtain ⟨⟨i, t⟩, he⟩ := e.surjective j
  obtain ⟨b, k, hk⟩ := h i
  have hb : a = b := by simpa only [he] using (hk t).1
  subst b
  have hl : S.width r a - 1 = t.val + z * k :=
    (congrArg (fun q : S.exposed r => q.val.2.val) he).symm.trans (hk t).2
  let u : Fin z := ⟨z - 1, by omega⟩
  have hr := (e (i, u)).val.2.isLt
  rw [(hk u).2, (hk u).1] at hr
  change z - 1 + z * k < S.width r a at hr
  exact ⟨k + 1, by rw [Nat.mul_succ]; have := t.isLt; omega⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-! # Exclusive address sums from short length fields -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent

open Coloring Control Transcript Install

private def extend (a : ℕ) : (b : ℕ) → Val (word b) → Val (word (a + b))
  | 0, _ => Lookup.bits a 0
  | b + 1, x => (x.1, extend a b x.2)

private theorem value_extend (a b : ℕ) (x : Val (word b)) :
    Lookup.value (a + b) (extend a b x) = Lookup.value b x := by
  induction b with
  | zero => exact Lookup.value_bits (by positivity)
  | succ b ih =>
    change x.1.toNat + 2 * Lookup.value (a + b) (extend a b x.2) = _
    rw [ih]
    rfl

variable (F : Type) [Field F]

private theorem extend_net (a b : ℕ) : DNet F (word b) (word (a + b)) (extend a b) (a + b) := by
  induction b with
  | zero => exact (Lookup.const_net F (word a) _).mono (by simp)
  | succ b ih => exact ((DNet.id F .bit).par ih).mono (by simp [wd]; omega)

theorem widen {r j : ℕ} (hr : r ≤ j) :
    Circuit F (.addr r) (.addr j) (Fin.castLE (Nat.pow_le_pow_right (by decide : 0 < 2) hr)) j := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hr
  apply Circuit.of_dnet (.refl _) (.refl _) (extend_net F a r)
  intro x
  simp only [Equiv.coe_refl, Function.comp_id]
  rw [decode_addr, ← code_addr]
  congr 1
  exact Fin.ext (value_extend a r x)

def offsets {r j : ℕ} (hr : r ≤ j) (h : ℕ) (x : B h → B r) (i : B h) : B j :=
  ∑ k ∈ Finset.univ.filter (· < i), Fin.castLE (Nat.pow_le_pow_right (by decide : 0 < 2) hr) (x k)

theorem offsets_net {r j : ℕ} (hr : r ≤ j) (h : ℕ) :
    Circuit F (.vec h (.addr r)) (.vec h (.addr j)) (offsets hr h) (100001 * 2 ^ h * (1 + j)) := by
  have H := (Circuit.map (h := h) _ (fun _ => widen F hr)).comp (prefix_sum F h j)
  exact H.mono (by ring_nf; omega)

private theorem val_sum {I : Type} {j : ℕ} (s : Finset I) (f : I → B j)
    (h : ∑ i ∈ s, (f i).val < 2 ^ j) : (∑ i ∈ s, f i).val = ∑ i ∈ s, (f i).val := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi] at h ⊢
    rw [Fin.val_add, ih (by omega), Nat.mod_eq_of_lt h]

theorem offsets_val {r j : ℕ} (hr : r ≤ j) (h : ℕ) (x : B h → B r) (i : B h)
    (hi : ∑ k ∈ Finset.univ.filter (· < i), (x k).val < 2 ^ j) :
    (offsets hr h x i).val = ∑ k ∈ Finset.univ.filter (· < i), (x k).val :=
  val_sum _ (fun k => Fin.castLE (Nat.pow_le_pow_right (by decide : 0 < 2) hr) (x k)) hi

variable {F} {X Y : Type} [Fintype Y] {u m n : ℕ} {L : Set (Table F)}

theorem precompute (hu : 3 ≤ u) {f : (X → Bool) → Y → Bool} {k : (Y → Bool) → F}
    (hf : BNet F f m) (hk : WideWeight F u L k n) : WideWeight F u L (k ∘ f) (4 * m + n) := by
  intro a ix
  let iy : Y ≃ slots (word (Fintype.card Y)) := Fintype.equivOfCardEq (by simp)
  obtain ⟨v, hv, net⟩ := DWide.of_dnet (L := L) hu (hf a _ ix iy)
  obtain ⟨t, ht, h⟩ := hk _ iy
  refine ⟨v + t, Nat.add_le_add hv ht, ?_⟩
  simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true,
    Function.comp_def, Equiv.apply_symm_apply, Equiv.symm_apply_apply] using net.comp h

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-!
# Relaying long headers inside bins

A short description selects the source header for each target row;
sources may be reused. Work on narrow vertical slices of the entire
bin. Lengths need not be divisible by the slice count.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Transcript Classical

variable {F G R L D X T P : Type} [Field F] [Fintype G] [Fintype R] [Fintype L]
    [Fintype D] [Fintype X] [Fintype T] [Fintype P]

def relay (read : (D → Bool) → R → Option R) (ctrl : G → D → X ⊕ Bool)
    (src : G → R → L → X ⊕ Bool) (x : X → Bool) (g : G) (i : R) (k : L) : Bool :=
  (read (Sum.elim x id ∘ ctrl g) i).elim false (fun t => Sum.elim x id (src g t k))

theorem relay_net {w j u : ℕ} (hj : w ≤ j) (hj' : j + 1 ≤ 2 * w) (hu : 3 ≤ u)
    (ha : 2 * 2 ^ (j + 1) * (2 * j + 2) ≤ u)
    (read : (D → Bool) → R → Option R) (ctrl : G → D → X ⊕ Bool)
    (src dst : G → R → L → X ⊕ Bool) (layout : L ↪ T × P)
    (hk : Fintype.card D + 2 * (Fintype.card R * Fintype.card P) < j)
    (hn : Fintype.card G * Fintype.card T ≤ 2 ^ j) :
    WideWeight F u (SortTables F w)
      (fun x => if ∀ g i k, Sum.elim x id (dst g i k) = relay read ctrl src x g i k then 1 else 0)
      (4 * Fintype.card X + 11000 * 2 ^ j * (1 + j)) := by
  let tape (tap : G → R → L → X ⊕ Bool) (a : G × T) (z : R × P) :=
    Function.extend layout (tap a.1 z.1) (fun _ => Sum.inr false) (a.2, z.2)
  let calls (a : G × T) := Sum.elim (ctrl a.1) (Sum.elim (tape src a) (tape dst a))
  let eqn (x : D ⊕ (R × P) ⊕ (R × P) → Bool) :=
    ∀ i k, x (.inr (.inr (i, k))) =
      (read (x ∘ Sum.inl) i).elim false (fun t => x (.inr (.inl (t, k))))
  let test x : F := if eqn x then 1 else 0
  have H := dictionary hj hj' hu ha
    (by simp only [Fintype.card_sum, Fintype.card_prod]; omega)
    (by simpa using hn) test calls
  convert H using 1
  funext x
  have arg (a : G × T) : eqn (Sum.elim x id ∘ calls a) ↔ ∀ i k,
      Sum.elim x id (tape dst a (i, k)) =
        (read (Sum.elim x id ∘ ctrl a.1) i).elim false (fun t => Sum.elim x id (tape src a (t, k))) :=
    Iff.rfl
  have valid : (∀ a, eqn (Sum.elim x id ∘ calls a)) ↔
      ∀ g i k, Sum.elim x id (dst g i k) = relay read ctrl src x g i k := by
    simp only [arg, relay]
    constructor
    · intro h g i k
      simpa only [tape, Prod.mk.eta, layout.injective.extend_apply] using
        h (g, (layout k).1) i (layout k).2
    · rintro h ⟨g, t⟩ i k
      by_cases he : (t, k) ∈ Set.range layout
      · obtain ⟨l, hl⟩ := he
        simpa only [tape, ← hl, layout.injective.extend_apply] using h g i l
      · have ht (f) (r) : tape f (g, t) (r, k) = .inr false :=
          Function.extend_apply' _ _ _ he
        simp only [ht, Sum.elim_inr, id_eq]
        cases read _ i <;> rfl
  simp only [← valid, test]
  by_cases h : ∀ a, eqn (Sum.elim x id ∘ calls a)
  · simp [h]
  · rw [ite_eq_right h, eq_comm]
    obtain ⟨a, ha⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ a) (ite_eq_right ha)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-!
# Recovering the ordered exterior units

An aligned equivalence on bits descends to an equivalence on units
without changing the within-unit index.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent

variable {F A : Type} {S : Assembly.Scheme F} {r : S.format.obj} {z : ℕ}
    (hu : ∀ i j, Parts.Uniform (pattern S r i j) z)

def toOuter (x : outer S r z) (t : Fin z) : S.exposed r :=
  ⟨join S r z hu (x.val, t), x.property⟩

namespace Strips
variable {e : A × Fin z ≃ S.exposed r}

private theorem one (h : Strips e) (hz : 0 < z) (i : A) :
    ∃ a : outer S r z, ∀ t, e (i, t) = toOuter hu a t := by
  obtain ⟨s, k, hk⟩ := h i
  let last : Fin z := ⟨z - 1, by omega⟩
  have hl := (e (i, last)).val.2.isLt
  rw [(hk last).2, (hk last).1] at hl
  change z - 1 + z * k < S.width r s at hl
  have hd : k + 1 ≤ S.width r s / z := by
    apply (Nat.le_div_iff_mul_le hz).mpr
    rw [mul_comm, Nat.mul_add, Nat.mul_one]
    omega
  let w : units S r z := ⟨s.1.1, s.1.2.1, (s.1.2.2, s.2), ⟨k, hd⟩⟩
  have hv : S.peer r (unitSpan w) = none := by
    change S.peer r s = none
    rw [← (hk last).1]
    exact (e (i, last)).property
  refine ⟨⟨w, hv⟩, fun t => Subtype.ext ?_⟩
  refine Sigma.ext (hk t).1 ((Fin.heq_ext_iff (congrArg (S.width r) (hk t).1)).mpr ?_)
  exact (hk t).2

theorem segments (h : Strips e) (hz : 0 < z) :
    ∃ f : A ≃ outer S r z, ∀ i t, e (i, t) = toOuter hu (f i) t := by
  choose f hf using one hu h hz
  let t : Fin z := ⟨0, hz⟩
  have hi : Function.Injective f := by
    intro i j he
    have hh : e (i, t) = e (j, t) := by rw [hf, he, hf]
    exact congrArg Prod.fst (e.injective hh)
  have hs : Function.Surjective f := by
    intro b
    obtain ⟨⟨i, j⟩, he⟩ := e.surjective (toOuter hu b t)
    rw [hf] at he
    have hh := (join S r z hu).injective (congrArg Subtype.val he)
    exact ⟨i, Subtype.ext (congrArg Prod.fst hh)⟩
  exact ⟨Equiv.ofBijective f ⟨hi, hs⟩, hf⟩

end Strips
end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-!
# Placing host descriptors at their start offsets

A shared dictionary computes lengths. Exclusive prefix sums give
destinations; scattering checks the entire proposed output including
the blank positions. Arithmetic cannot wrap at a valid destination.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Coloring Control Transcript Install Classical

variable {F X D T : Type} [Field F] [Fintype X] [Fintype D] [Fintype T] {w j h u r : ℕ}

/-- A named array of binary addresses of width `j` bits. -/
abbrev Addresses (I : Type) [Fintype I] (j : ℕ) : Format :=
  ⟨I → B j, I × slots (word j),
    (Equiv.piCongrRight (fun _ => (Format.addr j).code)).trans (Equiv.curry _ _ _).symm⟩

private theorem cost_bound {M H I J w j r : ℕ} (hh : H ≤ J) (hi : I ≤ J)
    (hr : r ≤ j) (hj : j ≤ 2 * w) :
    8 * (M + H * r) + 9 * (4 * (M + H * r) + 11000 * J * (1 + j) +
      (4 * (M + (100001 * H * (1 + j) + 100000 * J * (1 + j))) + 10000 * (M + I * j + J * w))) ≤ 10 ^ 9 * (M + J * (1 + w)) := by
  have h₁ := Nat.mul_le_mul hh (hr.trans hj)
  have h₂ := Nat.mul_le_mul hh hj
  have h₃ := Nat.mul_le_mul_left J hj
  have h₄ := Nat.mul_le_mul hi hj
  ring_nf at *
  omega

/-- Compute destinations from the exclusive count offsets before
scattering a possibly different collection of records. -/
theorem scatter_with {I L : Type} [Fintype I] [Fintype L]
    (len : (D → Bool) → ℕ) (src : Fin (2 ^ h) → D → X ⊕ Bool) (data : I → L → X ⊕ Bool)
    (dst : T → L → X ⊕ Bool) (used : T → X ⊕ Bool) (name : T ↪ Fin (2 ^ j))
    (post : (B h → B j) → I → B j)
    (net : Circuit F (.vec h (.addr j)) (Addresses I j) post (100000 * 2 ^ j * (1 + j)))
    (hj : w ≤ j) (hj' : j + 1 ≤ 2 * w) (hu : 3 ≤ u) (ha : 2 * 2 ^ (2 * w) * (4 * w) ≤ u)
    (hd : Fintype.card D + r < j) (hH : 2 ^ h ≤ 2 ^ j)
    (hL : j + Fintype.card L + 2 ≤ 4 * w) (hsize : Fintype.card I + Fintype.card T ≤ 2 ^ j) :
    ∃ f : (X → Bool) → F, WideWeight F u (SortTables F w) f (10 ^ 9 * (Fintype.card X + 2 ^ j * (1 + w))) ∧
      ∀ (x : X → Bool) (e : I ↪ T) (p : B h → B j),
        (∀ i, len (Sum.elim x id ∘ src i) < 2 ^ r) →
        (∀ i, (p i).val = ∑ v ∈ Finset.univ.filter (· < i), len (Sum.elim x id ∘ src v)) →
        (∀ i, post p i = name (e i)) →
        f x = if (∀ v, Sum.elim x id (used v) = true ↔ v ∈ Set.range e) ∧
          ∀ v k, Sum.elim x id (dst v k) =
            Function.extend e (fun i => Sum.elim x id (data i k)) (fun _ => false) v
          then 1 else 0 := by
  have hr : r ≤ j := by omega
  let A := Format.vec h (.addr r)
  let Z := Addresses I j
  let ask (y : D → Bool) := bits (word r) (Lookup.bits r (len y))
  let lengths := applyRows ask src (Equiv.refl A.pins)
  have hu' : 2 * 2 ^ (j + 1) * (2 * j + 2) ≤ u := by
    refine le_trans ?_ ha
    exact Nat.mul_le_mul (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) hj')) (by omega)
  have grab := transform (F := F) ask src (Equiv.refl A.pins) hj hj' hu hu'
    (by simpa using hd) (by simp; omega)
  let expand : X ⊕ Bool → (X ⊕ Z.pins) ⊕ Bool := Sum.map Sum.inl id
  let adr (i : I) (k : slots (word j)) : (X ⊕ Z.pins) ⊕ Bool := .inl (.inr (i, k))
  have hu'' : 2 * 2 ^ j * (4 * w) ≤ u := by
    refine le_trans ?_ ha
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ (Nat.pow_le_pow_right (by decide) (by omega)))
  obtain ⟨f, hf, he⟩ := scatter F (name.trans (index j).symm.toEmbedding) adr
    (fun i => expand ∘ data i) (fun i => expand ∘ dst i) (expand ∘ used) hj (by omega) hu hu''
    hL hsize
  let next := Z.code ∘ (post ∘ offsets hr h) ∘ A.code.symm
  let join (y : X ⊕ A.pins → Bool) := Sum.elim (y ∘ Sum.inl) (next (y ∘ Sum.inr))
  have step : BNet F join (Fintype.card X + (100001 * 2 ^ h * (1 + j) + 100000 * 2 ^ j * (1 + j))) :=
    (BNet.id F X).parallel ((offsets_net F hr h).comp net)
  have check := bind hu grab (precompute hu step hf)
  let run (x : X → Bool) := Sum.elim x (next (lengths x))
  refine ⟨f ∘ run, ?_, fun x e p hl hn hp => ?_⟩
  · intro a ix
    obtain ⟨q, hq, hnet⟩ := check a ix
    refine ⟨q, hq.trans ?_, hnet⟩
    simp only [Fintype.card_sum, A, Z, Fintype.card_prod, Fintype.card_fin, card_slots, wd_word]
    exact cost_bound hH (by omega) hr (by omega)
  · have hv (i) : (A.code.symm (lengths x) i).val = len (Sum.elim x id ∘ src i) := by
      change (index r ((bits (word r)).symm (ask (Sum.elim x id ∘ src i)))).val = _
      unfold ask
      rw [Equiv.symm_apply_apply]
      exact Lookup.value_bits (hl i)
    have hpos : offsets hr h (A.code.symm (lengths x)) = p := by
      funext i
      apply Fin.ext
      rw [offsets_val, hn]
      · simp only [hv]
      · simp only [hv, ← hn i]
        exact (p i).isLt
    have hok (i) : bits (word j) ((name.trans (index j).symm.toEmbedding) (e i)) =
        Sum.elim (run x) id ∘ adr i := by
      change bits (word j) ((index j).symm (name (e i))) =
        (Format.addr j).code (post (offsets hr h (A.code.symm (lengths x))) i)
      rw [hpos, hp]
      rfl
    have tap (i : X ⊕ Bool) : Sum.elim (run x) id (expand i) = Sum.elim x id i := by cases i <;> rfl
    simpa only [Function.comp_apply, tap] using he (run x) e hok

theorem short_scatter (len : (D → Bool) → ℕ) (src : Fin (2 ^ h) → D → X ⊕ Bool)
    (dst : T → D → X ⊕ Bool) (used : T → X ⊕ Bool) (name : T ↪ Fin (2 ^ j))
    (hj : w ≤ j) (hj' : j + 1 ≤ 2 * w) (hu : 3 ≤ u) (ha : 2 * 2 ^ (2 * w) * (4 * w) ≤ u)
    (hd : Fintype.card D + r < j) (hsize : 2 ^ h + Fintype.card T ≤ 2 ^ j) :
    ∃ f : (X → Bool) → F, WideWeight F u (SortTables F w) f (10 ^ 9 * (Fintype.card X + 2 ^ j * (1 + w))) ∧
      ∀ (x : X → Bool) (e : Fin (2 ^ h) ↪ T),
        (∀ i, len (Sum.elim x id ∘ src i) < 2 ^ r) →
        (∀ i, (name (e i)).val = ∑ v ∈ Finset.univ.filter (· < i), len (Sum.elim x id ∘ src v)) →
        f x = if (∀ v, Sum.elim x id (used v) = true ↔ v ∈ Set.range e) ∧
          ∀ v k, Sum.elim x id (dst v k) =
            Function.extend e (fun i => Sum.elim x id (src i k)) (fun _ => false) v
          then 1 else 0 := by
  have hH : 2 ^ h ≤ 2 ^ j := by omega
  have net : Circuit F (.vec h (.addr j)) (Addresses (B h) j) id (100000 * 2 ^ j * (1 + j)) := by
    refine (Circuit.id F (.vec h (.addr j))).mono ?_
    rw [Format.width_vec, Format.width_addr]
    have := Nat.mul_le_mul_right j hH
    ring_nf at this ⊢
    omega
  obtain ⟨f, hf, he⟩ := scatter_with len src src dst used name id net hj hj' hu ha hd hH
    (by omega) (by simpa using hsize)
  exact ⟨f, hf, fun x e hl hp => he x e (name ∘ e) hl hp (fun _ => rfl)⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

section
/-! # Binary addresses of consecutive port headers -/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
open Coloring Install Control

private def clearLow (a : ℕ) : (r : ℕ) → Val (word (a + r)) → Val (word (a + r))
  | 0, x => x
  | r + 1, x => (false, clearLow a r x.2)

private theorem clear_val (a r : ℕ) (x : Val (word (a + r))) :
    Lookup.value (a + r) (clearLow a r x) = Lookup.value (a + r) x / 2 ^ r * 2 ^ r := by
  induction r with
  | zero => simp [clearLow]
  | succ r ih =>
    have hx : Lookup.value (a + (r + 1)) x / 2 = Lookup.value (a + r) x.2 := by
      change (x.1.toNat + 2 * Lookup.value (a + r) x.2) / 2 = _
      cases x.1 <;> simp
      omega
    rw [pow_succ', ← Nat.div_div_eq_div_mul, hx]
    change 0 + 2 * Lookup.value (a + r) (clearLow a r x.2) = _
    rw [ih]
    ring

variable (F : Type) [Field F]

private theorem clear_net (a r : ℕ) :
    DNet F (word (a + r)) (word (a + r)) (clearLow a r) (a + r) := by
  induction r with
  | zero => exact (DNet.id F (word a)).mono (by simp)
  | succ r ih =>
    exact ((DNet.table F .bit .bit (fun _ => false) (by decide)).par ih).mono (by omega)

private def high (r j : ℕ) (i : B j) : B j :=
  ⟨i.val / 2 ^ r * 2 ^ r, (Nat.div_mul_le_self ..).trans_lt i.isLt⟩

private theorem high_net {r j : ℕ} (hr : r ≤ j) :
    Circuit F (.addr j) (.addr j) (high r j) j := by
  obtain ⟨a, rfl⟩ := Nat.exists_eq_add_of_le' hr
  apply Circuit.of_dnet (.refl _) (.refl _) (clear_net F a r)
  intro x
  simp only [Equiv.coe_refl, Function.comp_id]
  rw [decode_addr, ← code_addr]
  congr 1
  exact Fin.ext (clear_val a r x)

/-- Double the bin stride, preserving the offset and adding the port number. -/
def portOffset {j : ℕ} (r k : ℕ) (i : B j) : B j :=
  i + high r j i + Fin.ofNat _ k

theorem portOffset_val {j : ℕ} (r k : ℕ) (i : B j) :
    (portOffset r k i).val = (i.val / 2 ^ r * (2 * 2 ^ r) + i.val % 2 ^ r + k) % 2 ^ j := by
  unfold portOffset
  simp only [Fin.val_add, Fin.val_ofNat, Nat.add_mod_mod, Nat.mod_add_mod, high]
  have := Nat.div_add_mod i.val (2 ^ r)
  congr 1
  nlinarith

private theorem port_net {r j : ℕ} (hr : r ≤ j) (k : ℕ) :
    Circuit F (.addr j) (.addr j) (portOffset r k) (30000 * (1 + j)) := by
  have fixed : Circuit F (.addr j) (.addr j) (fun _ => Fin.ofNat _ k) (2 * j) := by
    let c := (index j).symm (Fin.ofNat (2 ^ j) k)
    have h := (DNet.discard F (word j)).comp (Lookup.const_net F (word j) c)
    apply Circuit.of_dnet (.refl _) (.refl _) (h.mono (n := 2 * j) (by simp; omega))
    intro x
    rfl
  have h := ((Circuit.id F (.addr j)).pair (high_net F hr)).comp (numeric_add F j)
  exact ((h.pair fixed).comp (numeric_add F j)).mono (by simp; omega)

theorem portOffsets {r j h d : ℕ} (hr : r ≤ j) (hh : 2 ^ h ≤ 2 ^ j) (hd : 2 ^ h * d ≤ 2 ^ j) :
    Circuit F (.vec h (.addr j)) (Addresses (B h × Fin d) j)
      (fun x p => portOffset r p.2.val (x p.1)) (100000 * 2 ^ j * (1 + j)) := by
  let A := Format.vec h (.addr j)
  have one (i : Fin d) :
      Circuit F A A (fun x k => portOffset r i.val (x k)) (2 ^ h * (30000 * (1 + j))) :=
    Circuit.map _ (fun _ => port_net F hr i.val)
  let e : Fin d × A.pins ≃ (B h × Fin d) × slots (word j) :=
    (Equiv.prodAssoc _ _ _).symm.trans ((Equiv.prodComm _ _).prodCongr (.refl _))
  have net := (BNet.finite_share _ one).rename (.refl _) e
  refine net.mono ?_
  change A.width + Fintype.card (Fin d) * (5 * A.width + 2 ^ h * (30000 * (1 + j))) ≤ _
  rw [Fintype.card_fin, Format.width_vec, Format.width_addr]
  have h₁ := Nat.mul_le_mul_right j hh
  have h₂ := Nat.mul_le_mul_right j hd
  ring_nf at h₁ h₂ hd ⊢
  omega

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
end

/-!
# Scattering short and long headers into bins

Short headers use a bin stride of one half-bin. Long headers use the
full stride and one row per port. The packing inequalities exclude
modular wraparound in both address calculations.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows

open Coloring Transcript Classical

variable {X D L : Type} {h j w u r K m d cap : ℕ}

private def addressName {v : ℕ} (hk : K * v ≤ 2 ^ j) : Fin K × Fin v ↪ B j :=
  finProdFinEquiv.toEmbedding.trans (Fin.castLEEmb hk)

private theorem name_anchor (l : Inventory (2 ^ h) m d) (hs : ∀ i, size (l i) u ≤ 2 ^ r)
    (hk : bins l u (2 ^ r) ≤ K) (hab : K * 2 ^ r ≤ 2 ^ j) (i : B h) :
    (addressName hab (anchor l u (2 ^ r) K (Nat.two_pow_pos r) hs hk i)).val = start (counts l u) i :=
  Nat.mod_add_div _ _

private theorem length_bounds (l : Inventory (2 ^ h) m d) (hs : ∀ i, size (l i) u ≤ 2 ^ r)
    (v : B h → ℕ) (he : ∀ i, v i = counts l u i) :
    (∀ i, v i < 2 ^ (r + 1)) ∧ ∀ i, start (counts l u) i = ∑ k ∈ Finset.univ.filter (· < i), v k := by
  constructor
  · intro i
    rw [he]
    exact (hs i).trans_lt (pow_lt_pow_right₀ (by decide) (by omega))
  · intro i
    simp only [he]
    rfl

variable (F : Type) [Field F] [Fintype X] [Fintype D]

theorem anchor_scatter (len : (D → Bool) → ℕ) (src : B h → D → X ⊕ Bool)
    (dst : Anchor (2 ^ r) K → D → X ⊕ Bool) (used : Anchor (2 ^ r) K → X ⊕ Bool)
    (hj : w ≤ j) (hj' : j + 1 ≤ 2 * w) (hc : 3 ≤ cap) (ha : 2 * 2 ^ (2 * w) * (4 * w) ≤ cap)
    (hd : Fintype.card D + (r + 1) < j) (hsize : 2 ^ h + K * 2 ^ r ≤ 2 ^ j) :
    ∃ f : (X → Bool) → F, WideWeight F cap (SortTables F w) f (10 ^ 9 * (Fintype.card X + 2 ^ j * (1 + w))) ∧
      ∀ (x : X → Bool) (l : Inventory (2 ^ h) m d) (hs : ∀ i, size (l i) u ≤ 2 ^ r)
        (hk : bins l u (2 ^ r) ≤ K),
        (∀ i, len (Sum.elim x id ∘ src i) = counts l u i) →
        let e := anchor l u (2 ^ r) K (Nat.two_pow_pos r) hs hk
        f x = if (∀ v, Sum.elim x id (used v) = true ↔ v ∈ Set.range e) ∧
          ∀ v k, Sum.elim x id (dst v k) =
            Function.extend e (fun i => Sum.elim x id (src i k)) (fun _ => false) v
          then 1 else 0 := by
  have hab : K * 2 ^ r ≤ 2 ^ j := (Nat.le_add_left _ _).trans hsize
  obtain ⟨f, hf, he⟩ := short_scatter (F := F) len src dst used (addressName hab) hj hj' hc ha hd
    (by simpa only [Anchor, Address, B, Fintype.card_prod, Fintype.card_fin] using hsize)
  refine ⟨f, hf, fun x l hs hk hl => ?_⟩
  obtain ⟨small, offset⟩ := length_bounds l hs _ hl
  let e := anchor l u (2 ^ r) K (Nat.two_pow_pos r) hs hk
  have out := he x e small (fun i => (name_anchor l hs hk hab i).trans (offset i))
  refine out.trans ?_
  split <;> rfl

theorem port_scatter [Fintype L] (len : (D → Bool) → ℕ) (src : B h → D → X ⊕ Bool)
    (srcLong : B h × Fin d → L → X ⊕ Bool)
    (dst : Address (2 ^ r) K → L → X ⊕ Bool) (used : Address (2 ^ r) K → X ⊕ Bool)
    (hj : w ≤ j) (hj' : j + 1 ≤ 2 * w) (hc : 3 ≤ cap) (ha : 2 * 2 ^ (2 * w) * (4 * w) ≤ cap)
    (hd : Fintype.card D + (r + 1) < j) (hL : j + Fintype.card L + 2 ≤ 4 * w)
    (hsize : 2 ^ h * d + K * (2 * 2 ^ r) ≤ 2 ^ j) (hdpos : 0 < d) :
    ∃ f : (X → Bool) → F, WideWeight F cap (SortTables F w) f (10 ^ 9 * (Fintype.card X + 2 ^ j * (1 + w))) ∧
      ∀ (x : X → Bool) (l : Inventory (2 ^ h) m d) (hs : ∀ i, size (l i) u ≤ 2 ^ r)
        (hk : bins l u (2 ^ r) ≤ K),
        (∀ i, len (Sum.elim x id ∘ src i) = counts l u i) →
        let e := portAnchor l u (2 ^ r) K (Nat.two_pow_pos r) hs hk
        f x = if (∀ v, Sum.elim x id (used v) = true ↔ v ∈ Set.range e) ∧
          ∀ v k, Sum.elim x id (dst v k) =
            Function.extend e (fun i => Sum.elim x id (srcLong i k)) (fun _ => false) v
          then 1 else 0 := by
  have hrow : 2 ^ h * d ≤ 2 ^ j := (Nat.le_add_right _ _).trans hsize
  have hH : 2 ^ h ≤ 2 ^ j := (Nat.le_mul_of_pos_right _ hdpos).trans hrow
  have hab : K * (2 * 2 ^ r) ≤ 2 ^ j := (Nat.le_add_left _ _).trans hsize
  have hab' : K * 2 ^ r ≤ 2 ^ j := (Nat.mul_le_mul_left K (by omega)).trans hab
  have hp := portOffsets F (show r ≤ j by omega) hH hrow
  obtain ⟨f, hf, he⟩ := scatter_with len src srcLong dst used (addressName hab) _ hp hj hj' hc ha hd hH hL
    (by simpa only [Anchor, Address, B, Fintype.card_prod, Fintype.card_fin] using hsize)
  refine ⟨f, hf, fun x l hs hk hl => ?_⟩
  obtain ⟨small, offset⟩ := length_bounds l hs _ hl
  let pos (i : B h) := addressName hab' (anchor l u (2 ^ r) K (Nat.two_pow_pos r) hs hk i)
  let e := portAnchor l u (2 ^ r) K (Nat.two_pow_pos r) hs hk
  suffices ha : ∀ i, portOffset r i.2.val (pos i.1) = addressName hab (e i) by
    have out := he x e pos small (fun i => (name_anchor l hs hk hab' i).trans (offset i)) ha
    refine out.trans ?_
    split <;> rfl
  intro i
  apply Fin.ext
  rw [portOffset_val, show (pos i.1).val = _ from name_anchor l hs hk hab' i.1]
  have hv : (addressName hab (e i)).val =
      start (counts l u) i.1 / 2 ^ r * (2 * 2 ^ r) + start (counts l u) i.1 % 2 ^ r + i.2.val := by
    change (e i).2.val + (2 * 2 ^ r) * (e i).1.val = _
    obtain ⟨h₁, h₂⟩ := portAnchor_val l u (2 ^ r) K (Nat.two_pow_pos r) hs hk i
    rw [h₁, h₂]
    ring
  rw [← hv, Nat.mod_eq_of_lt (addressName hab (e i)).isLt]

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
end

/-!
# Long port descriptors with private anchor tapes

Scatter one descriptor per port to its anchor and relay it within
the bin. The activity bits and contents of every anchor are forced,
so summing over this intermediate tape has multiplicity one.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
open Classical Transcript Coloring

variable {F X Y : Type} [Field F] [Fintype X] [Fintype Y] {m n cap : ℕ}

/-- Hide a witness tape that is uniquely determined on valid inputs. -/
theorem hide_unique {G : Set (Table F)} (hu : 3 ≤ cap) {f k : (X ⊕ Y → Bool) → F}
    (hf : WideWeight F cap G f m) (hk : WideWeight F cap G k n) :
    ∃ h, WideWeight F cap G h (8 * (Fintype.card X + Fintype.card Y) + 9 * (m + n)) ∧
      ∀ x y, (∀ z, f (Sum.elim x z) = if y = z then 1 else 0) → h x = k (Sum.elim x y) := by
  let jobs (b : Bool) := if b then f else k
  let costs (b : Bool) := if b then m else n
  have ready (b : Bool) : WideWeight F cap G (jobs b) (costs b) := by
    cases b
    · exact hk
    · exact hf
  have H := wide_sum jobs (fun _ => id) costs hu ready
  refine ⟨weightedSum jobs (fun _ => id), by simpa [costs] using H, ?_⟩
  intro x y h
  simp [weightedSum, jobs, h, ite_mul]

variable {Z D L T P : Type} {h r K d u j w : ℕ}
abbrev RelayRead (L : Type) (r : ℕ) := (L → Bool) → Fin (2 * 2 ^ r) → Option (Fin (2 * 2 ^ r))

def delivered (e : B h × Fin d ↪ Address (2 ^ r) K)
    (srcLong : B h × Fin d → Z → X ⊕ Bool) (read : RelayRead L r) (ctrl : Fin K → L → X ⊕ Bool)
    (x : X → Bool) (a : Address (2 ^ r) K) (k : Z) : Bool :=
  (read (Sum.elim x id ∘ ctrl a.1) a.2).elim false fun t =>
    Function.extend e (fun i => Sum.elim x id (srcLong i k)) (fun _ => false) (a.1, t)

def liftTap (t : X ⊕ Bool) : (X ⊕ Y) ⊕ Bool := Sum.map Sum.inl id t

omit [Fintype X] [Fintype Y] in
@[simp] theorem read_lift (x : X → Bool) (y : Y → Bool) (t : X ⊕ Bool) :
    Sum.elim (Sum.elim x y) id (liftTap t) = Sum.elim x id t := by cases t <;> rfl

omit [Fintype X] [Fintype Y] in
@[simp] theorem read_lift_fun (x : X → Bool) (y : Y → Bool) (f : T → X ⊕ Bool) :
    Sum.elim (Sum.elim x y) id ∘ liftTap ∘ f = Sum.elim x id ∘ f :=
  funext (fun _ => read_lift _ _ _)

private theorem bound {X Y w j : ℕ} (hj : j ≤ 2 * w) (hy : Y ≤ 2 ^ j * (4 * w + 1)) :
    8 * (X + Y) + 9 * (10 ^ 9 * (X + Y + 2 ^ j * (1 + w)) + (4 * (X + Y) + 11000 * 2 ^ j * (1 + j))) ≤
      10 ^ 12 * (X + 2 ^ j * (1 + w)) := by
  have := Nat.mul_le_mul_left (2 ^ j) hj
  ring_nf at *
  omega

theorem port_relay (F : Type) [Field F] [Fintype D] [Fintype Z] [Fintype L] [Fintype T] [Fintype P]
    (len : (D → Bool) → ℕ) (src : B h → D → X ⊕ Bool) (srcLong : B h × Fin d → Z → X ⊕ Bool)
    (read : RelayRead L r) (ctrl : Fin K → L → X ⊕ Bool)
    (dst : Address (2 ^ r) K → Z → X ⊕ Bool) (layout : Z ↪ T × P)
    (hj : w ≤ j) (hj' : j + 1 ≤ 2 * w) (hc : 3 ≤ cap) (ha : 2 * 2 ^ (2 * w) * (4 * w) ≤ cap)
    (hd : Fintype.card D + (r + 1) < j) (hL : j + Fintype.card Z + 2 ≤ 4 * w)
    (hsize : 2 ^ h * d + K * (2 * 2 ^ r) ≤ 2 ^ j) (hdpos : 0 < d)
    (hz : Fintype.card L + 2 * ((2 * 2 ^ r) * Fintype.card P) < j) (ht : K * Fintype.card T ≤ 2 ^ j) :
    ∃ f : (X → Bool) → F, WideWeight F cap (SortTables F w) f (10 ^ 12 * (Fintype.card X + 2 ^ j * (1 + w))) ∧
      ∀ (x : X → Bool) (l : Inventory (2 ^ h) m d) (hs : ∀ i, size (l i) u ≤ 2 ^ r)
        (hk : bins l u (2 ^ r) ≤ K),
        (∀ i, len (Sum.elim x id ∘ src i) = counts l u i) →
        f x = if ∀ v, Sum.elim x id ∘ dst v =
          delivered (portAnchor l u (2 ^ r) K (Nat.two_pow_pos r) hs hk) srcLong read ctrl x v
          then 1 else 0 := by
  let Y := Address (2 ^ r) K × Option Z
  let get (v : Address (2 ^ r) K) (k : Z) : (X ⊕ Y) ⊕ Bool := .inl (.inr (v, some k))
  let used (v : Address (2 ^ r) K) : (X ⊕ Y) ⊕ Bool := .inl (.inr (v, none))
  obtain ⟨t, ht₁, ht₂⟩ := port_scatter (m := m) (u := u) F len (fun i => liftTap ∘ src i)
    (fun i => liftTap ∘ srcLong i) get used hj hj' hc ha hd hL hsize hdpos
  have ha' : 2 * 2 ^ (j + 1) * (2 * j + 2) ≤ cap := le_trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) hj')) (by omega)) ha
  have hnet := relay_net (F := F) hj hj' hc ha' read (fun i => liftTap ∘ ctrl i)
    (Function.curry get) (fun i j => liftTap ∘ dst (i, j)) layout (by simpa using hz) (by simpa using ht)
  obtain ⟨f, hf, he⟩ := hide_unique hc ht₁ hnet
  refine ⟨f, ?_, fun x l hs hk hl => ?_⟩
  · have hY : Fintype.card Y ≤ 2 ^ j * (4 * w + 1) := by
      simp only [Y, Address, Fintype.card_prod, Fintype.card_option, Fintype.card_fin]
      exact Nat.mul_le_mul (by omega) (by omega)
    intro a i
    obtain ⟨v, hv, he⟩ := hf a i
    refine ⟨v, hv.trans ?_, he⟩
    rw [Fintype.card_sum]
    exact bound (by omega) hY
  let e := portAnchor l u (2 ^ r) K (Nat.two_pow_pos r) hs hk
  let data (i : Address (2 ^ r) K) (k : Z) :=
    Function.extend e (fun j => Sum.elim x id (srcLong j k)) (fun _ => false) i
  let values : Y → Bool := fun p => p.2.elim (decide (p.1 ∈ Set.range e)) (data p.1)
  have unique (y : Y → Bool) : t (Sum.elim x y) = if values = y then 1 else 0 := by
    rw [ht₂ _ l hs hk (by simpa only [read_lift_fun] using hl)]
    simp only [used, get, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, read_lift]
    congr 1
    apply propext
    constructor
    · rintro ⟨h₁, h₂⟩
      funext ⟨i, q⟩
      rcases q with _|k
      · exact Bool.eq_iff_iff.mpr (decide_eq_true_iff.trans (h₁ i).symm)
      · exact (h₂ i k).symm
    · rintro rfl
      exact ⟨fun _ => decide_eq_true_iff, fun _ _ => rfl⟩
  rw [he x values unique]
  simp only [relay, read_lift_fun, Function.comp_apply, read_lift, Function.curry_apply, get,
    Sum.elim_inl, Sum.elim_inr]
  congr 1
  exact propext ⟨fun h i => funext (h i.1 i.2), fun h i j => congrFun (h (i, j))⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
end
