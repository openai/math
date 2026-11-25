import OAI.LinearAlgebra.MatrixExponent.Transcript.Seats
import OAI.LinearAlgebra.MatrixExponent.Coloring.VectorSort
import OAI.LinearAlgebra.MatrixExponent.Install.Products
import OAI.LinearAlgebra.MatrixExponent.Install.ControlWeight
import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Machine
import OAI.LinearAlgebra.MatrixExponent.Diagram.Canonical
import OAI.LinearAlgebra.MatrixExponent.Diagram.Present
import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.StringOrder
import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Physical

/-! # Literal bits in weighted sums over a hidden tape -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol

open scoped Classical

/-- Add the two literal bits to the public tape before evaluating the
transcript. Both literals are fixed, so no new assignments are summed. -/
theorem sum_net {F X Y I : Type} [Field F] [Fintype X] [Fintype Y] [Fintype I]
    {Z : I → Type} [∀ i, Fintype (Z i)] {u : ℕ} {L : Set (Table F)}
    (f : (i : I) → (Z i → Bool) → F) (read : (i : I) → Z i → (X ⊕ Bool) ⊕ Y) (m : I → ℕ)
    (hu : 3 ≤ u) (hm : ∀ i, WideWeight F u L (f i) (m i)) :
    WideWeight F u L (fun x => ∑ y : Y → Bool, ∏ i, f i (Sum.elim (Sum.elim x id) y ∘ read i))
      (100 * (1 + Fintype.card X + Fintype.card Y+∑ i, m i)) := by
  intro a ix
  let ib : Bool ≃ slots (word 2) := Fintype.equivOfCardEq (by simp)
  let z := (bits (word 2)).symm ib.symm
  let b := Wire.pair a (word 2)
  let e : X ⊕ Bool ≃ slots b := ix.sumCongr ib
  have he (x : Val a) : bits b (x, z) ∘ e = Sum.elim (bits a x ∘ ix) id := by
    funext p
    cases p with
    | inl k => rfl
    | inr k =>
      change bits (word 2) z (ib k) = k
      simp only [z, Equiv.apply_symm_apply, Equiv.symm_apply_apply]
  have prep : DNet F a b (fun x => (x, z)) (wd a + 1) :=
    ((DNet.id F a).par (DNet.table F .unit (word 2) (fun _ => z) (by decide))).pre (.unit' _)
  obtain ⟨v, hv, hp⟩ := prep
  obtain ⟨s, hs, ps⟩ := hp.includeWide (L := L) hu
  obtain ⟨t, ht, pt⟩ := wide_sum f read m hu hm b e
  refine ⟨s + t, ?_, ?_⟩
  · rw [Fintype.card_sum, Fintype.card_bool] at ht
    have := (Fintype.card_congr ix).trans (MatrixExponent.card_slots a)
    omega
  · simpa only [ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, ite_true, he, weightedSum]
      using ps.comp pt

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end

section
/-! # Trivalent check for the range and activity of an encoded processor number -/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol

open Coloring Install
variable (F : Type) [Field F]

/-- The code P is the unique inactive number, and all larger codes are rejected. -/
theorem valid_id_net {P h : ℕ} (hp : P < 2 ^ h) :
    Weight F (fun b : Unit ⊕ (Format.addr h).pins → Bool =>
      if ((Format.addr h).code.symm (b ∘ Sum.inr)).val ≤ P ∧
        b (.inl ()) = decide (((Format.addr h).code.symm (b ∘ Sum.inr)).val < P)
        then 1 else 0) ((100 + h) ^ 10) := by
  let A := Format.addr h
  let p : B h := ⟨P, hp⟩
  have hc : Circuit F A A (fun _ => p) (A.width + 16 * A.width) := by
    have hdep : Depends (fun _ : A.pins → Bool => A.code p) 0 :=
      fun _ => ⟨∅, by simp, fun _ _ _ => rfl⟩
    exact hdep.bnet F
  have hx := Circuit.id F A
  have ht := numeric_lt F h
  have data := (Circuit.id F .bit).par (((hc.pair hx).comp ht).pair ((hx.pair hc).comp ht))
  let test (t : Unit ⊕ (Unit ⊕ Unit) → Bool) : F :=
    if t (.inr (.inl ())) = false ∧ t (.inl ()) = t (.inr (.inr ())) then 1 else 0
  have hw := BNet.weight data (Weight.dense F _ test)
  convert hw.mono (n := (100 + h) ^ 10) ?_ using 1
  · funext b
    let n := ((Format.addr h).code.symm (b ∘ Sum.inr)).val
    change (if n ≤ P ∧ b (.inl ()) = decide (n < P) then (1 : F) else 0) =
      if decide (P < n) = false ∧ b (.inl ()) = decide (n < P) then 1 else 0
    simp
  · simp only [Fintype.card_sum, Fintype.card_unit, A, Format.width_addr]
    refine le_trans ?_ (Nat.pow_le_pow_right (by omega) (by decide : 3 ≤ 10))
    ring_nf
    have hbit := Format.width_bit
    omega

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end

/-! # Trivalent checks for ordered processor numbers and the vacant sentinel -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol

open Coloring Install
open scoped Classical

/-- An inactive factor contributes one regardless of its payload. -/
theorem gate {F I : Type} [Field F] [Fintype I] {f : (I → Bool) → F} {m : ℕ}
    (hf : Weight F f m) :
    Weight F (fun b : Unit ⊕ I → Bool => if b (.inl ()) then f (b ∘ Sum.inr) else 1)
      (Weight.switchCost 1 * (2 * Fintype.card I + m + 1)) := by
  let g (r : Unit → Bool) (x : I → Bool) := if r () then f x else 1
  have hg (r) : Weight F (g r) (Fintype.card I + m) := by
    by_cases h : r () = true
    · simpa [g, h] using hf.mono (Nat.le_add_left m (Fintype.card I))
    · have hc : Weight F (fun _ : I → Bool => 1) (Fintype.card I) := by
        intro a i
        rw [Fintype.card_congr i, MatrixExponent.card_slots]
        exact DNet.discard F a
      simpa [g, h] using hc.mono (Nat.le_add_right (Fintype.card I) m)
  simpa only [g, Function.comp_apply, Fintype.card_unit, two_mul, add_assoc] using
    Weight.switch g hg

variable (F : Type) [Field F]

private theorem cmp (h : ℕ) :
    Weight F (fun b : (Format.addr h).pins ⊕ (Format.addr h).pins → Bool =>
      if (Format.addr h).code.symm (b ∘ Sum.inr) ≤ (Format.addr h).code.symm (b ∘ Sum.inl)
        then 1 else 0) (1000 * (1 + h) + 16) := by
  have hc := BNet.weight (numeric_lt F h) (Weight.dense F Unit (fun x => if x () then 0 else 1))
  convert hc using 1 <;> try rfl
  funext b
  let a := (Format.addr h).code.symm (b ∘ Sum.inl)
  let z := (Format.addr h).code.symm (b ∘ Sum.inr)
  change (if z ≤ a then (1 : F) else 0) = if decide (a < z) then 0 else 1
  simp only [decide_eq_true_eq, ← not_le, ite_not]

private def prev {n : ℕ} (i : Fin n) : Fin n :=
  ⟨i.val - 1, (Nat.sub_le ..).trans_lt i.isLt⟩

private theorem mono_iff {n h : ℕ} (f : Fin n → B h) :
    Monotone f ↔ ∀ i, f (prev i) ≤ f i := by
  refine ⟨fun hm i => hm (Nat.sub_le ..), fun hm => ?_⟩
  cases n with
  | zero => exact fun i => Fin.elim0 i
  | succ n =>
    apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact hm i.succ

/-- Compare each slot to its predecessor inside the same bucket.
The first slot compares to itself, and empty buckets require no checks. -/
theorem order_net (P V k h : ℕ) :
    Weight F (fun b : Slot P V k × (Format.addr h).pins → Bool =>
      if ∀ j : Fin (k + 1), Monotone (fun i : Fin (seats P V j.val) =>
        (Format.addr h).code.symm (fun a => b (⟨j, i⟩, a))) then 1 else 0)
      ((k + 1) * P * (100 + h) ^ 10) := by
  let S := Slot P V k
  let A := Format.addr h
  let past (s : S) : S := ⟨s.1, prev s.2⟩
  let read (s : S) : A.pins ⊕ A.pins → (S × A.pins) ⊕ Empty :=
    Sum.elim (fun t => .inl (s, t)) (fun t => .inl (past s, t))
  let test (_ : S) (b : A.pins ⊕ A.pins → Bool) : F :=
    if A.code.symm (b ∘ Sum.inr) ≤ A.code.symm (b ∘ Sum.inl) then 1 else 0
  have hn := weight_sum test read (fun _ => 1000 * (1 + h) + 16) (fun _ => cmp F h)
  have hb : 8 * (Fintype.card (S × A.pins) + Fintype.card Empty) +
      36 * ∑ _ : S, (1000 * (1 + h) + 16) ≤ (k + 1) * P * (100 + h) ^ 10 := by
    have hh : 8 * h + 36 * (1000 * (1 + h) + 16) ≤ (100 + h) ^ 10 := by
      refine le_trans ?_ (Nat.pow_le_pow_right (by omega) (by decide : 4 ≤ 10))
      ring_nf
      omega
    simp only [Fintype.card_prod, Fintype.card_empty, add_zero, Finset.sum_const,
      Finset.card_univ, Nat.nsmul_eq_mul, show Fintype.card A.pins = h from Format.width_addr h]
    calc
      _ = Fintype.card S * (8 * h + 36 * (1000 * (1 + h) + 16)) := by ring
      _ ≤ _ := Nat.mul_le_mul (card_slots P V k) hh
  convert hn.mono hb using 1
  funext b
  let x (s : S) : B h := A.code.symm (fun a => b (s, a))
  have he : (∀ j : Fin (k + 1), Monotone (fun i => x ⟨j, i⟩)) ↔ ∀ s, x (past s) ≤ x s := by
    simp only [mono_iff]
    exact ⟨fun ht s => ht s.1 s.2, fun ht j i => ht ⟨j, i⟩⟩
  unfold weightedSum
  rw [Fintype.sum_unique]
  change (if ∀ j : Fin (k + 1), Monotone (fun i => x ⟨j, i⟩) then (1 : F) else 0) =
    ∏ s, if x (past s) ≤ x s then 1 else 0
  simp only [he]
  by_cases ha : ∀ s, x (past s) ≤ x s
  · simp [ha]
  · obtain ⟨s, hs⟩ := not_forall.mp ha
    rw [ite_eq_right ha]
    symm
    exact Finset.prod_eq_zero (Finset.mem_univ s) (ite_eq_right hs)

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end

/-! # Binary names for the entire gate dictionary -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol

open Finset
open scoped Classical

variable {F : Type} [Field F] [Fintype F] {a b : Wire}
  {u U m h C : ℕ} {W : List Bool → F} {k : Val a → Val b → F}

/-- Canonical port shapes let the same short dictionary name every
trivalent gate as well as the dyadic weight tables. Each name has
exactly the indicated number of binary positions. -/
theorem named_gates (hh : 1 ≤ h) (hU : U ≤ h) (hF : Fintype.card F ≤ h ^ C)
    (net : Wide F u (labels U W) a b k m) :
    let t := 5 + Nat.clog 2 h * (8 * C + 1)
    ∃ (G : Diagram F a b) (name : G.V → Fin (2 ^ t)) (dictionary : Fin (2 ^ t) → Table F),
      G.eval = k ∧ G.cost = m ∧ (∀ v, G.arity v ≤ u) ∧ ∀ v, dictionary (name v) = G.table v := by
  classical
  obtain ⟨G, hk, hG, hm⟩ := net.diagram
  let L := (range (RAM.ceiling U + 1)).image (label U W)
  have hL : labels U W ⊆ (↑L : Set (Table F)) := by
    rintro _ ⟨i, hi, rfl⟩
    exact mem_image_of_mem _ (mem_range.mpr (Nat.lt_succ_of_le (Set.mem_Iic.mp hi)))
  have admits : G.Admits u (↑L : Set (Table F)) := fun v =>
    ⟨(hG v).1, (hG v).2.imp id (fun hi => hL hi)⟩
  let B := univ.image G.canonical.table
  let t := 5 + Nat.clog 2 h * (8 * C + 1)
  have hb : (RAM.ceiling U) ≤ U + 1 :=
    Nat.clog_le_of_le_pow Nat.lt_two_pow_self.le
  have hLc : L.card ≤ 3 * h := by
    have hl : L.card ≤ RAM.ceiling U + 1 := card_image_le.trans_eq (card_range _)
    omega
  have hp : Fintype.card F ^ 8 ≤ h ^ (8 * C + 1) := calc
    _ ≤ (h ^ C) ^ 8 := Nat.pow_le_pow_left hF _
    _ = h ^ (C * 8) := (pow_mul ..).symm
    _ ≤ _ := Nat.pow_le_pow_right (by omega) (by omega)
  have hh₁ : h ≤ h ^ (8 * C + 1) := Nat.le_self_pow (by omega) _
  have size : B.card ≤ 2 ^ t := calc
    _ ≤ L.card + 16 * Fintype.card F ^ 8 := G.canonical_palette admits
    _ ≤ 3 * h ^ (8 * C + 1) + 16 * h ^ (8 * C + 1) :=
      Nat.add_le_add (hLc.trans (Nat.mul_le_mul_left _ hh₁)) (Nat.mul_le_mul_left _ hp)
    _ = 19 * h ^ (8 * C + 1) := by ring
    _ ≤ 2 ^ 5 * ((2 : ℕ) ^ (Nat.clog 2 h)) ^ (8 * C + 1) :=
      Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left (Nat.le_pow_clog (by decide) _) _)
    _ = _ := by unfold t; rw [pow_add 2 5, pow_mul 2 (Nat.clog 2 h)]
  obtain ⟨code⟩ := Function.Embedding.nonempty_of_card_le
    (α := ↑B) (β := Fin (2 ^ t)) (by simpa only [Fintype.card_coe, Fintype.card_fin] using size)
  let tableAt (v : G.canonical.V) : ↑B := ⟨G.canonical.table v, mem_image_of_mem _ (mem_univ _)⟩
  let name (v : G.canonical.V) := code (tableAt v)
  let dictionary (i : Fin (2 ^ t)) : Table F :=
    if p : ∃ x : ↑B, code x = i then (Classical.choose p).val
    else ⟨.unit, .unit, fun _ _ => 1⟩
  refine ⟨G.canonical, name, dictionary, G.eval_canonical.trans hk,
    G.cost_canonical.trans hm, fun v => (G.arity_canonical v).le.trans (hG v).1, ?_⟩
  intro v
  have p : ∃ x : ↑B, code x = name v := ⟨tableAt v, rfl⟩
  simp only [dictionary, dite_eq_left p]
  exact congrArg Subtype.val (code.injective (Classical.choose_spec p))

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end

/-! # Verifying one controller, including the inactive case -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol

open Coloring Install
open scoped Classical

variable {F X : Type} [Field F] {t U w : ℕ}

private abbrev Check (X : Type) (t U : ℕ) := Option (X ⊕ RAM.Calls t U)

private abbrev pins : Check X t U → Type
  | none => Bool
  | some (.inl _) => Bool
  | some (.inr s) => Option (RAM.token s.1.val).pins

private instance (d : Check X t U) : Fintype (pins d) := by
  rcases d with _ | (i | s) <;> unfold pins <;> infer_instance

private def data (W : List Bool → F) (mask : X → Bool) :
    (d : Check X t U) → (pins d → Bool) → F
  | none, y => if y false then if y true then 1 else 0 else 1
  | some (.inl i), y => if y false then 1 else if mask i = true → y true = false then 1 else 0
  | some (.inr s), y => enabledToken U W s.1.val y

private def cost : Check X t U → ℕ
  | none => 128
  | some (.inl _) => 128
  | some (.inr s) => 6 * capacity s

variable [Fintype X] (W : List Bool → F) (R : Controller X (Output t U) w)
  (j : ℕ) (on : X) (mask : X → Bool)

private def taps : (d : Check X t U) → pins d → RAM.Source X (R.time j)
  | none, b => if b then R.tap j (.inl ()) else .inl on
  | some (.inl i), b => if b then .inl i else .inl on
  | some (.inr _), none => .inl on
  | some (.inr s), some k => R.tap j (.inr ⟨s, k⟩)

private theorem product_eq :
    (R.program j).products (data W mask) (taps R j on) = activeValue W (R.value j) on mask := by
  funext x
  have read (i : X) : (R.program j).eval x (.inl i) = x i := rfl
  unfold RAM.Program.products activeValue
  rw [Fintype.prod_option, Fintype.prod_sum_type]
  simp only [data, taps, enabledToken, Function.comp_def, Bool.false_eq_true,
    ite_false, ite_true, read, Controller.correct]
  by_cases h : x on = true
  · simp [h, localValue, ite_mul]
  · simp only [h, Bool.false_eq_true, ite_false, one_mul, Finset.prod_const_one, mul_one]
    by_cases hmask : ∀ i, mask i = true → x i = false
    · rw [ite_eq_left hmask]
      exact Finset.prod_eq_one fun i _ => ite_eq_left (hmask i)
    · rw [ite_eq_right hmask]
      obtain ⟨i, hi⟩ := not_forall.mp hmask
      exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

private theorem program_net :
    WideWeight F (10 * (U + 1)) (labels U W) (activeValue W (R.value j) on mask)
      (9 * (129 * Fintype.card X + RAM.Program.expense (R.time j) w 4 + 128 + 12 * (RAM.ceiling U + 1) * t)) := by
  have hu : 3 ≤ 10 * (U + 1) := by omega
  have hc (d : Check X t U) : WideWeight F (10 * (U + 1)) (labels U W) (data W mask d) (cost d) := by
    rcases d with _ | (i | s)
    · exact of_weight hu (Weight.dense F Bool _)
    · exact of_weight hu (Weight.dense F Bool _)
    · exact label_cost U W (Nat.lt_succ_iff.mp s.1.isLt)
  have hn := (R.program j).build (data W mask) (taps R j on) hu cost hc
  rw [product_eq, Fintype.sum_option, Fintype.sum_sum_type] at hn
  intro a e
  obtain ⟨n, h, he⟩ := hn a e
  refine ⟨n, h.trans ?_, he⟩
  simp only [cost, Finset.sum_const, Finset.card_univ, Nat.nsmul_eq_mul, ← Finset.mul_sum]
  have hb := sum_capacity t t (RAM.ceiling U)
  linarith only [hb]

/-- The two logarithms allow repeated input and output addresses. -/
private theorem expense_bound (i o j g w : ℕ) :
    RAM.Program.expense (clock i o j g) w 4 ≤
      (i + 2 ^ j + o) * (100 + j + w + g + Nat.clog 2 (i + 1) + Nat.clog 2 (o + 1)) ^ 210 := by
  let a := w + Nat.clog 2 (i + 1) + Nat.clog 2 (o + 1)
  have port (x : ℕ) (hx : Nat.clog 2 (x + 1) ≤ a) : x ≤ 2 ^ a :=
    (Nat.le_succ x).trans ((Nat.le_pow_clog (by decide) (x + 1)).trans
      (Nat.pow_le_pow_right (by decide) hx))
  calc
    _ ≤ RAM.Program.expense (clock i o j g) a 4 := by
      unfold RAM.Program.expense
      gcongr
      unfold a; omega
    _ ≤ (i + 2 ^ j + o) * (100 + a + j + g) ^ 210 := clock_expense _ _ _ _ _
      (port i (by unfold a; omega)) (port o (by unfold a; omega))
    _ = _ := by rw [show 100 + a + j + g = 100 + j + w + g + Nat.clog 2 (i + 1) + Nat.clog 2 (o + 1) by unfold a; omega]

private theorem total_bound (i o h c e K : ℕ) (hK : 100 ≤ K) (ho : o ≤ 1 + 8 * c)
    (he : e ≤ (i + h + o) * K ^ 210) :
    9 * (129 * i + e + 128 + 12 * c) ≤ (1 + i + h + c) * K ^ 212 := by
  let V := 1 + i + h + c
  have h₁ : e ≤ 8 * (V * K ^ 210) := calc
    _ ≤ (i + h + o) * K ^ 210 := he
    _ ≤ (8 * V) * K ^ 210 := Nat.mul_le_mul_right _ (by unfold V; omega)
    _ = _ := by rw [mul_assoc]
  have h₂ : V ≤ V * K ^ 210 := Nat.le_mul_of_pos_right V (pow_pos (by omega) _)
  have h₃ : 9 * (129 * i + e + 128 + 12 * c) ≤ 1233 * (V * K ^ 210) := by
    have hv : 129 * i + 128 + 12 * c ≤ 129 * V := by unfold V; omega
    omega
  have h₄ : 1233 ≤ K ^ 2 := (show 1233 ≤ 100 ^ 2 by decide).trans (Nat.pow_le_pow_left hK _)
  calc
    _ ≤ 1233 * (V * K ^ 210) := h₃
    _ ≤ K ^ 2 * (V * K ^ 210) := Nat.mul_le_mul_right _ h₄
    _ = _ := by rw [mul_left_comm, ← pow_add]

/-- One common dictionary serves every processor, charge and mask. Even
when inactive, the bit-RAM has a unique execution on the given input. -/
theorem active_net :
    WideWeight F (10 * (U + 1)) (labels U W) (activeValue W (R.value j) on mask)
      ((1 + Fintype.card X + 2 ^ j + (RAM.ceiling U + 1) * t) *
        (100 + j + w + R.size + Nat.clog 2 (Fintype.card X + 1) + Nat.clog 2 (Fintype.card (Output t U) + 1)) ^ 212) := by
  intro a e
  obtain ⟨v, h, hv⟩ := program_net W R j on mask a e
  refine ⟨v, h.trans ?_, hv⟩
  rw [mul_assoc 12]
  exact total_bound _ (Fintype.card (Output t U)) _ _ _ _ (by omega)
    (by rw [← mul_assoc]; exact card_output _ _) (expense_bound _ _ _ _ _)

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end

/-! # Circuit bounds for all factors on the physical tape -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.System

open Coloring
open scoped Classical

variable {X K : Type} [Field K] {k H U V h C r : ℕ} {S : Spec X k H} (D : System S U)

def fee (h C r : ℕ) : S.Factor V → ℕ
  | .inl g => 4 * (r * (S.pool V g + 1) * ((S.supply g).width + h ^ C))
  | .inr (.inl _) => 4 * (100 + H) ^ 10
  | .inr (.inr (.inl g)) => 4 * ((k + 1) * S.P g * (100 + H) ^ 10)
  | .inr (.inr (.inr (.inl _))) => 4 * Channels.cost S.key S.body (S.Reserved V) h C r
  | .inr (.inr (.inr (.inr i))) => D.slotCost i.1 i.2.1

theorem fee_net (W : List Bool → K) (p : Prices K h C r)
    (hk : S.key.width ≤ h ^ 2) (hi : H ≤ h ^ 2) (hm : ∀ g, S.pool V g ≤ 2 ^ (h ^ 3))
    (hn : Fintype.card (Σ l, S.Reserved V l) ≤ 2 ^ (h ^ 3)) (i : S.Factor V) :
    WideWeight K (10 * (U + 1)) (labels U W) (D.check W i) (D.fee h C r i) := by
  have hu : 3 ≤ 10 * (U + 1) := by omega
  rcases i with g|i|g|u|i
  · obtain ⟨j, n, m, hj, hw, ht, hb⟩ := p H (S.pool V g) (S.supply g).width hi (hm g)
    have pc := Private.weight (S := Slot (S.P g) V k) (S.supply g) (S.named g) hj hw ht
    apply of_weight hu (pc.mono ?_)
    refine le_trans ?_ hb
    gcongr
    decide
  · exact of_weight hu (valid_id_net K (S.named i.1))
  · exact of_weight hu (order_net K (S.P g) V k H)
  · exact of_weight hu (Channels.weight S.key S.body (S.Reserved V) p hk hn)
  · exact active_net W (D.verify i.1 i.2.1) i.2.1.val (S.on i.1 i.2.1) (S.mask i.1 i.2.1)

theorem sum_fee (V h C r : ℕ) [Fintype X] :
    100 * (1 + Fintype.card X + Fintype.card (S.Hidden V)+∑ i : S.Factor V, D.fee h C r i) ≤
      D.cost V h C r := by
  have ho : (∑ g, 4 * ((k + 1) * S.P g * (100 + H) ^ 10)) = 4 * ((k + 1) * S.size * (100 + H) ^ 10) := by
    rw [← Finset.mul_sum, ← Finset.sum_mul, ← Finset.mul_sum]
  have hi : Fintype.card (S.Site V) * (4 * (100 + H) ^ 10) ≤ 4 * ((k + 1) * S.size * (100 + H) ^ 10) := calc
    _ ≤ ((k + 1) * S.size) * (4 * (100 + H) ^ 10) := Nat.mul_le_mul_right _ (S.site_count V)
    _ = _ := by ring
  rw [Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type, Fintype.sum_sum_type]
  simp only [fee, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.cast_id, Fintype.card_unit, one_mul]
  rw [ho, ← Finset.mul_sum]
  unfold cost
  omega

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.System
end

/-! # Summing the physical transcript on a fixed set of hidden bits -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.System
open Coloring
open scoped Classical

variable {X K : Type} [Field K] {k H U V : ℕ} (S : Spec X k H)

private def layout : (S.Hidden V → Bool) ≃ S.Tape V where
  toFun y g i t := y ⟨⟨g, i⟩, t⟩
  invFun b p := b p.1.1 p.1.2 p.2
  left_inv _ := rfl
  right_inv _ := rfl

private def read : (i : S.Factor V) → S.pins i → (X ⊕ Bool) ⊕ S.Hidden V
  | .inl g, .inl (p, t) => .inl (S.privateBits g p t)
  | .inl g, .inr (i, t) => .inr ⟨⟨g, i⟩, .inl t⟩
  | .inr (.inl i), .inl a => .inr ⟨i, .inl (.inl a)⟩
  | .inr (.inl i), .inr t => .inr ⟨i, .inl (.inr (.inl t))⟩
  | .inr (.inr (.inl g)), (i, t) => .inr ⟨⟨g, i⟩, .inl (.inr (.inl t))⟩
  | .inr (.inr (.inr (.inl _))), ⟨l, ⟨i, v⟩, t⟩ => .inr ⟨i, .inr (.inr ⟨l, v, t⟩)⟩
  | .inr (.inr (.inr (.inr i))), t => .inr ⟨i, t⟩

variable {S} (D : System S U) (W : List Bool → K)

private theorem indicator {I : Type} [Fintype I] (q : I → Prop) [DecidablePred q] :
    (∏ i, if q i then (1 : K) else 0) = if ∀ i, q i then 1 else 0 := by
  by_cases h : ∀ i, q i
  · simp [h]
  · obtain ⟨i, hi⟩ := not_forall.mp h
    rw [ite_eq_right h]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right hi)

private theorem check_prod (x : X → Bool) (y : S.Hidden V → Bool) :
    (∏ i, D.check W i (Sum.elim (Sum.elim x id) y ∘ read S i)) =
      D.physical W x (layout S y) := by
  let b := layout S y
  let p (g : Level k) := Private.good (S.data x g) (fun i => S.badge (b g i))
  let n (i : S.Site V) := (S.badge (b i.1 i.2)).2.1.val ≤ S.P i.1 ∧
    (S.badge (b i.1 i.2)).1 = decide ((S.badge (b i.1 i.2)).2.1.val < S.P i.1)
  let o (g : Level k) := ∀ j, Monotone (fun i => (S.badge (b g ⟨j, i⟩)).2.1)
  have pub : S.Public x b ↔ (∀ g, p g) ∧ (∀ i, n i) ∧ (∀ g, o g) ∧ Channels.good (S.issued b) :=
    ⟨fun h => ⟨h.privateMatch, fun i => h.ids i.1 i.2, h.sorted, h.messages⟩,
      fun h => ⟨h.1, fun g i => h.2.1 ⟨g, i⟩, h.2.2.1, h.2.2.2⟩⟩
  rw [Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type, Fintype.prod_sum_type]
  simp only [Fintype.prod_unique]
  change (∏ g, if p g then (1 : K) else 0) * ((∏ i, if n i then 1 else 0) *
    ((∏ g, if o g then 1 else 0) * ((if Channels.good (S.issued b) then 1 else 0) *
      ∏ i : S.Site V, D.actor W i.1 i.2.1 (b i.1 i.2)))) = D.physical W x b
  rw [indicator, indicator, indicator, Fintype.prod_sigma]
  simp only [physical, pub, ite_and, ite_mul, zero_mul, one_mul]

/-- Fixed literal reads and a bijective layout of the hidden tape realize the
sum with one assignment for each physical tape. -/
theorem physical_net [Fintype X] {h C r : ℕ} (p : Prices K h C r)
    (hk : S.key.width ≤ h ^ 2) (hi : H ≤ h ^ 2)
    (hm : ∀ g, S.pool V g ≤ 2 ^ (h ^ 3)) (hn : Fintype.card (Σ l, S.Reserved V l) ≤ 2 ^ (h ^ 3)) :
    WideWeight K (10 * (U + 1)) (labels U W) (fun x => ∑ b : S.Tape V, D.physical W x b)
      (D.cost V h C r) := by
  have net := sum_net (D.check W) (read S) (D.fee h C r) (by omega)
    (D.fee_net W p hk hi hm hn)
  -- Use the same enumeration of assignments as the abstract hidden type in sum_net.
  let : DecidableEq (S.Hidden V) := fun a b => Classical.propDecidable (a = b)
  have eq (x : X → Bool) :
      (∑ y : S.Hidden V → Bool, ∏ i, D.check W i (Sum.elim (Sum.elim x id) y ∘ read S i)) =
        ∑ b : S.Tape V, D.physical W x b :=
    Fintype.sum_equiv (layout S) _ _ (check_prod D W x)
  simp only [eq] at net
  intro a i
  obtain ⟨v, hv, n⟩ := net a i
  exact ⟨v, hv.trans (D.sum_fee V h C r), n⟩

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.System
end
