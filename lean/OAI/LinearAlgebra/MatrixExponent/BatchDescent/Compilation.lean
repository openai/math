import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Transform
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dictionary
import OAI.LinearAlgebra.MatrixExponent.Diagram.Replacement
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Encoded
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior.Strips
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior.Fields
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Sweep
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Encoding
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore.Elect
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Restore.Rule

/-!
# Batching all small labels in a network

Read the exceptional tables from one dictionary on the diagram tape.
All other stations keep their original labels. This works for loops,
repeated wires and zero-valued tables in arbitrary characteristic.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Finset Transcript Install Classical Processor Label

variable {F V : Type} [Field F] [Fintype V] {a b c : Wire} {w u s : ℕ}

/-- On a fixed transcript, replace the exceptional factors by a single
factor that reads the whole tape. -/
private theorem batch_tape (hw : 64 ≤ w) (L : Finset (Table F))
    (hL : L.card ≤ 2 ^ (w / 4)) (ht : ∀ T ∈ L, arity T ≤ w / 4)
    (T : V → Table F) (hs : ∑ v, (1 + arity (T v)) ≤ s) (hs' : s ≤ 2 ^ (2 * w - 1))
    (hu : 3 ≤ u) (ha : 2 * 2 ^ (2 * w) * (4 * w) ≤ u)
    (hvalid : ∀ v, T v ∉ L → arity (T v) ≤ u ∧ (arity (T v) ≤ 3 ∨ T v ∈ Allowed F w))
    (r : ∀ v, slots (args (T v)) → slots (.pair (.pair a b) c))
    (htape : wd a + wd b + wd c ≤ s) :
    ∃ n, Wide F u (Allowed F w) a b
      (value (fun v => args (T v)) (fun v => applyTable (T v)) r) n ∧ n ≤ 10 ^ 8 * (s + w * 2 ^ w) := by
  let d := Wire.pair (.pair a b) c
  let J := Option {v // T v ∉ L}
  let A : J → Wire := fun i => i.elim d fun v => args (T v)
  let f (x : Val d) (v : V) := applyTable (T v) (project (r v) x)
  let k : (i : J) → Val (A i) → F
    | none, x => ∏ v : {v // T v ∈ L}, f x v
    | some v, x => applyTable (T v) x
  let read : (i : J) → slots (A i) → slots d
    | none => id
    | some v => r v
  let N := 4 * s + 440000 * (s + w * 2 ^ w)
  let cost : J → ℕ := fun i => i.elim N fun v => 9 * (1 + arity (T v))
  have ready (i : J) : ∃ t ≤ cost i, Wide F u (Allowed F w) (A i) .unit (fun x _ => k i x) t := by
    cases i with
    | some v => exact bend hu _ (hvalid v v.property).1 (hvalid v v.property).2
    | none =>
      obtain ⟨n, hn, hk⟩ := tape T L hw hu ha hL ht hs hs' r d (Equiv.refl _)
      rw [card_slots] at hn
      exact ⟨n, hn.trans (Nat.add_le_add_right (Nat.mul_le_mul_left 4 htape) _),
        hk.mono le_rfl sort_allowed⟩
  obtain ⟨n, hn, h⟩ := wide A k cost read hu ready
  refine ⟨n, ?_, ?_⟩
  · convert h using 1
    funext x y
    apply sum_congr rfl
    intro z _
    rw [Fintype.prod_option]
    have hp : project (a := d) id ((x, y), z) = ((x, y), z) := (bits d).symm_apply_apply _
    change (∏ v, f ((x, y), z) v) =
      (∏ v : {v // T v ∈ L}, f (project id ((x, y), z)) v) * ∏ v : {v // T v ∉ L}, f ((x, y), z) v
    rw [hp]
    exact (Fintype.prod_subtype_mul_prod_subtype (fun v => T v ∈ L) _).symm
  · have hc := Fintype.sum_subtype_add_sum_subtype (fun v => T v ∈ L) (fun v => 1 + arity (T v))
    have hc' : (∑ v : {v // T v ∉ L}, (1 + arity (T v))) ≤ s := (Nat.le_add_left _ _).trans (hc.le.trans hs)
    rw [Fintype.sum_option] at hn
    change n ≤ 8 * (wd a + wd b + wd c) + 9 * (N + ∑ v : {v // T v ∉ L}, 9 * (1 + arity (T v))) at hn
    rw [← mul_sum] at hn
    unfold N at hn
    omega

theorem batch_labels {k : Val a → Val b → F}
    (hw : 64 ≤ w) (L : Finset (Table F)) (hL : L.card ≤ 2 ^ (w / 4)) (ht : ∀ T ∈ L, arity T ≤ w / 4)
    (h : Wide F u (Allowed F w ∪ (L : Set (Table F))) a b k s) (hs : s ≤ 2 ^ (2 * w - 1)) :
    ∃ v n, Wide F v (Allowed F w) a b k n ∧ n ≤ 10 ^ 8 * (s + w * 2 ^ w) := by
  obtain ⟨G, rfl, hG, hcost⟩ := h.diagram
  let v := max (max u 3) (2 * 2 ^ (2 * w) * (4 * w))
  let c := word (Fintype.card G.E)
  let e : G.E ≃ slots (word (Fintype.card G.E)) := Fintype.equivOfCardEq (by simp)
  let read (i : G.V) : slots (args (G.table i)) → slots (.pair (.pair a b) c) := Sum.elim
    (fun j => Sum.elim (fun t => .inl (.inl t)) (fun t => .inr (e t)) (G.src ⟨i, j⟩))
    (fun j => Sum.elim (fun t => .inl (.inr t)) (fun t => .inr (e t)) (G.dst ⟨i, j⟩))
  have hvalid (i : G.V) (hi : G.table i ∉ L) :
      arity (G.table i) ≤ v ∧ (arity (G.table i) ≤ 3 ∨ G.table i ∈ Allowed F w) :=
    ⟨(hG i).1.trans (by unfold v; omega), (hG i).2.imp_right (fun t => t.resolve_right hi)⟩
  have hsize : wd a + wd b + wd c ≤ s := by
    rw [← hcost, Diagram.cost_eq, show wd c = Fintype.card G.E from wd_word _]
    omega
  obtain ⟨n, hn, hb⟩ := batch_tape (u := v) hw L hL ht G.table hcost.le hs (by unfold v; omega)
    (le_max_right _ _) hvalid read hsize
  refine ⟨v, n, ?_, hb⟩
  convert hn using 1
  funext x y
  let f := (bits c).trans (e.symm.arrowCongr (Equiv.refl Bool))
  symm
  unfold value Diagram.eval
  refine @Fintype.sum_equiv (Val c) (G.E → Bool) F (valFintype c) _ _ f _ _ ?_
  intro z
  apply prod_congr rfl
  intro i _
  apply congrArg₂ (G.table i).2.2
  · apply congrArg (bits (G.table i).1).symm
    funext j
    change bits (.pair (.pair a b) c) ((x, y), z) (read i (.inl j)) = _
    unfold read
    cases he : G.src ⟨i, j⟩ <;> simp only [Sum.elim_inl, he, Sum.elim_inr] <;> rfl
  · apply congrArg (bits (G.table i).2.1).symm
    funext j
    change bits (.pair (.pair a b) c) ((x, y), z) (read i (.inr j)) = _
    unfold read
    cases he : G.dst ⟨i, j⟩ <;> simp only [Sum.elim_inr, he, Sum.elim_inl] <;> rfl

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

section
/-!
# Extra block reserve

The upper bounds on the work per host may be polynomial in the
address width. Keep an extra quadratic number of block-index bits
throughout the beats, then move them to the host coordinate before
applying the terminal packing. This leaves the replication subpolynomial.
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Recipe
open Filter

variable {F : Type} [Field F] (P : Recipe F)

theorem reserve_height (R J : ℕ) : P.blocks (R + J) J = P.blocks R J + J ^ 2 := by
  unfold blocks
  ring

theorem reserve_width (R J : ℕ) :
    P.blocks (R + J) J ≤ (R + 1 + P.n * (P.H + 5)) * J ^ 2 := by
  unfold blocks group
  have := Nat.mul_le_mul_left R (show J ≤ J ^ 2 by nlinarith)
  nlinarith only [this]

theorem reserve_parameters (R Q V B J : ℕ) (hB : 5 + Q + P.b + V ≤ B)
    {κ : ℝ} (hk : 0 < κ) :
    ∀ᶠ w : ℕ in atTop, ∃ j z : ℕ, J ≤ j ∧ 1 ≤ j ∧ 2 ^ (B * j) ≤ w ∧ w ≤ 2 ^ (2 * B * j) ∧
      0 < z ∧ 2 ^ (V * j) ∣ z ∧ 16 * (2 ^ (Q * j) * P.b ^ j) * z ≤ w ∧ w ≤ 32 * (2 ^ (Q * j) * P.b ^ j) * z ∧
      0 < P.batch (R + j) j z ∧ (P.batch (R + j) j z : ℝ) ≤ ((2 : ℝ) ^ w : ℝ) ^ κ := by
  obtain ⟨N, hN⟩ := eventually_atTop.mp (replication (half_pos hk) 1)
  filter_upwards [P.parameters R Q V B (max J N) hB (half_pos hk)] with w hw
  obtain ⟨j, z, hj, hj', hl, hu, hz, hv, hn, he, hs, hp⟩ := hw
  have hh : 2 ^ j ≤ w := (Nat.pow_le_pow_right (by decide)
    (Nat.le_mul_of_pos_left _ (by omega : 0 < B))).trans hl
  have ht := hN j (by omega) w hh
  have hsize : P.batch (R + j) j z = 2 ^ (j ^ 2) * P.batch R j z := by
    unfold batch
    rw [P.reserve_height, pow_add]
    ring
  refine ⟨j, z, by omega, hj', hl, hu, hz, hv, hn, he, ?_, ?_⟩
  · rw [hsize]; positivity
  · rw [hsize, Nat.cast_mul, Nat.cast_pow, Nat.cast_ofNat]
    rw [one_mul] at ht
    refine (mul_le_mul ht hp (by positivity) (by positivity)).trans_eq ?_
    rw [← Real.rpow_add (by positivity), add_halves]

theorem reserve_limits (R Q B : ℕ) (hB : 6 + Q ≤ B) :
    ∀ᶠ j : ℕ in atTop, ∀ z w : ℕ, 2 ^ (B * j) ≤ w → w ≤ 2 ^ (2 * B * j) →
      16 * (2 ^ (Q * j) * P.b ^ j) * z ≤ w → w ≤ 32 * (2 ^ (Q * j) * P.b ^ j) * z →
      let h := P.blocks (R + j) j
      let p := P.b ^ j * z
      h + 4 ≤ p ∧ 2 * 2 ^ (h + 2) * (h + 1 + p + 2) ≤ min (2 ^ ((Nat.clog 2 w) ^ 3)) (2 ^ (w / 2)) := by
  filter_upwards [eventually_ge_atTop 1, Exterior.limits (R + 1 + P.n * (P.H + 5)) B]
    with j hj ht z w hl hu hlo hup
  apply ht _ _ w (P.reserve_width R j) _ _ hu
  · have hd : 32 * 2 ^ (Q * j) * 2 ^ j ≤ 32 * 2 ^ (Q * j) * (P.b ^ j * z) := calc
      _ = 2 ^ (5 + Q * j + j) := by simp [pow_add]
      _ ≤ 2 ^ (B * j) := Nat.pow_le_pow_right (by decide) (by nlinarith)
      _ ≤ w := hl
      _ ≤ _ := by simpa [mul_assoc] using hup
    exact Nat.le_of_mul_le_mul_left hd (by positivity)
  · exact (Nat.le_mul_of_pos_left _ (by positivity : 0 < 16 * 2 ^ (Q * j))).trans
      (by simpa [mul_assoc] using hlo)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Recipe
end

/-!
# Completing a controlled descent

Each supported state uniquely determines its whole decision tape.
The same terminal tensor closes every such state, including different
states sharing the same code.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Coloring Assembly Transcript PackRows Classical

variable {F Z : Type} [Field F] [Fintype Z] {D : Dimensions} {S : Scheme F}
  {x y : Wire} {w j cap u v : ℕ} {A : Format}

omit [Field F] in
private theorem decisions_width (h : D.FitsControls S Z w j cap u v) :
    Fintype.card (D.Decisions S) ≤ 10 * 2 ^ j * (1 + w) := by
  have hb : Fintype.card (D.BinOutput S) ≤ 2 * w := by
    have := h.short
    have := h.upper
    omega
  have hc : D.a + 2 + D.e ≤ 8 * w := by have := h.head; have := h.names; omega
  have hd : D.K * (2 * D.v) ≤ 2 ^ j := (Nat.le_add_left _ _).trans h.slots
  have hK : D.K ≤ 2 ^ j := (Nat.le_mul_of_pos_right _ (by positivity)).trans hd
  change Fintype.card ((Fin D.K × D.BinOutput S) ⊕
    (D.Addr × (slots (word (D.a + 2)) ⊕ Fin D.e))) ≤ _
  rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin,
    show Fintype.card (D.Addr × (slots (word (D.a + 2)) ⊕ Fin D.e)) =
      (D.K * (2 * D.v)) * (D.a + 2 + D.e) by simp; omega]
  exact (Nat.add_le_add (Nat.mul_le_mul hK hb) (Nat.mul_le_mul hd hc)).trans (by ring_nf; omega)

namespace View
variable (V : View D S x y A Z)

private theorem controls (h : D.FitsControls S Z w j cap u v) :
    ∃ f : ((form A D x y).pins ⊕ D.Decisions S → Bool) → F,
      WideWeight F cap (Allowed F w) f
        (10 ^ 16 * (Fintype.card ((form A D x y).pins ⊕ D.Decisions S) + 2 ^ j * (1 + w))) ∧
      ∀ (G : Diagram F x y) (t : Assignment D S G) (ht : t.Fits) (a : (form A D x y).obj),
        V.Valid t ht a.1 → ∀ z, f (Sum.elim ((form A D x y).code a) z) =
          if V.display t ht h.code a.1 = z then 1 else 0 := by
  let lift : A.pins ⊕ Bool → ((form A D x y).pins ⊕ D.Decisions S) ⊕ Bool :=
    Sum.map (fun i => .inl (.inl i)) id
  let dst : D.Decisions S → ((form A D x y).pins ⊕ D.Decisions S) ⊕ Bool := fun i => .inl (.inr i)
  obtain ⟨f, hf, he⟩ := D.controls_net S h (lift ∘ V.rows)
    (fun i j => lift ∘ V.long i j) (fun i => lift ∘ V.short i) dst V.code V.user
  refine ⟨f, fun a i => ?_, fun G t ht a ha z => ?_⟩
  · obtain ⟨n, hn, hnet⟩ := hf a i
    exact ⟨n, hn, hnet.mono le_rfl sort_allowed⟩
  · let x' := Sum.elim ((form A D x y).code a) z
    have taps {Y : Type} (g : Y → A.pins ⊕ Bool) :
        Sum.elim x' id ∘ lift ∘ g = Sum.elim (A.code a.1) id ∘ g := by
      funext b
      simp only [Function.comp_apply]
      cases g b <;> rfl
    have eq := he x' t.inventory ht.position ht.reserve (fun i => by
      rw [taps]; exact V.lengths t ht ha i)
    simp only [taps, ← ha.rows, Equiv.symm_apply_apply] at eq
    refine eq.trans ?_
    congr 1
    exact propext eq_comm

theorem evaluate (hc : D.FitsControls S Z w j cap u v) (hr : D.FitsScreen S x y w j cap) :
    ∃ f : ((form A D x y).pins → Bool) → F,
      WideWeight F cap (Allowed F w) f (10 ^ 20 * ((form A D x y).width + 2 ^ j * (1 + w))) ∧
      ∀ (G : Diagram F x y) (t : Assignment D S G) (ht : t.Fits) (a : (form A D x y).obj),
        V.Valid t ht a.1 → f ((form A D x y).code a) = t.state.diagram.eval a.2.1 a.2.2 := by
  obtain ⟨k, hk, ek⟩ := V.controls hc
  obtain ⟨f, hf, ef⟩ := V.screen.run hr
  obtain ⟨g, hg, eg⟩ := hide_unique hc.gates hk hf
  refine ⟨g, fun a i => ?_, fun G t ht a ha => ?_⟩
  · obtain ⟨n, hn, hn'⟩ := hg a i
    refine ⟨n, ?_, hn'⟩
    have ht := decisions_width hc
    rw [mul_assoc] at ht
    rw [show Fintype.card ((form A D x y).pins ⊕ D.Decisions S) =
      Fintype.card (form A D x y).pins + Fintype.card (D.Decisions S) from Fintype.card_sum] at hn
    unfold Format.width
    omega
  · rw [eg _ _ (ek G t ht a ha), ef _ _ _ _ (V.flags t ht hc.code a ha), V.supplied]
    exact t.post.toPresentation.eval ..

end View

universe v

theorem terminal (X : Snapshot.{v} F (copies x D.copies) (copies y D.copies)) (V : View D S x y X.port Z)
    (hc : D.FitsControls S Z w j cap u v) (hr : D.FitsScreen S x y w j cap)
    (hs : ∀ i a b, ∃ (G : Diagram F x y) (t : Assignment D S G) (hw : t.Fits),
      X.eval i a b = t.state.diagram.eval a b ∧ V.Valid t hw (X.encode i a b)) :
    Finishes F cap (Allowed F w) X.public (10 ^ 20 * (X.public.port.width + 2 ^ j * (1 + w))) := by
  obtain ⟨f, hf, he⟩ := V.evaluate hc hr
  refine ⟨fun a => f (X.public.port.code a), ?_, fun i a b => ?_⟩
  · intro a b i j
    obtain ⟨m, hm, H⟩ := hf a i
    refine ⟨m, hm, ?_⟩
    have H' := H.post (rewire_reindex (a := b) (b := .unit) j)
    simp only [view_apply, Equiv.apply_symm_apply]
    exact H'
  · obtain ⟨G, t, hw, hv, hk⟩ := hs i a b
    exact (he G t hw (X.encode i a b, a, b) hk).trans hv.symm

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

section
/-!
# Sizing the terminal checks

Use 32 slices per half-bin row to carry long names. These slices
are independent of the whole apparent bit size of a local table.
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dimensions
open Assembly Coloring PackRows

variable {F Z : Type} [Fintype Z] (D : Dimensions) (S : Scheme F)

def shortWidth (c : ℕ) : ℕ :=
  D.v * (1 + c) + (4 * D.v * D.u) ^ 2 +
    2 * D.v * (2 ^ S.h * (1 + S.ℓ + 2 * D.u ^ 2) + 2 * D.v + (D.r + 2) + 1 + D.q * (1 + D.h))

theorem controls_card : Fintype.card (BinKey D.v Z) + Fintype.card (D.BinOutput S) =
    D.shortWidth S (Fintype.card Z) := by
  simp only [shortWidth, Fintype.card_prod, Fintype.card_sum, Fintype.card_option, Fintype.card_fin,
    Fintype.card_unit, card_slots, wd_word]
  ring

theorem shortWidth_le {c t : ℕ} (hc : c ≤ t) (hb : 2 ^ S.h ≤ t) (he : S.ℓ ≤ t)
    (hr : D.r ≤ t) (hh : D.h ≤ t) (hq : D.q ≤ t) (hu : D.u ≤ t) (hv : D.v ≤ t) :
    8 * D.shortWidth S c ≤ (100 + t) ^ 8 := by
  unfold shortWidth
  calc
    _ ≤ 8 * (t * (1 + t) + (4 * t * t) ^ 2 + 2 * t * (t * (1 + t + 2 * t ^ 2) + 2 * t + (t + 2) + 1 + t * (1 + t))) := by gcongr
    _ ≤ _ := by ring_nf; omega

private theorem short_bounds (c : ℕ) :
    let k := D.shortWidth S c
    c ≤ k ∧ D.r ≤ k ∧ 4 * D.v ≤ k ∧ (2 * D.v) ^ 2 ≤ k ∧ (4 * D.v * D.u) ^ 2 ≤ k ∧
      2 ^ S.h * (1 + S.ℓ + 2 * D.u ^ 2) ≤ k := by
  let a := 2 ^ S.h * (1 + S.ℓ + 2 * D.u ^ 2)
  let b := a + 2 * D.v + (D.r + 2) + 1 + D.q * (1 + D.h)
  have hv := Nat.two_pow_pos D.r
  have h : b ≤ 2 * D.v * b := Nat.le_mul_of_pos_left _ (by positivity)
  have he : c ≤ D.v * (1 + c) := (Nat.le_add_left ..).trans (Nat.le_mul_of_pos_left _ hv)
  have hu := Nat.le_mul_of_pos_right (4 * D.v) D.upos
  have hp : (2 * D.v) ^ 2 ≤ (4 * D.v * D.u) ^ 2 := Nat.pow_le_pow_left (by omega) _
  have hq : 4 * D.v ≤ (2 * D.v) ^ 2 := by nlinarith only [show 0 < D.v from hv]
  change let k := D.v * (1 + c) + (4 * D.v * D.u) ^ 2 + 2 * D.v * b
    c ≤ k ∧ D.r ≤ k ∧ 4 * D.v ≤ k ∧ (2 * D.v) ^ 2 ≤ k ∧ (4 * D.v * D.u) ^ 2 ≤ k ∧ a ≤ k
  have : a ≤ b ∧ D.r ≤ b := by unfold b; omega
  dsimp only
  omega

def rows (x y : Wire) := 2 ^ S.m * D.PortCount S + 32 * D.K * D.v + (wd x + wd y) * D.n

theorem room {x y : Wire} {w j cap : ℕ} (hw : 64 ≤ w)
    (hj : w ≤ j) (hj' : 4 * j ≤ 5 * w) (hm : 4 * S.m ≤ 5 * w)
    (he : D.e = 2 * w) (ha : D.a = 3 * w)
    (hh : 8 * D.shortWidth S (Fintype.card Z) ≤ w)
    (ht : 16 * (D.q * D.b) * D.z ≤ w) (hext : D.h + 4 ≤ D.b * D.z)
    (hrows : D.rows S x y ≤ 2 ^ j) (hu : 2 * 2 ^ (2 * w) * (4 * w) ≤ cap)
    (hsmall : 2 * 2 ^ (D.h + 2) * (D.h + 1 + D.b * D.z + 2) ≤ min (2 ^ ((Nat.clog 2 w) ^ 3)) (2 ^ (w / 2))) :
    FitsControls D S Z w j cap (32 * D.v) (w / (8 * D.v) + 1) ∧ FitsScreen D S x y w j cap := by
  obtain ⟨hz, hr, hv, hv', hmove, htag⟩ := D.short_bounds S (Fintype.card Z)
  have hcap : 2 ^ (w / 2) ≤ cap :=
    (Nat.pow_le_pow_right (by decide) (show w / 2 ≤ 2 * w by omega)).trans <|
      ((Nat.le_mul_of_pos_left _ (by decide : 0 < 2)).trans
        (Nat.le_mul_of_pos_right _ (by omega : 0 < 4 * w))).trans hu
  have h3 : 3 ≤ cap := by
    have := Nat.pow_le_pow_right (by decide : 0 < 2) (show 2 ≤ w / 2 by omega)
    omega
  have hu' : 16 * (2 * D.u * D.z) ≤ w := by rwa [← D.width, ← mul_assoc]
  have hd : 8 * (D.q * D.recordWidth) ≤ w := by
    calc
      _ ≤ 8 * (D.q * (2 * (D.b * D.z))) := by gcongr; unfold recordWidth; omega
      _ = 16 * (D.q * D.b) * D.z := by ring
      _ ≤ _ := ht
  have ht' : 2 ^ S.m * D.PortCount S + 32 * (D.K * D.v) + (wd x + wd y) * D.n ≤ 2 ^ j := by
    simpa only [rows, mul_assoc] using hrows
  have hr' : D.K * (2 * D.v) = 2 * (D.K * D.v) := by ring
  have hh' := D.controls_card S (Z := Z)
  let x' := w / (8 * D.v) + 1
  have hc : w < 8 * D.v * x' := Nat.lt_mul_div_succ _ (by positivity)
  have hs : 8 * D.v * x' ≤ w + 8 * D.v := by
    unfold x'
    rw [mul_add, mul_one]
    exact Nat.add_le_add_right (Nat.mul_div_le _ _) _
  have lift : 4 * w ≤ 32 * D.v * x' := by nlinarith only [hc]
  have fits : (2 * D.v) ^ 2 + 2 * (2 * D.v * x') < j := by nlinarith only [hs, hv, hv', hh, hj, hw]
  constructor
  · exact ⟨hj, by omega, h3, hu, by omega, by omega, by omega, by omega, by omega,
      by unfold CodeFits; omega, by omega, (by omega : 2 * S.m ≤ 4 * w).trans lift,
      (by omega : D.e ≤ 4 * w).trans lift, fits, by rw [mul_left_comm]; omega⟩
  · refine ⟨⟨hj, by omega, h3, hu, by omega, ?_, ?_, ?_, ?_⟩, by omega, by omega, by omega, by omega,
      by omega, ?_⟩
    · change (4 * D.v * D.u) ^ 2 + 2 * (2 * D.u * D.z) < j
      omega
    · change 2 ^ S.h * (1 + S.ℓ + 2 * D.u ^ 2) + 2 * D.u * D.z < j
      omega
    · change w ≤ D.a + 2 * D.u * D.z + 2
      omega
    · change D.a + 2 * D.u * D.z + 2 ≤ 4 * w
      omega
    · exact (Nat.mul_le_mul_left _ (show D.recordWidth + 1 ≤ D.h + 1 + D.b * D.z + 2 by
        unfold recordWidth; omega)).trans (le_min ((hsmall.trans (min_le_right ..)).trans hcap) hsmall)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dimensions
end

section
/-!
# Converting a bit budget into one array size

Reserve sufficient rows before seeing the chosen summand. All the
sorting calls then use the same dyadic height.
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dimensions
open Assembly PackRows

variable {F : Type} (D : Dimensions) (S : Scheme F) (x y : Wire) (w T : ℕ)

structure Budget : Prop where
  min : 64 ≤ w
  narrow : 16 * (D.q * D.b) * D.z ≤ w
  wide : w ≤ 32 * (D.q * D.b) * D.z
  bins : D.K = 512 * T / (D.v * w) + 1
  host : 2 ^ S.m * (D.PortCount S + 2) * w ≤ T
  exterior : (wd x + wd y) * D.copies ≤ T
  slack : D.v * w ≤ T
  base : 2 ^ w * w ≤ T
  upper : 50000 * T ≤ 2 ^ (5 * w / 4)

def height := max w (Nat.clog 2 (D.rows S x y))

namespace Budget
variable {D S x y w T} (B : D.Budget S x y w T)

include B

private theorem bin_budget : 512 * T ≤ D.K * (D.v * w) ∧ D.K * (D.v * w) ≤ 513 * T := by
  rw [B.bins]
  have hm := B.min
  have hv : 0 < D.v * w := Nat.mul_pos (by positivity) (by omega)
  refine ⟨?_, ?_⟩
  · exact (Nat.lt_mul_div_succ _ hv).le.trans_eq (mul_comm _ _)
  · rw [add_mul, one_mul]
    have := Nat.div_mul_le_self (512 * T) (D.v * w)
    have := B.slack
    omega

theorem fits [Field F] {G : Diagram F x y} (t : Assignment D S G)
    (hl : ∀ i j, t.state.load i j ≤ (D.u * D.z : ℕ)) (hc : t.state.X ≤ T)
    (hr : D.PortCount S + 2 + 2 * 2 ^ S.h ≤ D.v) : t.Fits := by
  apply t.fits hl hr
  have hs : D.u * D.z ≤ w := by
    have h := B.narrow
    rw [D.width] at h
    nlinarith only [h]
  have he : w ≤ 64 * (D.u * D.z) := by
    refine B.wide.trans_eq ?_
    rw [D.width]; ring
  have hk : 8 * T ≤ D.K * D.v * D.u * D.z := by
    have h := B.bin_budget.1.trans (Nat.mul_le_mul_left D.K (Nat.mul_le_mul_left D.v he))
    nlinarith only [h]
  have hh := (Nat.mul_le_mul_left (2 ^ S.m * (D.PortCount S + 2)) hs).trans B.host
  have hv := (Nat.mul_le_mul_left D.v hs).trans B.slack
  exact le_trans (by nlinarith only [hc, hh, hv, B.exterior]) hk

theorem row_count : D.rows S x y * w ≤ 16500 * T := by
  have h₁ := B.host
  have h₂ := B.bin_budget.2
  have h₃ : (wd x + wd y) * D.n * w ≤ 64 * T := by
    calc
      _ ≤ (wd x + wd y) * D.n * (32 * (D.q * D.b) * D.z) := Nat.mul_le_mul_left _ B.wide
      _ = 32 * (wd x + wd y) * (D.n * D.q) * (D.b * D.z) := by ring
      _ = 64 * ((wd x + wd y) * D.copies) := by rw [D.cover]; unfold copies; ring
      _ ≤ _ := Nat.mul_le_mul_left _ B.exterior
  unfold rows
  ring_nf at h₁ h₂ h₃ ⊢
  omega

private theorem height_bounds :
    4 * S.m ≤ 5 * w ∧ 4 * D.height S x y w ≤ 5 * w ∧ 2 ^ (D.height S x y w) * (1 + w) ≤ 100000 * T := by
  let u := D.rows S x y
  have hm := B.min
  have hu : 2 ^ S.m ≤ u := by
    unfold u rows
    have hd : 0 < D.PortCount S := by unfold PortCount; positivity
    have := Nat.le_mul_of_pos_right (2 ^ S.m) hd
    omega
  have hu' : 0 < u := lt_of_lt_of_le (by positivity) hu
  have ht : u ≤ 2 ^ (5 * w / 4) :=
    (Nat.le_mul_of_pos_right _ (by omega : 0 < w)).trans
      (B.row_count.trans ((by omega : 16500 * T ≤ 50000 * T).trans B.upper))
  have hH := (Nat.pow_le_pow_iff_right (by decide : 1 < 2)).mp (hu.trans ht)
  have hJ := Nat.clog_le_of_le_pow ht
  change 4 * S.m ≤ 5 * w ∧ 4 * max w (Nat.clog 2 u) ≤ 5 * w ∧ _
  refine ⟨by omega, by omega, ?_⟩
  have he : 2 ^ (Nat.clog 2 u) ≤ 2 * u := by
    cases eq : Nat.clog 2 u with
    | zero => simp; omega
    | succ k =>
      have h : 2 ^ k < u := Nat.pow_lt_of_lt_clog (by omega)
      rw [pow_succ']; omega
  have hk : 2 ^ (D.height S x y w) ≤ 2 * u + 2 ^ w := by
    change 2 ^ (max w (Nat.clog 2 u)) ≤ _
    rcases le_total w (Nat.clog 2 u) with ht | ht
    · rw [max_eq_right ht]; exact he.trans (Nat.le_add_right ..)
    · rw [max_eq_left ht]; exact Nat.le_add_left ..
  refine (Nat.mul_le_mul hk (show 1 + w ≤ 2 * w by omega)).trans ?_
  have hr : u * w ≤ 16500 * T := B.row_count
  nlinarith only [hr, B.base]

theorem charge : 2 ^ (D.height S x y w) * (1 + w) ≤ 100000 * T := B.height_bounds.2.2

theorem room {Z : Type} [Fintype Z] {cap : ℕ} (he : D.e = 2 * w) (ha : D.a = 3 * w)
    (hh : 8 * D.shortWidth S (Fintype.card Z) ≤ w) (hext : D.h + 4 ≤ D.b * D.z)
    (hu : 2 * 2 ^ (2 * w) * (4 * w) ≤ cap)
    (hsmall : 2 * 2 ^ (D.h + 2) * (D.h + 1 + D.b * D.z + 2) ≤ Min.min (2 ^ ((Nat.clog 2 w) ^ 3)) (2 ^ (w / 2))) :
    let j := D.height S x y w
    FitsControls D S Z w j cap (32 * D.v) (w / (8 * D.v) + 1) ∧ FitsScreen D S x y w j cap :=
  D.room S B.min (le_max_left ..) B.height_bounds.2.1 B.height_bounds.1 he ha hh B.narrow hext
    ((Nat.le_pow_clog (by decide) _).trans (Nat.pow_le_pow_right (by decide) (le_max_right ..))) hu hsmall

end Budget
end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dimensions
end

section
/-!
# Paying for the transfer and the terminal host

Long names are charged once per potential contact. The surviving
blocks absorb this cost, while the stack width pays for the short
controls at individual occurrences.
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent

variable {F : Type} [Field F] {x y : Wire} {G : Diagram F x y} {D : Dimensions}
  {M C c e R J w : ℕ}

theorem Transfer.funded (b : Transfer G D M C c e R J w) (Q V B : ℕ)
    (hj : 1 ≤ J) (_hq : c + 2 ≤ Q) (hr : Q + 2 * c + 10 ≤ R) (hv : R + c + 5 ≤ V)
    (hb : 100 * (1 + V + e) ≤ B) (hrsv : R * J ≤ D.h) (hsize : 2 ^ w ≤ M)
    (hwidth : 2 ^ (B * J) ≤ w) (hn : 16 * (D.q * D.b) * D.z ≤ w) (hu : w ≤ 32 * (D.q * D.b) * D.z)
    (fq : D.q = 2 ^ (Q * J)) (fv : 2 * D.v = 2 ^ (V * J)) (fd : D.d ≤ 2 ^ (c * J))
    (T : ℕ) (hT : T = allowance C D.h J (D.b * D.z) M (wd x + wd y))
    (fk : D.K = 512 * T / (D.v * w) + 1) (ht : 10 ^ 38 * T ≤ 2 ^ (5 * w / 4)) :
    D.Budget b.scheme x y w T ∧ D.shortBudget M e J ≤ T ∧ D.longBudget M c R J w ≤ T ∧
      D.PortCount b.scheme + 2 + 2 * 2 ^ b.scheme.h ≤ D.v := by
  let p (a : ℕ) := 2 ^ (a * J)
  have add (a d : ℕ) : p (a + d) = p a * p d := by simp [p, add_mul, pow_add]
  have pos (a : ℕ) : 0 < p a := Nat.two_pow_pos _
  have le (a : ℕ) : 2 ^ a ≤ p a :=
    Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ hj)
  have mono : Monotone p := fun _ _ h => Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ h)
  let N := 2 ^ (D.h - R * J)
  let L := 2 ^ (D.h - J)
  let k := D.b * D.z
  have hJ : J ≤ D.h := (Nat.le_mul_of_pos_left _ (by omega : 0 < R)).trans hrsv
  have sumR : N * p R = 2 ^ D.h := by unfold N p; rw [← pow_add, Nat.sub_add_cancel hrsv]
  have sumJ : L * p 1 = 2 ^ D.h := by unfold L p; rw [one_mul, ← pow_add, Nat.sub_add_cancel hJ]
  have core : L * k * M ≤ T := by
    rw [hT, allowance]
    exact (Nat.le_add_right _ _).trans (Nat.le_mul_of_pos_left _ (by omega))
  have outer : (wd x + wd y) * D.copies ≤ T := by
    rw [hT, allowance, Dimensions.copies, mul_comm (wd x + wd y)]
    exact (Nat.le_add_left _ _).trans (Nat.le_mul_of_pos_left _ (by omega))
  have upper : w ≤ p (5 + Q) * k := calc
    _ ≤ 32 * (D.q * D.b) * D.z := hu
    _ = (2 ^ 5 * p Q) * k := by rw [fq]; unfold k p; ring
    _ ≤ _ := by rw [add]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ (le 5))
  have stack : p (1 + e) ≤ k := by
    apply Nat.le_of_mul_le_mul_left _ (pos (5 + Q))
    rw [← add]
    exact (mono (by omega : 5 + Q + (1 + e) ≤ B)).trans (hwidth.trans upper)
  have short : D.shortBudget M e J ≤ T := calc
    _ = L * p (1 + e) * M := by
      change M * 2 ^ D.h * p e = _
      rw [add, ← sumJ]; ring
    _ ≤ L * k * M := Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ stack)
    _ ≤ _ := core
  have ports : D.PortCount b.scheme + 2 ≤ 5 * p c := by
    have h := Nat.pow_le_pow_right (by decide : 0 < 2) b.lanes
    have := pos c
    unfold Dimensions.PortCount p at *
    omega
  have port_exp : D.PortCount b.scheme + 2 ≤ p (3 + c) := by
    rw [add]
    exact ports.trans (Nat.mul_le_mul_right _ ((by decide : 5 ≤ 2 ^ 3).trans (le 3)))
  have hosts : 2 ^ b.scheme.m ≤ M * N * p c := by
    apply Nat.le_of_mul_le_mul_right _ (pos R)
    refine b.hosts.trans_eq ?_
    change M * 2 ^ D.h * p c = _
    rw [← sumR]; ring
  have allocation : N * p c * p (3 + c) * p (5 + Q) ≤ L := by
    apply Nat.le_of_mul_le_mul_right _ (pos 1)
    rw [sumJ, ← sumR]
    simp only [mul_assoc, ← add]
    exact Nat.mul_le_mul_left _ (mono (by omega))
  have paid : (M * N * p c) * p (3 + c) * w ≤ T := calc
    _ ≤ (M * N * p c) * p (3 + c) * (p (5 + Q) * k) := Nat.mul_le_mul_left _ upper
    _ = (N * p c * p (3 + c) * p (5 + Q)) * k * M := by ring
    _ ≤ L * k * M := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ allocation)
    _ ≤ _ := core
  have long : D.longBudget M c R J w ≤ T :=
    (Nat.mul_le_mul_right w (Nat.le_mul_of_pos_right _ (pos (3 + c)))).trans paid
  have host : 2 ^ b.scheme.m * (D.PortCount b.scheme + 2) * w ≤ T :=
    (Nat.mul_le_mul_right _ (Nat.mul_le_mul hosts port_exp)).trans paid
  have base : 2 ^ w * w ≤ T := by
    have h := (Nat.le_mul_of_pos_right M (show 0 < N from Nat.two_pow_pos _)).trans
      (Nat.le_mul_of_pos_right _ (pos c))
    exact (Nat.mul_le_mul_right _ (hsize.trans h)).trans long
  have hv' : D.v ≤ 2 ^ w := calc
    _ ≤ 2 * D.v := by omega
    _ = p V := fv
    _ ≤ p B := mono (by omega)
    _ ≤ w := hwidth
    _ ≤ _ := Nat.lt_two_pow_self.le
  have hmin : 64 ≤ w := (le 6).trans ((mono (by omega : 6 ≤ B)).trans hwidth)
  refine ⟨⟨hmin, hn, hu, fk, host, outer, (Nat.mul_le_mul_right _ hv').trans base, base,
    (Nat.mul_le_mul_right _ (by norm_num : 50000 ≤ 10 ^ 38)).trans ht⟩, short, long, ?_⟩
  have hp := mono (show c ≤ R + c by omega)
  have hk : 2 ^ b.scheme.h ≤ p (R + c) := Nat.pow_le_pow_right (by decide) b.blocks
  have hh : 14 * p (R + c) ≤ 2 * D.v := calc
    _ ≤ p 5 * p (R + c) := Nat.mul_le_mul_right _ ((by decide : 14 ≤ 2 ^ 5).trans (le 5))
    _ ≤ p V := by rw [← add]; exact mono (by omega)
    _ = _ := fv.symm
  omega

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

section
/-!
# Cost of one controlled transfer

Pass the public bits through once, then close the terminal layouts.
Batch the remaining short tables after composing every stage.
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Transfer
open Assembly Coloring

variable {F : Type} [Field F] {x y : Wire} {G : Diagram F x y} {D : Dimensions}
    {M C c e R J w T : ℕ} (b : Transfer G D M C c e R J w)

private theorem endpoints (budget : D.Budget b.scheme x y w T)
    (hT : T = allowance C D.h J (D.b * D.z) M (wd x + wd y)) (hJ : J ≤ D.h)
    (hu : 2 ^ (c * J) * D.b ≤ D.u) (hv : D.PortCount b.scheme + 2 + 2 * 2 ^ b.scheme.h ≤ D.v) :
    ∀ i a v, ∃ (G : Diagram F x y) (t : Assignment D b.scheme G) (hw : t.Fits),
      b.stop.eval i a v = t.state.diagram.eval a v ∧ b.view.Valid t hw (b.stop.encode i a v) := by
  intro i a v
  obtain ⟨t, hw, hl, hv', hc⟩ := b.correct i a v
  have hx : t.state.X ≤ T := by
    apply Nat.cast_le (α := ℝ) |>.mp
    rw [hT, allowance_value _ _ _ _ _ _ hJ]
    refine hw.trans ?_
    unfold Dimensions.copies
    gcongr
    linarith
  have ht (u j) : t.state.load u j ≤ (D.u * D.z : ℕ) :=
    (hl u j).trans (Nat.cast_le.mpr (Nat.mul_le_mul_right D.z hu))
  exact ⟨G, t, budget.fits t ht hx hv, hv', hc _⟩

theorem build (budget : D.Budget b.scheme x y w T)
    (hT : T = allowance C D.h J (D.b * D.z) M (wd x + wd y)) (hJ : J ≤ D.h)
    (hu : 2 ^ (c * J) * D.b ≤ D.u) (hv : D.PortCount b.scheme + 2 + 2 * 2 ^ b.scheme.h ≤ D.v)
    (hs : D.shortBudget M e J ≤ T) (hl : D.longBudget M c R J w ≤ T)
    (he : D.e = 2 * w) (ha : D.a = 3 * w) (hh : 8 * D.shortWidth b.scheme (Fintype.card b.Z) ≤ w)
    (hext : D.h + 4 ≤ D.b * D.z)
    (hsmall : 2 * 2 ^ (D.h + 2) * (D.h + 1 + D.b * D.z + 2) ≤ min (2 ^ ((Nat.clog 2 w) ^ 3)) (2 ^ (w / 2)))
    (htop : 10 ^ 38 * T ≤ 2 ^ (5 * w / 4)) :
    ∃ u s, Wide F u (Allowed F w) (copies x D.copies) (copies y D.copies)
      (MatrixExponent.power G.eval D.copies) s ∧ s ≤ 10 ^ 35 * T := by
  let cap := max b.scale (2 * 2 ^ (2 * w) * (4 * w))
  let L := Allowed F w ∪ (b.labels : Set (Table F))
  let j := D.height b.scheme x y w
  obtain ⟨hc, hr⟩ := budget.room he ha hh hext (show 2 * 2 ^ (2 * w) * (4 * w) ≤ cap from le_max_right ..) hsmall
  have done := terminal b.stop b.view hc hr (b.endpoints budget hT hJ hu hv)
  have large : Allowed F w ⊆ L := Set.subset_union_left
  have prog := b.transfer.widen (le_max_left b.scale (2 * 2 ^ (2 * w) * (4 * w))) (Set.Subset.refl L)
  obtain ⟨n, hn, net⟩ := prog.public_end hc.gates (done.widen le_rfl large) b.first b.code b.encoded
  have hb := b.cost
  have hex : wd (copies x D.copies) + wd (copies y D.copies) ≤ T := by
    rw [wd_copies, wd_copies, ← mul_add, mul_comm]
    exact budget.exterior
  have width : b.stop.public.port.width = b.stop.port.width +
      (wd (copies x D.copies) + wd (copies y D.copies)) := by
    rw [show b.stop.public.port = b.stop.port.pair (.wire (.pair _ _)) from rfl, Format.width_pair]
    exact congrArg _ (card_slots (.pair _ _))
  have hcost := budget.charge
  rw [width] at hn
  have h₁ : n ≤ 10 ^ 26 * T := by omega
  have h₃ := budget.min
  have hn' : n ≤ 2 ^ (2 * w - 1) := (h₁.trans ((by omega : 10 ^ 26 * T ≤ 10 ^ 38 * T).trans htop)).trans
    (Nat.pow_le_pow_right (by decide) (by omega))
  rw [b.power] at net
  obtain ⟨u, s, hs, hsize⟩ := batch_labels h₃ b.labels b.few b.small net hn'
  have hw := budget.base
  rw [mul_comm (2 ^ w)] at hw
  exact ⟨u, s, hs, by omega⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Transfer
end

section
/-! # Fitting short descriptions below the sorting address width -/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Filter
variable {F : Type} [Field F]

theorem Recipe.shallow (P : Recipe F) (R : ℕ) :
    ∀ᶠ J : ℕ in atTop, P.blocks (R + J) J ≤ 2 ^ J := by
  filter_upwards [replication (by norm_num : (0 : ℝ) < 1) (R + 1 + P.n * (P.H + 5))] with j hj
  have hb := hj _ le_rfl
  rw [Real.rpow_one] at hb
  have he : (2 : ℕ) ^ ((R + 1 + P.n * (P.H + 5)) * j ^ 2) ≤ 2 ^ (2 ^ j) := by exact_mod_cast hb
  exact (P.reserve_width R j).trans ((Nat.pow_le_pow_iff_right (by decide)).mp he)

private theorem bound (e j B : ℕ) (he : 1 ≤ e) (hj : 1 ≤ j) (hB : 100 * e ≤ B) :
    (100 + 2 ^ (e * j)) ^ 8 ≤ 2 ^ (B * j) := by
  have hl := Nat.mul_pos he hj
  have ha : 100 + 2 ^ (e * j) ≤ 2 ^ (7 + e * j) := by
    rw [pow_add]; have := Nat.two_pow_pos (e * j); omega
  calc
    _ ≤ (2 ^ (7 + e * j)) ^ 8 := Nat.pow_le_pow_left ha _
    _ = 2 ^ ((7 + e * j) * 8) := (pow_mul ..).symm
    _ ≤ 2 ^ (B * j) := Nat.pow_le_pow_right (by decide) (by
      have := Nat.mul_le_mul_right j hB
      rw [mul_assoc] at this
      omega)

theorem Transfer.short {x y : Wire} {G : Diagram F x y} {D : Dimensions}
    {M C c e R J w Q V B b : ℕ} (t : Transfer G D M C c e R J w)
    (hj : 1 ≤ J) (hr : Q ≤ R) (hv : R + c + 5 ≤ V) (hb : 100 * (1 + b + V + e) ≤ B)
    (hh : D.h ≤ 2 ^ J) (hb' : D.b = b ^ J) (hq : D.q = 2 ^ (Q * J)) (hrow : D.r ≤ V * J)
    (hw : 2 ^ (B * J) ≤ w) : 8 * D.shortWidth t.scheme (Fintype.card t.Z) ≤ w := by
  let L := 1 + b + V + e
  have pow (n : ℕ) (hn : n ≤ L) : 2 ^ (n * J) ≤ 2 ^ (L * J) :=
    Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hn)
  have huge := bound L J B (by unfold L; omega) hj hb
  have unit : D.u ≤ 2 ^ (L * J) := by
    calc
      D.u ≤ D.q * D.b := by rw [D.width]; omega
      _ ≤ 2 ^ (Q * J) * (2 ^ b) ^ J := by rw [hq, hb']; gcongr; exact Nat.lt_two_pow_self.le
      _ = 2 ^ ((Q + b) * J) := by rw [add_mul, pow_add, pow_mul 2 b]
      _ ≤ _ := pow (Q + b) (by unfold L; omega)
  have hpow := pow V (by unfold L; omega)
  apply le_trans _ (huge.trans hw)
  apply D.shortWidth_le
  · exact t.bits.trans (pow _ (by unfold L; omega))
  · exact (Nat.pow_le_pow_right (by decide) t.blocks).trans (pow _ (by unfold L; omega))
  · exact t.tag.trans (pow _ (by unfold L; omega))
  · exact hrow.trans ((Nat.lt_two_pow_self.le).trans hpow)
  · exact hh.trans (by simpa using pow 1 (by unfold L; omega))
  · rw [hq]; exact pow _ (by unfold L; omega)
  · exact unit
  · exact (Nat.pow_le_pow_right (by decide) hrow).trans hpow

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

section
/-!
# A succinct transfer yields the many-list compiler

Fix the exponent of the long-name cost before the terminal reserve.
Then choose the width scale after the short-record exponent is known.
The logarithmic number of beats yields a power saving in that width.
-/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Filter

variable {F : Type} [Field F]

private theorem final_cost (B J w C h k M E s : ℕ) (hB : 0 < B) (hw : 1 ≤ w)
    (hu : w ≤ 2 ^ (2 * B * J)) (hJ : J ≤ h) (hs : s ≤ 10 ^ 35 * allowance C h J k M E) :
    (s : ℝ) ≤ (10 ^ 35 * (C + 1) : ℕ) * (2 ^ h * k : ℕ) *
      ((M : ℝ) * (w : ℝ) ^ (-(1 / (2 * B : ℝ))) + E) := by
  have h := Nat.cast_le (α := ℝ) |>.mpr hs
  rw [Nat.cast_mul, allowance_value _ _ _ _ _ _ hJ] at h
  refine h.trans ?_
  push_cast
  rw [mul_comm (M : ℝ), ← mul_assoc, ← mul_assoc]
  gcongr
  exact saving hB hw hu

theorem compilation_of_encoded (h : Encoded F) : Compilation F := by
  obtain ⟨P, C, c, d, hd, h⟩ := h
  let Q := c + 2
  let R := Q + 2 * c + 10
  let V := R + c + 5
  obtain ⟨e, H⟩ := h Q R V le_rfl le_rfl le_rfl
  let B := 100 * (1 + P.b + V + e)
  have hQR : Q ≤ R := by unfold R; omega
  have hVQ : Q ≤ V := by unfold V; omega
  have hB : 5 + Q + P.b + V ≤ B := by unfold B; omega
  have hb : 0 < B := by omega
  obtain ⟨L, hL⟩ := eventually_atTop.mp <| (H B le_rfl).and <|
    (P.reserve_limits R Q B (by omega)).and (P.shallow R)
  refine ⟨10 ^ 35 * (C + 1), 1 / (2 * (B : ℝ)), by positivity, fun κ hk => ?_⟩
  let δ := min κ (1 / 20 : ℝ)
  filter_upwards [P.reserve_parameters R Q V B L hB (show 0 < δ by unfold δ; positivity),
    allowance_small C, eventually_ge_atTop 1] with w hw hall hw'
  obtain ⟨J, z, hL', hJ, hl, hu, hz, hdiv, hlo, hhi, hp, hdim⟩ := hw
  obtain ⟨run, limits, shallow⟩ := hL J hL'
  intro x y k v M net h₀ low high
  obtain ⟨G, rfl, hg, hcard⟩ := net.diagram
  by_cases hG : Nonempty G.V
  swap
  · let _ := not_nonempty_iff.mp hG
    have hv : v = 0 := hcard.symm.trans Fintype.card_of_isEmpty
    obtain ⟨n, hn, hnet⟩ := (net.power 1).includeWide (L := Allowed F w) (le_rfl : 3 ≤ 3)
    have hzero : n = 0 := by simpa [hv] using hn
    refine ⟨1, 3, n, le_rfl, ?_, hnet, ?_⟩
    · rw [Nat.cast_one]
      apply Real.one_le_rpow _ hk.le
      exact_mod_cast Nat.one_le_pow w 2 (by decide)
    · rw [hzero, Nat.cast_zero]
      positivity
  let b := P.blocks (R + J) J
  let T := allowance C b J (P.b ^ J * z) M (wd x + wd y)
  have hq : 0 < Q * J := Nat.mul_pos (by unfold Q; omega) hJ
  have hv : 0 < V * J := Nat.mul_pos (by unfold V; omega) hJ
  have hr : R * J ≤ b := by
    unfold b Recipe.blocks
    exact (Nat.mul_le_mul_right J (Nat.le_add_right ..)).trans (Nat.le_add_right ..)
  have hr' : J ≤ b := (Nat.le_mul_of_pos_left _ (by unfold R; omega)).trans hr
  have hh : Q * J ≤ b + 1 := (Nat.mul_le_mul_right _ hQR).trans (hr.trans (Nat.le_succ b))
  let D := P.dimensions w J z (R + J) Q V (2 ^ (d * J)) T hq hv hh hz hdiv
  have hZ : D.z = z := P.dimensions_z ..
  have copies : D.copies = P.batch (R + J) J z := P.dimensions_copies ..
  have hT : T = allowance C D.h J (D.b * D.z) M (wd x + wd y) := by rw [hZ]; rfl
  obtain ⟨a⟩ := run w z T hq hv hh hz hdiv hl hu hlo hhi x y G M hG hg (by omega) low high
  change Transfer G D M C c e R J w at a
  have hn : (D.copies : ℝ) ≤ (2 ^ w : ℕ) ^ δ := by
    simpa only [copies, Nat.cast_pow, Nat.cast_ofNat] using hdim
  have big : 1 ≤ (↑(2 ^ w : ℕ) : ℝ) := by exact_mod_cast Nat.one_le_pow w 2 (by decide)
  have top : 10 ^ 38 * T ≤ 2 ^ (5 * w / 4) := by
    rw [hT]
    exact hall _ _ _ _ _ hr' (by omega) high
      (hn.trans (Real.rpow_le_rpow_of_exponent_le big (min_le_right ..)))
  have hsmall : 8 * D.shortWidth a.scheme (Fintype.card a.Z) ≤ w :=
    a.short hJ hQR (le_rfl : R + c + 5 ≤ V) (le_rfl : 100 * (1 + P.b + V + e) ≤ B) shallow rfl rfl
      (Nat.sub_le ..) hl
  obtain ⟨budget, short, long, room⟩ := a.funded Q V B hJ le_rfl le_rfl le_rfl
    (by unfold B; omega) hr low hl (by rw [hZ]; exact hlo) (by rw [hZ]; exact hhi) rfl
    (P.dimensions_rows ..) (Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ hd))
    T hT rfl top
  have hunit : 2 ^ (c * J) * D.b ≤ D.u := by
    apply Nat.mul_le_mul_right
    apply Nat.pow_le_pow_right (by decide)
    unfold Q
    rw [add_mul]
    omega
  obtain ⟨hdepth, hsort⟩ := limits z w hl hu hlo hhi
  obtain ⟨u, s, hwide, hcost⟩ := a.build budget hT hr' hunit room short long rfl rfl hsmall
    (by rw [hZ]; exact hdepth) (by rw [hZ]; exact hsort) top
  refine ⟨D.copies, u, s, by rw [copies]; exact hp,
    hn.trans (Real.rpow_le_rpow_of_exponent_le big (min_le_left ..)), hwide, ?_⟩
  rw [hT] at hcost
  exact final_cost B J w C D.h (D.b * D.z) M (wd x + wd y) s hb hw' hu hr' hcost

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

section
/-! # Many-list encoding at a failed hardness test -/

namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent

theorem encoded {F : Type} [Field F] [Finite F] (h : ¬ Tagged.Hard F) : Encoded F := by
  let _ := Fintype.ofFinite F
  exact encoded_of_rules h (subroundRule F) (resetRule F)

end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end
