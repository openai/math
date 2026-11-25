import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Pieces
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.PortRelay
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Header
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dictionary
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Exterior.Strips

/-! # Checking short bin controls while hiding the unique anchor tape -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows

open Classical Coloring Transcript

variable {H v K m d ℓ u : ℕ} {D Z X : Type}

def anchored (e : Fin H ↪ Anchor v K) (src : Fin H → D → Bool)
    (i : Fin K) (p : BinKey v D) : Bool :=
  p.2.elim (decide ((i, p.1) ∈ Set.range e))
    (fun k => Function.extend e (fun j => src j k) (fun _ => false) (i, p.1))

theorem BinData.anchored {code : (D → Bool) → Descriptor m d ℓ} {l : Inventory H m d}
    (hv : 0 < v) (hs : ∀ i, size (l i) u ≤ v) (hk : bins l u v ≤ K)
    {ix : Index l u} {f : Label H m ℓ} {src : Fin H → D → Bool}
    (hlen : ∀ i, (code (src i)).len = l i) (hf : ∀ i, (code (src i)).label = f i)
    (hi : ∀ i j p (k : Fin (l i j p)), (code (src i)).slot j p k.val = (ix i j ⟨p, k⟩).val) :
    BinData code l u v K hv hs hk ix f src (PackRows.anchored (anchor l u v K hv hs hk) src) :=
  ⟨fun _ _ => decide_eq_true_iff,
    fun i k => (anchor l u v K hv hs hk).injective.extend_apply (fun j => src j k) (fun _ => false) i, hlen, hf, hi⟩

variable [Fintype X] [Fintype D] [Fintype Z] {w j h r cap : ℕ}

/-- The public input determines every anchor bit. Summing over that
intermediate tape therefore preserves the scalar weight. -/
theorem bin_service (F : Type) [Field F] (len : (D → Bool) → ℕ)
    (code : (D → Bool) → Descriptor m d ℓ) (user : (D → Bool) → Fin d → Fin (2 ^ r) → Z → Bool)
    (src : B h → D → X ⊕ Bool) (dst : Fin K → BinOut (2 ^ r) u m ℓ Z → X ⊕ Bool)
    (hj : w ≤ j) (hj' : j + 1 ≤ 2 * w) (hc : 3 ≤ cap) (ha : 2 * 2 ^ (2 * w) * (4 * w) ≤ cap)
    (hd : Fintype.card D + (r + 1) < j) (hsize : 2 ^ h + K * 2 ^ r ≤ 2 ^ j)
    (hkey : Fintype.card (BinKey (2 ^ r) D) + Fintype.card (BinOut (2 ^ r) u m ℓ Z) < j) :
    ∃ f : (X → Bool) → F, WideWeight F cap (SortTables F w) f (10 ^ 12 * (Fintype.card X + 2 ^ j * (1 + w))) ∧
      ∀ (x : X → Bool) (l : Inventory (2 ^ h) m d) (hs : ∀ i, size (l i) u ≤ 2 ^ r)
        (hk : bins l u (2 ^ r) ≤ K),
        (∀ i, len (Sum.elim x id ∘ src i) = counts l u i) →
        let t := anchored (anchor l u (2 ^ r) K (Nat.two_pow_pos r) hs hk) (fun i => Sum.elim x id ∘ src i)
        f x = if ∀ i, Sum.elim x id ∘ dst i = binFunction u code user (t i) then 1 else 0 := by
  let Y := Fin K × BinKey (2 ^ r) D
  let O := Fin K × BinOut (2 ^ r) u m ℓ Z
  let get (i : Anchor (2 ^ r) K) (k : D) : (X ⊕ Y) ⊕ Bool := .inl (.inr (i.1, i.2, some k))
  let used (i : Anchor (2 ^ r) K) : (X ⊕ Y) ⊕ Bool := .inl (.inr (i.1, i.2, none))
  obtain ⟨t, ht, ht'⟩ := anchor_scatter (m := m) (d := d) (u := u) F len
    (fun i => liftTap ∘ src i) get used hj hj' hc ha hd hsize
  have hK : K ≤ 2 ^ j := (Nat.le_mul_of_pos_right K (Nat.two_pow_pos r)).trans
    ((Nat.le_add_left _ _).trans hsize)
  have hcap : 2 * 2 ^ (j + 1) * (2 * j + 2) ≤ cap := le_trans
    (Nat.mul_le_mul (Nat.mul_le_mul_left 2 (Nat.pow_le_pow_right (by decide) hj')) (by omega)) ha
  let input (i : Fin K) (k : BinKey (2 ^ r) D) : Y ⊕ Bool := .inl (i, k)
  let tap : Y ⊕ O → (X ⊕ Y) ⊕ Bool := Sum.elim (fun y => .inl (.inr y)) (fun o => liftTap (dst o.1 o.2))
  have hnet := binTransform F code user input (Equiv.refl O) hj hj' hc hcap hkey hK
  obtain ⟨f, hf, hout⟩ := hide_unique hc ht (precompute hc ((tap_depends tap).bnet F) hnet)
  refine ⟨f, ?_, fun x l hs hk hl => ?_⟩
  · have hy : Fintype.card Y + Fintype.card O ≤ 2 ^ j * (2 * w) := by
      rw [show Fintype.card Y = K * Fintype.card (BinKey (2 ^ r) D) by
        rw [Fintype.card_prod, Fintype.card_fin],
        show Fintype.card O = K * Fintype.card (BinOut (2 ^ r) u m ℓ Z) by
          rw [Fintype.card_prod, Fintype.card_fin], ← mul_add]
      exact Nat.mul_le_mul hK (hkey.le.trans (by omega))
    intro a i
    obtain ⟨q, hq, hn⟩ := hf a i
    refine ⟨q, hq.trans ?_, hn⟩
    have hh := Nat.mul_le_mul_left (2 ^ j) (show j ≤ 2 * w by omega)
    simp only [Fintype.card_sum, Install.localCost]
    ring_nf at hy hh ⊢
    omega
  let e := anchor l u (2 ^ r) K (Nat.two_pow_pos r) hs hk
  let val := anchored e (fun i => Sum.elim x id ∘ src i)
  let y : Y → Bool := Function.uncurry val
  have unique (z : Y → Bool) : t (Sum.elim x z) = if y = z then 1 else 0 := by
    rw [ht' _ l hs hk (by simpa only [read_lift_fun] using hl)]
    simp only [get, used, Sum.elim_inl, Sum.elim_inr, Function.comp_apply, read_lift]
    congr 1
    apply propext
    constructor
    · rintro ⟨on, data⟩
      funext ⟨i, k, q⟩
      cases q with
      | none => exact Bool.eq_iff_iff.mpr (decide_eq_true_iff.trans (on (i, k)).symm)
      | some j => exact (data (i, k) j).symm
    · rintro rfl
      exact ⟨fun _ => decide_eq_true_iff, fun _ _ => rfl⟩
  rw [hout x y unique]
  simp only [Function.comp_apply]
  congr 1
  apply propext
  simp only [funext_iff, applyRows, tap, input,
    Sum.elim_inl, Sum.elim_inr, Function.comp_def, read_lift]
  exact ⟨fun h i k => (h (i, k)).symm, fun h p => (h p.1 p.2).symm⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
end

/-!
# Joining the two host names to a local header

The physical layout of the identifier is fixed in advance. Each output
bit needs only the activity flag and one bit of the short or long record.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows.Channels
open Classical Coloring Install Transcript

variable {h r n : ℕ}

abbrev Short (r : ℕ) := slots (word (r + 2))
abbrev Long (h : ℕ) := slots (word h) ⊕ slots (word h)

def short : Option (Bool × B r) → Short r → Bool
  | none => fun _ => false
  | some (b, i) => Sum.elim (fun _ => true) (Sum.elim (fun _ => b) ((Format.addr r).code i))

def long (x : B h × B h) : Long h → Bool := (Format.pair (.addr h) (.addr h)).code x

private abbrev Fields (h r : ℕ) := Long h ⊕ slots (word r)

variable (hn : 2 * h + r ≤ n)

private def placeBits : Fields h r ↪ slots (word n) :=
  (Function.Embedding.nonempty_of_card_le (show Fintype.card (Fields h r) ≤ Fintype.card (slots (word n))
    by simpa [Fields, Long, two_mul] using hn)).some

private def takeBit (i : slots (word n)) : Option (Fields h r) :=
  if hit : ∃ j, placeBits hn j = i then some hit.choose else none

private theorem take_place (j : Fields h r) : takeBit hn (placeBits hn j) = some j := by
  have h : ∃ i, placeBits hn i = placeBits hn j := ⟨j, rfl⟩
  rw [takeBit, dite_eq_left h, (placeBits hn).injective h.choose_spec]

private def write (x : Long h → Bool) (y : slots (word r) → Bool) (j : slots (word n)) :=
  (takeBit hn j).elim false (Sum.elim x y)

def code : (B h × B h × B r) ↪ Val (word n) where
  toFun x := (bits (word n)).symm (write hn (long (x.1, x.2.1)) ((Format.addr r).code x.2.2))
  inj' := by
    rintro ⟨i, j, k⟩ ⟨i', j', k'⟩ eq
    have he := (bits (word n)).symm.injective eq
    have hx : (i, j) = (i', j') := by
      apply (Format.pair (.addr h) (.addr h)).code.injective
      funext t
      simpa only [write, take_place, Option.elim_some, Sum.elim_inl, long] using
        congrFun he (placeBits hn (.inl t))
    have hy : k = k' := by
      apply (Format.addr r).code.injective
      funext t
      simpa only [write, take_place, Option.elim_some, Sum.elim_inr] using
        congrFun he (placeBits hn (.inr t))
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hx
    rw [hy]

def merge (x : Long h → Bool) (y : Short r → Bool) : Short n → Bool :=
  if y (.inl ()) then Sum.elim (fun _ => true)
    (Sum.elim (fun _ => y (.inr (.inl ()))) (write hn x (fun i => y (.inr (.inr i)))))
  else bits (word (n + 2)) (false, false, Lookup.zero n)

theorem merge_none (x : Long h → Bool) :
    merge hn x (short none) = bits (word (n + 2)) (false, false, Lookup.zero n) := rfl

theorem merge_eq (x : B h × B h) (y : Option (Bool × B r)) :
    merge hn (long x) (short y) = bits (word (n + 2)) (fill (code hn) x y) := by
  cases y with
  | none => rfl
  | some s =>
    obtain ⟨b, k⟩ := s
    funext t
    rcases t with _|_|i
    · rfl
    · rfl
    · exact congrFun ((bits (word n)).apply_symm_apply (write hn (long x) ((Format.addr r).code k))).symm i

private theorem merge_bit (i : Short n) :
    ∃ j : Long h ⊕ Short r, ∀ a b c d, b (.inl ()) = d (.inl ()) →
      Sum.elim a b j = Sum.elim c d j → merge hn a b i = merge hn c d i := by
  rcases i with _ | _ | k
  · refine ⟨.inr (.inl ()), fun a b c d he _ => ?_⟩
    simp only [merge, he, ite_apply, Sum.elim_inl]
  · refine ⟨.inr (.inr (.inl ())), fun a b c d he hf => ?_⟩
    change b _ = d _ at hf
    simp only [merge, he, ite_apply, Sum.elim_inr, Sum.elim_inl, hf]
  · cases hk : takeBit hn k with
    | none =>
      refine ⟨.inr (.inl ()), fun a b c d he _ => ?_⟩
      simp only [merge, he, ite_apply, Sum.elim_inr, write, hk, Option.elim_none]
    | some j =>
      refine ⟨Sum.map id (fun v => .inr (.inr v)) j, fun a b c d he hf => ?_⟩
      simp only [merge, he, ite_apply, Sum.elim_inr, write, hk, Option.elim_some]
      cases j <;> simp_all

variable {F I X : Type} [Field F] [Fintype I] [Fintype X]
    (lg : I → Long h → X ⊕ Bool) (sm : I → Short r → X ⊕ Bool) (out : I → Short n → X ⊕ Bool)

def written (x : X → Bool) : Prop :=
  ∀ i, Sum.elim x id ∘ out i = merge hn (Sum.elim x id ∘ lg i) (Sum.elim x id ∘ sm i)

theorem merge_net : Weight F (fun x => if written hn lg sm out x then 1 else 0)
    (Fintype.card X + 136 * (Fintype.card I * (n + 2)) + 17) := by
  let bad (x : X → Bool) (p : I × Short n) :=
    decide (Sum.elim x id (out p.1 p.2) ≠ merge hn (Sum.elim x id ∘ lg p.1) (Sum.elim x id ∘ sm p.1) p.2)
  have hb : Depends bad 3 := by
    rintro ⟨i, j⟩
    obtain ⟨k, hk⟩ := merge_bit hn j
    obtain ⟨A, ha, h₁⟩ := tap_depends (sm i) (.inl ())
    obtain ⟨B, hb, h₂⟩ := tap_depends (Sum.elim (lg i) (sm i)) k
    obtain ⟨D, hd, h₃⟩ := tap_depends (out i) j
    refine ⟨(A ∪ B) ∪ D, ?_, fun x y he => ?_⟩
    · have := Finset.card_union_le A B
      have := Finset.card_union_le (A ∪ B) D
      omega
    have h₁ := h₁ x y (fun _ h => he _ (Finset.mem_union_left _ (Finset.mem_union_left _ h)))
    have h₂ := h₂ x y (fun _ h => he _ (Finset.mem_union_left _ (Finset.mem_union_right _ h)))
    have h₃ := h₃ x y (fun _ h => he _ (Finset.mem_union_right _ h))
    have eq : merge hn (Sum.elim x id ∘ lg i) (Sum.elim x id ∘ sm i) j =
        merge hn (Sum.elim y id ∘ lg i) (Sum.elim y id ∘ sm i) j :=
      hk _ _ _ _ h₁ (by cases k <;> exact h₂)
    simp only [Function.comp_apply] at h₃
    simp only [bad, eq, h₃]
  have net := ((hb.bnet F).comp (BNet.any F (I × Short n))).weight
    (Weight.dense F Unit (fun x => if x () then 0 else 1))
  convert net using 1
  · funext x
    have eq : (∃ i, bad x i = true) ↔ ¬written hn lg sm out x := by
      simp only [bad, written, Prod.exists, funext_iff, decide_eq_true_eq, not_forall, Function.comp_apply]
    simp only [Function.comp_apply, decide_eq_true_eq, eq, ite_not]
  · simp only [localCost, Fintype.card_prod, Fintype.card_unit, Short]
    rw [card_slots (word (n + 2)), wd_word]
    omega

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows.Channels
end

/-! # Routing and checking normalized internal headers -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
open Classical Transcript Coloring

variable {X Y D L T P : Type} {h r K d u j w m n cap : ℕ}

def readIndex (r : ℕ) : RelayRead (Fin (2 * 2 ^ r) × Fin (2 * 2 ^ r)) r :=
  fun c i => if he : ∃ j, c (i, j) = true then some he.choose else none

theorem readIndex_eq {c : Fin (2 * 2 ^ r) × Fin (2 * 2 ^ r) → Bool} {i j : Fin (2 * 2 ^ r)}
    (hc : ∀ k, c (i, k) = true ↔ k = j) : readIndex r c i = some j := by
  have he : ∃ k, c (i, k) = true := ⟨j, (hc j).mpr rfl⟩
  rw [readIndex, dite_eq_left he, (hc _).mp he.choose_spec]

theorem delivered_at {Z : Type} (e : B h × Fin d ↪ Address (2 ^ r) K)
    (srcLong : B h × Fin d → Z → X ⊕ Bool) (read : RelayRead L r) (ctrl : Fin K → L → X ⊕ Bool)
    (x : X → Bool) (v : Address (2 ^ r) K) (i : B h × Fin d)
    (hb : v.1 = (e i).1) (hr : read (Sum.elim x id ∘ ctrl v.1) v.2 = some (e i).2) :
    delivered e srcLong read ctrl x v = Sum.elim x id ∘ srcLong i := by
  funext t
  rw [delivered, hr, Option.elim_some, hb, Prod.mk.eta, e.injective.extend_apply]
  rfl

private theorem delivered_lift {Z : Type} (e : B h × Fin d ↪ Address (2 ^ r) K)
    (srcLong : B h × Fin d → Z → X ⊕ Bool) (read : RelayRead L r) (ctrl : Fin K → L → X ⊕ Bool)
    (x : X → Bool) (y : Y → Bool) (v : Address (2 ^ r) K) :
    delivered e (fun i => liftTap ∘ srcLong i) read (fun i => liftTap ∘ ctrl i) (Sum.elim x y) v =
      delivered e srcLong read ctrl x v := by
  funext k
  simp only [delivered, read_lift_fun, Function.comp_apply, read_lift]

namespace Channels

private theorem cost {X Y T N w : ℕ} (hp : 0 < N) (hy : Y ≤ N * (4 * w)) (ht : T ≤ N * (4 * w)) :
    8 * (X + Y) + 9 * (10 ^ 12 * (X + Y + N * (1 + w)) + 4 * (X + Y + 136 * T + 17)) ≤ 10 ^ 15 * (X + N * (1 + w)) := by
  ring_nf at *
  omega

theorem header_net (F : Type) [Field F] [Fintype X] [Fintype D] [Fintype L] [Fintype T] [Fintype P]
    (len : (D → Bool) → ℕ) (src : B h → D → X ⊕ Bool) (srcLong : B h × Fin d → Long h → X ⊕ Bool)
    (read : RelayRead L r) (ctrl : Fin K → L → X ⊕ Bool)
    (sm : Address (2 ^ r) K → Short r → X ⊕ Bool) (out : Address (2 ^ r) K → Short n → X ⊕ Bool)
    (hcode : 2 * h + r ≤ n) (hout : n + 2 ≤ 4 * w) (layout : Long h ↪ T × P)
    (hj : w ≤ j) (hj' : j + 1 ≤ 2 * w) (hc : 3 ≤ cap) (ha : 2 * 2 ^ (2 * w) * (4 * w) ≤ cap)
    (hd : Fintype.card D + (r + 1) < j) (hL : j + 2 * h + 2 ≤ 4 * w)
    (hsize : 2 ^ h * d + K * (2 * 2 ^ r) ≤ 2 ^ j) (hdpos : 0 < d)
    (hz : Fintype.card L + 2 * ((2 * 2 ^ r) * Fintype.card P) < j) (ht : K * Fintype.card T ≤ 2 ^ j) :
    ∃ f : (X → Bool) → F, WideWeight F cap (SortTables F w) f (10 ^ 15 * (Fintype.card X + 2 ^ j * (1 + w))) ∧
      ∀ (x : X → Bool) (l : Inventory (2 ^ h) m d) (hs : ∀ i, size (l i) u ≤ 2 ^ r)
        (hk : bins l u (2 ^ r) ≤ K),
        (∀ i, len (Sum.elim x id ∘ src i) = counts l u i) →
        f x = if ∀ v, Sum.elim x id ∘ out v =
          merge hcode (delivered (portAnchor l u (2 ^ r) K (Nat.two_pow_pos r) hs hk) srcLong read ctrl x v)
            (Sum.elim x id ∘ sm v) then 1 else 0 := by
  let A := Address (2 ^ r) K
  let Y := A × Long h
  let get (a : A) (k : Long h) : (X ⊕ Y) ⊕ Bool := .inl (.inr (a, k))
  have hw : Fintype.card (Long h) = 2 * h := by simp [Long, two_mul]
  obtain ⟨t, ht₁, ht₂⟩ := port_relay (m := m) (u := u) F len (fun i => liftTap ∘ src i)
    (fun i => liftTap ∘ srcLong i) read (fun i => liftTap ∘ ctrl i) get layout hj hj' hc ha hd
    (by rwa [hw]) hsize hdpos hz ht
  have hnet := merge_net (F := F) hcode get (fun i => liftTap ∘ sm i) (fun i => liftTap ∘ out i)
  obtain ⟨f, hf, he⟩ := hide_unique hc ht₁ (of_weight hc hnet)
  refine ⟨f, ?_, fun x l hs hk hl => ?_⟩
  · intro a i
    obtain ⟨v, hv, net⟩ := hf a i
    refine ⟨v, hv.trans ?_, net⟩
    have hi : Fintype.card A ≤ 2 ^ j := by simp only [A, Address, Fintype.card_prod, Fintype.card_fin]; omega
    have hh : Fintype.card Y ≤ 2 ^ j * (4 * w) := by
      rw [show Fintype.card Y = Fintype.card A * Fintype.card (Long h) from Fintype.card_prod .., hw]
      exact Nat.mul_le_mul hi (by omega)
    rw [Fintype.card_sum]
    exact cost (Nat.two_pow_pos j) hh (Nat.mul_le_mul hi hout)
  let e := portAnchor l u (2 ^ r) K (Nat.two_pow_pos r) hs hk
  let values : Y → Bool := Function.uncurry (delivered e srcLong read ctrl x)
  have unique (y : Y → Bool) : t (Sum.elim x y) = if values = y then 1 else 0 := by
    rw [ht₂ _ l hs hk (by simpa only [read_lift_fun] using hl)]
    simp only [delivered_lift]
    congr 1
    exact propext ⟨fun h => funext fun ⟨i, j⟩ => (congrFun (h i) j).symm, by rintro rfl i; rfl⟩
  rw [he x values unique]
  simp only [written, read_lift_fun]
  rfl

end Channels
end OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
end

/-! # Coordinates of a terminal row layout -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Packing PackRows Coloring Assembly

structure Dimensions where
  /-- Logarithm of the original number of stacks. -/
  h : ℕ
  /-- Number of finest bundles per stack. -/
  b : ℕ
  /-- Number of stacks per row. -/
  q : ℕ
  /-- Half the row capacity in finest bundles. -/
  u : ℕ
  /-- Logarithm of the half-bin capacity in rows. -/
  r : ℕ
  /-- Bits per slice of a finest bundle. -/
  p : ℕ
  /-- Bin count. -/
  K : ℕ
  /-- Number of exterior channels per host. -/
  d : ℕ
  /-- Rows reserved per original exterior name. -/
  n : ℕ
  /-- Bit lengths of a paired internal identifier and an exterior name. -/
  a : ℕ
  e : ℕ
  width : q * b = 2 * u
  cover : n * q = 2 * 2 ^ h
  bpos : 0 < b
  qpos : 0 < q
  ppos : 0 < p

namespace Dimensions
variable (D : Dimensions) {F : Type} (S : Scheme F)

abbrev v := 2 ^ D.r
abbrev z := bundleSize D.v D.p
abbrev Addr := PackRows.Address D.v D.K
abbrev PortCount := 2 * 2 ^ S.d + D.d

abbrev StackBits := Fin D.b × Fin D.z
abbrev Label := Fin D.d × Cell D.h × Fin D.b
abbrev Source := Fin D.u → Option D.Label

abbrev ExteriorBits := Unit ⊕ (Fin D.q × Option (Fin D.h))
abbrev User := Channels.Short D.r ⊕ D.ExteriorBits
abbrev Names := Fin D.e
abbrev BinOutput := BinOut D.v D.u (2 ^ S.h) S.ℓ D.User
abbrev Decisions := (Fin D.K × D.BinOutput S) ⊕ (D.Addr × (Channels.Short D.a ⊕ D.Names))
abbrev Originals (x y : Wire) := (Stack.Outer x y × Cell D.h) × D.StackBits

theorem upos : 0 < D.u := by
  have h := D.width
  have := Nat.mul_pos D.qpos D.bpos
  omega

theorem zpos : 0 < D.z := Nat.mul_pos (by positivity) D.ppos

def cellCode : Cell D.h ↪ (Fin D.h → Bool) :=
  (Fintype.equivOfCardEq (by simp [Cell])).toEmbedding

end Dimensions
end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-!
# The assignment of endpoint bundles at the terminal stage

Each original stack carries a fixed number of consecutive finest
bundles. Only the local channel and stack key are needed on the
short record. Long exterior names are shared by a host's blocks.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent

open Assembly Coloring PackRows Classical

variable {F : Type} [Field F] {x y : Wire}

abbrev Dimensions.copies (D : Dimensions) := 2 ^ D.h * (D.b * D.z)

structure Assignment (D : Dimensions) (S : Scheme F) (G : Diagram F x y) where
  depth : ℕ
  state : Packing.HostNet F (Stack.fringe (copies x D.copies) (copies y D.copies)) depth D.z
  rows : S.format.obj
  post : S.Posting rows state
  capacity : ℕ
  holders : Stack.Holders G state capacity
  lane : B S.m → Stack.Outer x y → Fin D.d
  separate : ∀ i j a b, holders.core i a = holders.core j b →
    lane (post.host (holders.core i a)) i = lane (post.host (holders.core j b)) j → i = j
  reach : ∀ i, (Finset.univ.image (holders.core i)).card * D.q ≤ 2 ^ D.h
  strips : Strips (Exterior.ports post)

namespace Assignment
variable {D : Dimensions} {S : Scheme F} {G : Diagram F x y} (t : Assignment D S G)

abbrev inner := t.post.channels D.zpos
abbrev loc := t.holders.loc t.post.host t.post.block
abbrev outerCount := Exterior.lengths t.loc t.lane D.b
abbrev inventory := append t.inner.inventory t.outerCount

theorem inject_names (i j a b) (h : (t.loc i a).1 = (t.loc j b).1)
    (e : t.lane (t.loc i a).1 i = t.lane (t.loc j b).1 j) : i = j :=
  t.separate _ _ _ _ (t.post.host.injective h) e

theorem cap (i : Stack.Outer x y) :
    (Finset.univ.image fun s => (t.loc i s).1).card * D.q ≤ Fintype.card (Packing.Cell D.h) := by
  change (Finset.univ.image (t.post.host ∘ t.holders.core i)).card * D.q ≤ _
  rw [← Finset.image_image, Packing.card_cell]
  exact (Nat.mul_le_mul_right _ Finset.card_image_le).trans (t.reach i)

def external := (Exterior.addresses t.post t.holders t.lane D.zpos t.strips).choose

theorem ext_location (j : outer S t.rows D.z) :
    (t.external j).1 = j.val.1 ∧ (t.external j).2.1 = j.val.2.1 :=
  (Exterior.addresses t.post t.holders t.lane D.zpos t.strips).choose_spec.1 j

def pieces : Pieces S t.rows t.inventory D.v D.p :=
  t.post.pieces D.zpos (t.strips.uniform D.zpos) t.external t.ext_location

structure Fits : Prop where
  room : Pieces.Room (l := t.inventory) (u := D.u)
  position : ∀ i, size (t.inventory i) D.u ≤ D.v
  reserve : bins t.inventory D.u D.v ≤ D.K

variable (hw : t.Fits)

abbrev layout := make t.inventory D.u D.v D.K D.upos (by positivity) hw.room hw.position hw.reserve
abbrev index := t.pieces.index hw.room

def endpoint (i : Stack.Outer x y) (s : Packing.Cell D.h) (k : Fin D.b) : Endpoints t.inventory :=
  extendR _ _ (Exterior.point t.loc t.lane D.b ((i, s), k))

def coordinate (q : Endpoints t.inventory) : Fin D.u :=
  t.index hw q.1 q.2.1 q.2.2

def Registered (rows : B S.m → B S.h → D.Source) : Prop :=
  ∀ i j k c s b, rows i j k = some (c, s, b) ↔
    ∃ a : Stack.Outer x y, t.loc a s = (i, j) ∧ t.lane i a = c ∧ t.coordinate hw (t.endpoint a s b) = k

theorem end_bit (i : Stack.Outer x y) (s : Packing.Cell D.h) (k : Fin D.b) (j : Fin D.z) :
    t.pieces.slots (Exterior.ports t.post (((i, s), k), j)).val =
      (t.endpoint i s k, finProdFinEquiv.symm j) := by
  have e := (Exterior.addresses t.post t.holders t.lane D.zpos t.strips).choose_spec.2 ((i, s), k) j
  let u := t.external.symm (Exterior.point t.loc t.lane D.b ((i, s), k))
  change Exterior.ports t.post (((i, s), k), j) = toOuter t.pieces.uniform u j at e
  rw [e]
  unfold toOuter Pieces.slots
  simp only [Equiv.trans_apply, Equiv.symm_apply_apply, Equiv.prodCongr_apply, Prod.map]
  unfold pieces
  rw [t.post.pieces_outer _ _ _ _ u]
  simp only [u, Equiv.apply_symm_apply, endpoint]

end Assignment
end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end

/-!
# Canonical row decisions

Short descriptors stay within their bins. Host names and exterior
names follow the selected port anchors. The three parts of the tape
are functional, including every unused bit.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dimensions
open PackRows Coloring Assembly Classical

variable {F Z X : Type} (D : Dimensions) (S : Scheme F)

abbrev Description (Z : Type) := (Z → Bool) → Descriptor (2 ^ S.h) (D.PortCount S) S.ℓ
abbrev Extras (Z : Type) := (Z → Bool) → Fin D.d → Fin D.v → D.ExteriorBits → Bool
abbrev Group := B S.m × Fin (D.PortCount S)
abbrev Counts := Inventory (2 ^ S.m) (2 ^ S.h) (D.PortCount S)
abbrev CodeFits := 2 * S.m + D.r ≤ D.a

structure FitsControls (Z : Type) [Fintype Z] (w j cap t p : ℕ) : Prop where
  lower : w ≤ j
  upper : j + 1 ≤ 2 * w
  gates : 3 ≤ cap
  large : 2 * 2 ^ (2 * w) * (4 * w) ≤ cap
  desc : Fintype.card Z + (D.r + 1) < j
  short : Fintype.card (BinKey D.v Z) + Fintype.card (D.BinOutput S) < j
  hosts : j + 2 * S.m + 2 ≤ 4 * w
  names : j + D.e + 2 ≤ 4 * w
  slots : 2 ^ S.m * (D.PortCount S) + D.K * (2 * D.v) ≤ 2 ^ j
  code : D.CodeFits S
  head : D.a + 2 ≤ 4 * w
  hosts_fit : 2 * S.m ≤ t * p
  names_fit : D.e ≤ t * p
  slice : (2 * D.v) ^ 2 + 2 * (2 * D.v * p) < j
  slices : D.K * t ≤ 2 ^ j

def exteriorLane (j : Fin (D.PortCount S)) : Option (Fin D.d) :=
  if h : j.val < 2 * 2 ^ S.d then none else
    some ⟨j.val - 2 * 2 ^ S.d, by have := j.isLt; unfold PortCount at this; omega⟩

def flags (code : D.Description S Z) (user : D.Extras Z)
    (x : Z → Bool) (j : Fin (D.PortCount S)) (k : Fin D.v) : D.User → Bool :=
  Sum.elim (Channels.short (Channels.source (2 ^ S.d) D.d D.u D.v (code x).len j k.val))
    (fun z => (D.exteriorLane S j).elim false (fun p => user x p k z))

def longNames (s : S.format.obj) (p : D.Group S) : Channels.Long S.m → Bool :=
  Channels.long (Channels.names (fun i => (s i).1) p.1 p.2)

def extNames (names : B S.m → Fin D.d → D.Names → Bool) (p : D.Group S) : D.Names → Bool :=
  fun j => (D.exteriorLane S p.2).elim false (fun k => names p.1 k j)

def chooseBits {Y : Type} (f : Fin D.K → D.BinOutput S → Y) (i : Fin D.K)
    (p : Fin (2 * D.v) × Fin (2 * D.v)) : Y := f i (.inr (p.1, .inr (.inl p.2)))

def shortBits {Y : Type} (f : Fin D.K → D.BinOutput S → Y) (r : D.Addr)
    (j : Channels.Short D.r) : Y := f r.1 (.inr (r.2, .inr (.inr (.inl j))))

def fetch {Y : Type} (anc : D.Group S ↪ D.Addr) (b : Fin D.K → D.BinOutput S → Bool)
    (labels : D.Group S → Y → Bool) (i : D.Addr) (k : Y) : Bool :=
  (readIndex D.r (D.chooseBits S b i.1) i.2).elim false fun j =>
    Function.extend anc (fun a => labels a k) (fun _ => false) (i.1, j)

def decideRows (hn : D.CodeFits S) (code : D.Description S Z) (user : D.Extras Z)
    (sd : B S.m → Z → Bool) (r : S.format.obj) (ext : B S.m → Fin D.d → D.Names → Bool)
    (l : D.Counts S) (hs : ∀ i, size (l i) D.u ≤ D.v) (hk : bins l D.u D.v ≤ D.K) :
    D.Decisions S → Bool :=
  let a := anchor l D.u D.v D.K (Nat.two_pow_pos _) hs hk
  let b g := binFunction D.u code (D.flags S code user) (anchored a sd g)
  let e := portAnchor l D.u D.v D.K (Nat.two_pow_pos _) hs hk
  Sum.elim (Function.uncurry b) fun i =>
    Sum.elim (Channels.merge hn (D.fetch S e b (D.longNames S r) i.1) (D.shortBits S b i.1))
      (D.fetch S e b (D.extNames S ext) i.1) i.2

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dimensions
end

/-! # Checking the terminal decisions from short and long descriptors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dimensions
open PackRows Coloring Assembly Classical Transcript

variable {F Z X : Type} (D : Dimensions) (S : Scheme F)

private def hostTap (ts : S.format.pins → X ⊕ Bool) (a : D.Group S) : Channels.Long S.m → X ⊕ Bool :=
  let own := Sum.inr ∘ (Format.addr S.m).code a.1
  if h : a.2.val < 2 * 2 ^ S.d then
    let k := Channels.decodeLane ⟨a.2.val, h⟩
    let other j := ts (a.1, .inl (k.2, j))
    if k.1 then Sum.elim other own else Sum.elim own other
  else Sum.elim own own

private theorem hostTap_eq (ts : S.format.pins → X ⊕ Bool) (x : X → Bool) :
    (fun a => Sum.elim x id ∘ D.hostTap S ts a) =
      D.longNames S (S.format.code.symm (Sum.elim x id ∘ ts)) := by
  let r := S.format.code.symm (Sum.elim x id ∘ ts)
  have he (i : B S.m) (j : B S.d) (t : slots (word S.m)) :
      Sum.elim x id (ts (i, .inl (j, t))) = (Format.addr S.m).code ((r i).1 j) t :=
    (congrFun (S.format.code.apply_symm_apply (Sum.elim x id ∘ ts)) (i, .inl (j, t))).symm
  funext a t
  unfold hostTap longNames Channels.names
  by_cases h : a.2.val < 2 * 2 ^ S.d
  · simp only [dite_eq_left h]
    cases (Channels.decodeLane ⟨a.2.val, h⟩).1 <;> cases t <;> first | rfl | exact he _ _ _
  · simp only [dite_eq_right h]
    cases t <;> rfl

private def extTap (ext : B S.m → Fin D.d → D.Names → X ⊕ Bool) (p : D.Group S)
    (j : D.Names) : X ⊕ Bool :=
  (D.exteriorLane S p.2).elim (.inr false) (fun k => ext p.1 k j)

private theorem extTap_eq (ext : B S.m → Fin D.d → D.Names → X ⊕ Bool) (x : X → Bool) :
    (fun p => Sum.elim x id ∘ D.extTap S ext p) = D.extNames S (fun i j => Sum.elim x id ∘ ext i j) := by
  funext p k
  unfold extTap extNames
  simp only [Function.comp_apply]
  cases D.exteriorLane S p.2 <;> rfl

private theorem fetch_eq {Y : Type} (e : D.Group S ↪ D.Addr)
    (b : Fin D.K → D.BinOutput S → X ⊕ Bool) (src : D.Group S → Y → X ⊕ Bool) (x : X → Bool) :
    delivered e src (readIndex D.r) (D.chooseBits S b) x =
      D.fetch S e (fun i => Sum.elim x id ∘ b i) (fun p => Sum.elim x id ∘ src p) := rfl

private theorem tape_ok {A B C Y Z : Type} (b : A → B → Bool)
    (l : (A → B → Bool) → C → Y → Bool) (r : (A → B → Bool) → C → Z → Bool)
    (x : (A × B) ⊕ (C × (Y ⊕ Z)) → Bool) :
    let p i j := x (.inl (i, j))
    (∀ i, p i = b i) ∧ (∀ i, (fun j => x (.inr (i, .inl j))) = l p i) ∧
      (∀ i, (fun j => x (.inr (i, .inr j))) = r p i) ↔
        x = Sum.elim (Function.uncurry b) (fun i => Sum.elim (l b i.1) (r b i.1) i.2) := by
  intro p
  constructor
  · rintro ⟨a, h, k⟩
    rw [funext a] at h k
    funext i
    rcases i with ⟨i, j⟩ | ⟨i, j|j⟩
    · exact congrFun (a i) j
    · exact congrFun (h i) j
    · exact congrFun (k i) j
  · rintro rfl
    exact ⟨fun _ => rfl, fun _ => rfl, fun _ => rfl⟩

variable [Field F] [Fintype X] [Fintype Z] {w j cap t p : ℕ} (h : D.FitsControls S Z w j cap t p)
    (ts : S.format.pins → X ⊕ Bool) (ext : B S.m → Fin D.d → D.Names → X ⊕ Bool)
    (sd : B S.m → Z → X ⊕ Bool) (dst : D.Decisions S → X ⊕ Bool)
    (code : D.Description S Z) (user : D.Extras Z)

theorem controls_net :
    ∃ f : (X → Bool) → F, WideWeight F cap (SortTables F w) f (10 ^ 16 * (Fintype.card X + 2 ^ j * (1 + w))) ∧
      ∀ (x : X → Bool) (l : D.Counts S) (hs : ∀ i, size (l i) D.u ≤ D.v) (hk : bins l D.u D.v ≤ D.K),
        (∀ i, (code (Sum.elim x id ∘ sd i)).len = l i) →
        f x = if Sum.elim x id ∘ dst = D.decideRows S h.code code user (fun i => Sum.elim x id ∘ sd i)
          (S.format.code.symm (Sum.elim x id ∘ ts)) (fun i j => Sum.elim x id ∘ ext i j) l hs hk
          then 1 else 0 := by
  let len x := size (code x).len D.u
  let b i j := dst (.inl (i, j))
  let head i j := dst (.inr (i, .inl j))
  let name i j := dst (.inr (i, .inr j))
  let read := readIndex D.r
  let ctrl := D.chooseBits S b
  have hp : 0 < D.PortCount S := by unfold PortCount; positivity
  have hsize : 2 ^ S.m + D.K * D.v ≤ 2 ^ j :=
    (Nat.add_le_add (Nat.le_mul_of_pos_right _ hp) (Nat.mul_le_mul_left _ (by omega))).trans h.slots
  have hsli : Fintype.card (Fin (2 * D.v) × Fin (2 * D.v)) + 2 * ((2 * D.v) * Fintype.card (Fin p)) < j := by
    simpa [pow_two] using h.slice
  have ht : D.K * Fintype.card (Fin t) ≤ 2 ^ j := by simpa using h.slices
  obtain ⟨a, ha, ea⟩ := bin_service F len code (D.flags S code user) sd b h.lower h.upper h.gates h.large
    h.desc hsize h.short
  obtain ⟨e₁⟩ : Nonempty (Channels.Long S.m ↪ Fin t × Fin p) :=
    Function.Embedding.nonempty_of_card_le (by simpa [Channels.Long, two_mul] using h.hosts_fit)
  obtain ⟨g, hg, eg⟩ := Channels.header_net (m := 2 ^ S.h) (u := D.u) F len sd (D.hostTap S ts)
    read ctrl (D.shortBits S b) head h.code h.head e₁ h.lower h.upper h.gates h.large
    h.desc h.hosts h.slots hp hsli ht
  obtain ⟨e₂⟩ : Nonempty (D.Names ↪ Fin t × Fin p) :=
    Function.Embedding.nonempty_of_card_le (by simpa [Names] using h.names_fit)
  obtain ⟨k, hk, ek⟩ := port_relay (m := 2 ^ S.h) (u := D.u) F len sd (D.extTap S ext)
    read ctrl name e₂ h.lower h.upper h.gates h.large h.desc (by simpa [Names] using h.names)
    h.slots hp hsli ht
  have net := wide_mul h.gates ha (wide_mul h.gates hg hk)
  refine ⟨fun x => a x * (g x * k x), ?_, fun x l hs hr he => ?_⟩
  · intro a i
    obtain ⟨s, hv, hv'⟩ := net a i
    exact ⟨s, hv.trans (by omega), hv'⟩
  have hl (i) : len (Sum.elim x id ∘ sd i) = counts l D.u i := by unfold len counts; rw [he]
  change a x * (g x * k x) = _
  rw [ea _ l hs hr hl, eg _ l hs hr hl, ek _ l hs hr hl]
  simp only [read, ctrl, D.fetch_eq, D.hostTap_eq, D.extTap_eq, ite_mul, one_mul, zero_mul, ← ite_and]
  let e := portAnchor l D.u D.v D.K (Nat.two_pow_pos _) hs hr
  let left y i := Channels.merge h.code
    (D.fetch S e y (D.longNames S (S.format.code.symm (Sum.elim x id ∘ ts))) i) (D.shortBits S y i)
  let right y := D.fetch S e y (D.extNames S (fun i j => Sum.elim x id ∘ ext i j))
  congr 1
  exact propext (tape_ok _ left right (Sum.elim x id ∘ dst))

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.Dimensions
end

/-! # Reading the controls at an allocated port row -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows

variable {Z A : Type} {H u K m d ℓ r : ℕ} {code : (Z → Bool) → Descriptor m d ℓ}
    {l : Inventory H m d} {hs : ∀ i, size (l i) u ≤ 2 ^ r} {hk : bins l u (2 ^ r) ≤ K}
    {ix : Index l u} {f : Label H m ℓ} {src : Fin H → Z → Bool}
    {inp : Fin K → BinKey (2 ^ r) Z → Bool} (b : BinData code l u (2 ^ r) K (Nat.two_pow_pos _) hs hk ix f src inp)
    (flags : (Z → Bool) → Fin d → Fin (2 ^ r) → A → Bool)
    (hu : 0 < u) (ha : ∀ i j, arity (l i) j ≤ u)

local notation "arr" => make l u (2 ^ r) K hu (Nat.two_pow_pos r) ha hs hk
local notation "anc" => portAnchor l u (2 ^ r) K (Nat.two_pow_pos r) hs hk

include b in
theorem BinData.user_at (p : PortRows l u) (a : A) :
    let i := (arr).portLoc p
    binFunction u code flags (inp i.1) (.inr (i.2, .inr (.inr a))) =
      flags (src p.1) p.2.1 (p.2.2.castLE (ports_le hs ..)) a := by
  intro i
  apply Bool.eq_iff_iff.mpr
  rw [b.user flags hu ha]
  constructor
  · rintro ⟨p', h, k, hk', hw⟩
    have := (arr).portLoc.injective h
    subst p'
    rw [show k = p.2.2.castLE (ports_le hs ..) from Fin.ext hk'] at hw
    exact hw
  · exact fun hh => ⟨p, rfl, _, rfl, hh⟩

include b in
theorem BinData.user_off (i : Address (2 ^ r) K) (hi : i ∉ Set.range (arr).portLoc) (a : A) :
    binFunction u code flags (inp i.1) (.inr (i.2, .inr (.inr a))) = false := by
  apply Bool.eq_false_iff.mpr
  intro h
  obtain ⟨p, hp, _⟩ := (b.user flags hu ha i a).mp h
  exact hi ⟨p, hp⟩

include b in
theorem BinData.read_port (p : PortRows l u) :
    let i := (arr).portLoc p
    readIndex r (fun y => binFunction u code flags (inp i.1) (.inr (y.1, .inr (.inl y.2)))) i.2 =
      some ((anc) (p.1, p.2.1)).2 := by
  intro i
  refine readIndex_eq (fun k => ?_)
  rw [b.choose flags hu ha]
  exact ⟨fun ⟨q, hq, eq⟩ => (arr).portLoc.injective hq ▸ eq, fun h => ⟨p, rfl, h⟩⟩

include b in
theorem BinData.read_off (i : Address (2 ^ r) K) (hi : i ∉ Set.range (arr).portLoc) :
    readIndex r (fun y => binFunction u code flags (inp i.1) (.inr (y.1, .inr (.inl y.2)))) i.2 = none := by
  apply dite_eq_right
  rintro ⟨j, hj⟩
  obtain ⟨p, hp, _⟩ := (b.choose flags hu ha i j).mp hj
  exact hi ⟨p, hp⟩

end OAI.LinearAlgebra.MatrixExponent.BatchDescent.PackRows
end

/-! # Interpreting the decisions for a registered placement -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.BatchDescent
open Assembly PackRows Coloring Classical

namespace Dimensions

variable {F Z Y : Type} {D : Dimensions} {S : Scheme F}
    {l : D.Counts S} {hs : ∀ i, size (l i) D.u ≤ D.v} {hk : bins l D.u D.v ≤ D.K}
    {code : D.Description S Z} {ix : Index l D.u} {f : PackRows.Label (2 ^ S.m) (2 ^ S.h) S.ℓ}
    {sd : B S.m → Z → Bool} {inp : Fin D.K → BinKey D.v Z → Bool}
    (data : BinData code l D.u D.v D.K (Nat.two_pow_pos _) hs hk ix f sd inp)
    (user : D.Extras Z) (ha : ∀ i j, arity (l i) j ≤ D.u)

local notation "out" => (fun g => binFunction D.u code (D.flags S code user) (inp g))
local notation "arr" => make l D.u D.v D.K D.upos (Nat.two_pow_pos _) ha hs hk
local notation "anc" => portAnchor l D.u D.v D.K (Nat.two_pow_pos _) hs hk

include data in
private theorem fetch_at (y : D.Group S → Y → Bool) (p : PortRows l D.u) :
    D.fetch S anc out y ((arr).portLoc p) = y (p.1, p.2.1) := by
  let i := (arr).portLoc p
  have hb : i.1 = ((anc) (p.1, p.2.1)).1 := rfl
  have hr : readIndex D.r (D.chooseBits S out i.1) i.2 = some ((anc) (p.1, p.2.1)).2 :=
    data.read_port (D.flags S code user) D.upos ha p
  funext k
  change D.fetch S anc out y i k = _
  rw [fetch, hr, Option.elim_some, hb, Prod.mk.eta, (anc).injective.extend_apply]

include data in
private theorem fetch_off (y : D.Group S → Y → Bool) (i : D.Addr) (h : i ∉ Set.range (arr).portLoc) :
    D.fetch S anc out y i = fun _ => false := by
  have hr : readIndex D.r (D.chooseBits S out i.1) i.2 = none :=
    data.read_off (D.flags S code user) D.upos ha i h
  funext k
  rw [fetch, hr, Option.elim_none]

end Dimensions

namespace Assignment

variable {F Z : Type} [Field F] {x y : Wire} {S : Scheme F} {D : Dimensions} {G : Diagram F x y}
    (t : Assignment D S G) (hw : t.Fits) (hc : D.CodeFits S) (user : D.Extras Z) (sd : B S.m → Z → Bool)
    (ext : B S.m → Fin D.d → D.Names → Bool)

structure Observed (v : D.Decisions S → Bool) : Prop where
  moves : ∀ i b, v (.inl (i, .inl b)) = (t.layout hw).moves i b
  format : ∀ i b, v (.inl (i.1, .inr (i.2, .inl b))) = (t.layout hw).format (t.index hw) (labels S t.rows) i b
  head : ∀ i b, v (.inr (i, .inl b)) =
    MatrixExponent.bits (word (D.a + 2)) (t.inner.header (t.layout hw) hw.position (Channels.code hc) i) b
  flags : ∀ (a : PortRows t.inventory D.u) b, let i := (t.layout hw).portLoc a
    v (.inl (i.1, .inr (i.2, .inr (.inr (.inr b))))) =
      (D.exteriorLane S a.2.1).elim false
        (fun k => user (sd a.1) k (a.2.2.castLE (ports_le hw.position ..)) b)
  name : ∀ (a : PortRows t.inventory D.u) b,
    v (.inr ((t.layout hw).portLoc a, .inr b)) = D.extNames S ext (a.1, a.2.1) b
  flags_off : ∀ i ∉ Set.range (t.layout hw).portLoc, ∀ b,
    v (.inl (i.1, .inr (i.2, .inr (.inr (.inr b))))) = false
  name_off : ∀ i ∉ Set.range (t.layout hw).portLoc, ∀ b, v (.inr (i, .inr b)) = false

theorem observed (code : D.Description S Z)
    (hlen : ∀ i, (code (sd i)).len = t.inventory i)
    (hlabel : ∀ i, (code (sd i)).label = labels S t.rows i)
    (hslot : ∀ i j p (k : Fin (t.inventory i j p)),
      (code (sd i)).slot j p k.val = (t.index hw i j ⟨p, k⟩).val) :
    t.Observed hw hc user sd ext
      (D.decideRows S hc code user sd t.rows ext t.inventory hw.position hw.reserve) := by
  let flags := D.flags S code user
  let a := anchor t.inventory D.u D.v D.K (Nat.two_pow_pos _) hw.position hw.reserve
  let e := portAnchor t.inventory D.u D.v D.K (Nat.two_pow_pos _) hw.position hw.reserve
  let b (g) := binFunction D.u code flags (anchored a sd g)
  let L := t.layout hw
  have data := BinData.anchored (Nat.two_pow_pos _) hw.position hw.reserve hlen hlabel hslot
  have atPort (p : PortRows t.inventory D.u) (j : D.User) :
      b (L.portLoc p).1 (.inr ((L.portLoc p).2, .inr (.inr j))) =
        flags (sd p.1) p.2.1 (p.2.2.castLE (ports_le hw.position ..)) j :=
    data.user_at flags D.upos hw.room p j
  have offPort (i : D.Addr) (h : i ∉ Set.range L.portLoc) (j : D.User) :
      b i.1 (.inr (i.2, .inr (.inr j))) = false := data.user_off flags D.upos hw.room i h j
  refine ⟨data.moves flags D.upos hw.room, data.format flags D.upos hw.room,
    ?_, ?_, ?_, ?_, ?_⟩
  · intro i k
    change Channels.merge hc (D.fetch S e b (D.longNames S t.rows) i) (D.shortBits S b i) k =
      MatrixExponent.bits (word (D.a + 2)) (t.inner.header L hw.position (Channels.code hc) i) k
    by_cases hi : i ∈ Set.range L.portLoc
    · obtain ⟨p, rfl⟩ := hi
      have hlong : D.fetch S e b (D.longNames S t.rows) (L.portLoc p) =
          Channels.long (Channels.names (fun i => (t.rows i).1) p.1 p.2.1) :=
        Dimensions.fetch_at data user hw.room _ p
      have hshort : D.shortBits S b (L.portLoc p) = Channels.short
          (Channels.source (2 ^ S.d) D.d D.u D.v (t.inventory p.1) p.2.1 p.2.2.val) := by
        funext j
        have he := atPort p (.inl j)
        simpa only [Dimensions.shortBits, flags, Dimensions.flags, Sum.elim_inl, hlen, Fin.val_castLE] using he
      rw [hlong, hshort, Channels.merge_eq]
      obtain ⟨i, j, r⟩ := p
      rw [t.post.header_eq_fill D.zpos L hw.position (Channels.code hc) D.upos]
    · have hshort : D.shortBits S b i = Channels.short none := funext fun j => offPort i hi (.inl j)
      rw [hshort, Channels.merge_none, t.inner.header_absent L hw.position (Channels.code hc) i hi]
  · exact fun p j => atPort p (.inr j)
  · exact fun p j => congrFun (Dimensions.fetch_at data user hw.room (D.extNames S ext) p) j
  · exact fun i hi j => offPort i hi (.inr j)
  · exact fun i hi j => congrFun (Dimensions.fetch_off data user hw.room (D.extNames S ext) i hi) j

end Assignment
end OAI.LinearAlgebra.MatrixExponent.BatchDescent
end
