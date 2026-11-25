import OAI.LinearAlgebra.MatrixExponent.Spectral.Path
import OAI.LinearAlgebra.MatrixExponent.Install.Products
import OAI.LinearAlgebra.MatrixExponent.Routing.GeometryComparison
import OAI.LinearAlgebra.MatrixExponent.Routing.Fixed

/-!
# Binary presentations with named local ports

The tensor semiring forgets local coordinates. A binary presentation
retains them, so the cost of a restriction can be counted.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol

open Spectral

structure Binary (K S : Type) where
  port : S → Type
  [finitePort : ∀ s, Fintype (port s)]
  value : (∀ s, port s → Bool) → K

attribute [instance] Binary.finitePort

namespace Binary

variable {K S : Type} [Field K] [Fintype S] [Nonempty S]
open Classical

abbrev Assign (D : Binary K S) := ∀ s, D.port s → Bool

def raw (D : Binary K S) : Raw K S := Raw.ofTable _ D.value

def tensor (D : Binary K S) : Tensor K S := Tensor.ofRaw D.raw

def batch (n : ℕ) (D : Binary K S) : Binary K S where
  port s := Fin n × D.port s
  value x := ∏ i, D.value (fun s j => x s (i, j))

def product {I : Type} [Fintype I] (D : I → Binary K S) : Binary K S where
  port s := Σ i, (D i).port s
  value x := ∏ i, (D i).value (fun s j => x s ⟨i, j⟩)

abbrev Action (D V : Binary K S) := ∀ s, (D.port s → Bool) → (V.port s → Bool) → K

def act (D V : Binary K S) (k : Action D V) (x : D.Assign) : K :=
  ∑ y : V.Assign, (∏ s, k s (x s) (y s)) * V.value y

theorem applyLocal (D V : Binary K S) (k : Action D V) (x : D.Assign) :
    Raw.applyLocal (B := D.raw) V.raw k x = act D V k x := by
  refine (Raw.expand V.raw (fun s => k s (x s))).trans ?_
  apply Finset.sum_congr rfl
  intro y _
  exact congrArg _ (Raw.coeff_ofTable _ V.value y)

theorem sum_action {I : Type} [Fintype I] (D : Binary K S) (V : I → Binary K S) :
    D.tensor ≤ ∑ i, (V i).tensor ↔
      ∃ k : ∀ i, Action D (V i), ∀ x, D.value x = ∑ i, act D (V i) (k i) x := by
  unfold tensor
  rw [Raw.restriction_sum_iff]
  constructor
  · rintro ⟨k, hk⟩
    refine ⟨k, fun x => (Raw.coeff_ofTable _ D.value x).symm.trans ((hk x).trans ?_)⟩
    exact Finset.sum_congr rfl fun i _ => applyLocal D (V i) (k i) x
  · rintro ⟨k, hk⟩
    refine ⟨k, fun x => (Raw.coeff_ofTable _ D.value x).trans ((hk x).trans ?_)⟩
    exact Finset.sum_congr rfl fun i _ => (applyLocal D (V i) (k i) x).symm

theorem single_action (D V : Binary K S) :
    D.tensor ≤ V.tensor ↔ ∃ k : Action D V, ∀ x, D.value x = act D V k x := by
  have h := sum_action D (fun _ : Unit => V)
  simp only [Fintype.sum_unique] at h
  exact h.trans ⟨fun ⟨k, hk⟩ => ⟨k (), hk⟩, fun ⟨k, hk⟩ => ⟨fun _ => k, hk⟩⟩

end Binary
end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-!
# Implementing restrictions on bit arrays at all dyadic widths

The constant may depend on the two presentations and the finite
branch alphabet. It does not depend on the dyadic width.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol.Binary

open Spectral Install Classical

variable {K S A : Type} [Field K] [Fintype S] [Nonempty S] [Fintype A]
  (D V : Binary K S)

def rows (n : ℕ) : (batch n D).Assign ≃ (Fin n → D.Assign) where
  toFun x i s j := x s (i, j)
  invFun x s p := x p.1 s p.2
  left_inv _ := rfl
  right_inv _ := rfl

def diagonalAction (k : Action D V) (n : ℕ) : Action (batch n D) (batch n V) :=
  fun s x y => ∏ i, k s (fun j => x (i, j)) (fun j => y (i, j))

omit [Nonempty S] in
theorem diagonal_act (k : Action D V) (n : ℕ) (x : (batch n D).Assign) :
    act _ _ (diagonalAction D V k n) x = ∏ i, act D V k (rows D n x i) := by
  unfold act
  rw [Fintype.prod_sum, ← (rows V n).sum_comp]
  apply Finset.sum_congr rfl
  intro y _
  rw [Finset.prod_mul_distrib]
  apply congrArg₂ (· * ·) _ rfl
  unfold diagonalAction
  exact Finset.prod_comm

def Cheap (k : Action D V) (c : ℕ) : Prop :=
  ∀ s, Weight K (fun x : D.port s ⊕ V.port s → Bool => k s (x ∘ Sum.inl) (x ∘ Sum.inr)) c

def scale (h : ℕ) : ℕ := 2 ^ h * (h + 1) ^ 3

def Scalable (D : Binary K S) (V : A → Binary K S) : Prop :=
  ∃ c : ℕ, ∀ h : ℕ, ∃ k : ∀ i, Action (batch (2 ^ h) D) (batch (2 ^ h) (V i)),
    (∀ i, Cheap _ _ (k i) (c * scale h)) ∧
      ∀ x, (batch (2 ^ h) D).value x = ∑ i, act _ _ (k i) x

omit [Fintype S] [Nonempty S] in
theorem Cheap.mono {D V : Binary K S} {k : Action D V} {b c : ℕ} (hk : Cheap D V k b) (hc : b ≤ c) :
    Cheap D V k c := fun s => (hk s).mono hc

def size (D : Binary K S) : ℕ := ∑ s, Fintype.card (D.port s)

omit [Field K] [Nonempty S] in
theorem card_le (s : S) : Fintype.card (D.port s) ≤ size D :=
  Finset.single_le_sum (f := fun s => Fintype.card (D.port s)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ s)

omit [Nonempty S] in
theorem diagonal_cheap (k : Action D V) (h : ℕ) :
    Cheap _ _ (diagonalAction D V k (2 ^ h)) ((8 * 2 ^ (D.size + V.size)) * scale h) := by
  intro s
  let f := fun x : D.port s ⊕ V.port s → Bool => k s (x ∘ Sum.inl) (x ∘ Sum.inr)
  have H := ((Weight.dense K _ f).prod h).rename
    (Equiv.prodSumDistrib (Fin (2 ^ h)) (D.port s) (V.port s))
  refine H.mono ?_
  rw [Fintype.card_sum, mul_comm (2 ^ h)]
  unfold scale
  gcongr
  · exact D.card_le s
  · exact V.card_le s
  · exact Nat.le_mul_of_pos_right _ (by positivity)

end OAI.LinearAlgebra.MatrixExponent.Protocol.Binary
end

/-! # Tensor products on disjoint families of named bit positions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol.Binary

open Spectral Classical

variable {K S : Type} [Field K] [Fintype S] [Nonempty S]

def of {X : Type} [Fintype X] (f : (S → X → Bool) → K) : Binary K S :=
  ⟨fun _ => X, f⟩

def join (D V : Binary K S) : Binary K S where
  port s := D.port s ⊕ V.port s
  value x := D.value (fun s j => x s (.inl j)) * V.value (fun s j => x s (.inr j))

theorem raw_coeff (D : Binary K S) (x : ∀ s, D.raw.leg s) : D.raw.coeff x = D.value x :=
  Raw.coeff_ofTable _ D.value x

theorem tensor_of_join (D V : Binary K S) : (D.join V).tensor = D.tensor * V.tensor := by
  apply Tensor.ofRaw_eq
  refine Raw.equiv_coeff (fun s => Equiv.sumArrowEquivProdArrow _ _ Bool) fun x => ?_
  rw [Raw.coeff_mul]
  simp only [raw_coeff]
  rfl

theorem tensor_relabel {D V : Binary K S} (e : ∀ s, V.port s ≃ D.port s)
    (h : ∀ x, D.value x = V.value (fun s j => x s (e s j))) : D.tensor = V.tensor := by
  apply Tensor.ofRaw_eq
  refine Raw.equiv_coeff (fun s => (e s).symm.arrowCongr (Equiv.refl Bool)) fun x => ?_
  simp only [raw_coeff]
  exact h x

private def splitPorts {I : Type} (P : Option I → Type) :
    P none ⊕ (Σ i, P (some i)) ≃ Σ i, P i where
  toFun := Sum.elim (fun j => ⟨none, j⟩) (fun z => ⟨some z.1, z.2⟩)
  invFun
    | ⟨none, j⟩ => .inl j
    | ⟨some i, j⟩ => .inr ⟨i, j⟩
  left_inv := by rintro (x | ⟨i, x⟩) <;> rfl
  right_inv := by rintro ⟨_ | i, x⟩ <;> rfl

theorem tensor_of_product {I : Type} [Fintype I] (D : I → Binary K S) :
    (product D).tensor = ∏ i, (D i).tensor := by
  refine Fintype.induction_empty_option
    (P := fun T => ∀ (D : T → Binary K S), (product D).tensor = ∏ i, (D i).tensor)
    ?_ ?_ ?_ I D
  · intro A B _ e ih V
    let := Fintype.ofEquiv B e.symm
    rw [← e.prod_comp (fun i => (V i).tensor), ← ih (fun i => V (e i))]
    refine tensor_relabel (fun s => Equiv.sigmaCongrLeft (β := fun i => (V i).port s) e) ?_
    exact fun x => (e.prod_comp (fun i => (V i).value (fun s j => x s ⟨i, j⟩))).symm
  · intro V
    rw [Finset.prod_of_isEmpty]
    apply Tensor.ofRaw_eq
    refine Raw.equiv_coeff (fun s =>
      Equiv.ofUnique ((Σ i, (V i).port s) → Bool) Unit) fun x => ?_
    rw [raw_coeff]
    change (∏ i, (V i).value (fun s j => x s ⟨i, j⟩)) = ∑ _ : Unit, ∏ _ : S, (1 : K)
    simp
  · intro A _ ih V
    rw [Fintype.prod_option, ← ih (fun i => V (some i)), ← tensor_of_join]
    refine tensor_relabel (fun s => splitPorts (fun i => (V i).port s)) ?_
    exact fun x => Fintype.prod_option (fun i => (V i).value (fun s j => x s ⟨i, j⟩))

theorem tensor_of_batch (D : Binary K S) (n : ℕ) : (D.batch n).tensor = D.tensor ^ n := by
  calc
    _ = (product (fun _ : Fin n => D)).tensor :=
      tensor_relabel (fun s => Equiv.sigmaEquivProd _ _) (fun _ => rfl)
    _ = _ := by rw [tensor_of_product]; simp

end OAI.LinearAlgebra.MatrixExponent.Protocol.Binary
end

/-! # Local operators on bundles of dyadic width -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol

open Classical

abbrev Lines (h : ℕ) (X : Type) := X → Fin (2 ^ h) → Bool

abbrev Frame (K X Y : Type) := ∀ h, Lines h X → Lines h Y → K

namespace Frame

variable {K X Y Z U V I : Type} [Field K]

def weight (f : Frame K X Y) (h : ℕ) (x : (X ⊕ Y) × Fin (2 ^ h) → Bool) : K :=
  f h (fun i k => x (.inl i, k)) (fun j k => x (.inr j, k))

def Fast (f : Frame K X Y) : Prop :=
  ∃ c : ℕ, ∀ h : ℕ, Install.Weight K (weight f h) (c * Binary.scale h)

def pull (f : Frame K X Y) (i : X → U) (j : Y → V) : Frame K U V :=
  fun h x y => f h (x ∘ i) (y ∘ j)

def product [Fintype I] (f : I → Frame K X Y) : Frame K X Y :=
  fun h x y => ∏ i, f i h x y

def compose [Fintype Y] (f : Frame K X Y) (g : Frame K Y Z) : Frame K X Z :=
  fun h x z => ∑ y, f h x y * g h y z

def diagonal (k : (X → Bool) → (Y → Bool) → K) : Frame K X Y :=
  fun _h x y => ∏ i, k (fun j => x j i) (fun j => y j i)

def keep (K X : Type) [Field K] : Frame K X X :=
  fun _ x y => if x = y then 1 else 0

end Frame
end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Exact branch indices of a scheduled inventory reduction -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol

open Routing

variable {I E : Type} [DecidableEq I] (L : Finset I) (Q : (I → ℕ) → Intervention I E)

abbrev Branch : ℕ → (I → ℕ) → Type
  | 0, _ => Unit
  | k + 1, z => Σ j : (Q z).choice, Branch k ((Q z).next z j + Stock.copies L 1)

instance finiteBranch : (k : ℕ) → (z : I → ℕ) → Fintype (Branch L Q k z)
  | 0, _ => inferInstanceAs (Fintype Unit)
  | k + 1, z =>
    letI : ∀ j, Fintype (Branch L Q k ((Q z).next z j + Stock.copies L 1)) := fun _ => finiteBranch k _
    inferInstanceAs (Fintype (Σ j : (Q z).choice, Branch L Q k ((Q z).next z j + Stock.copies L 1)))

variable [Fintype I] (Y : I → E → ℕ)

/-- Install the current round's core links before the remaining links.
The terminal supplies for each remaining request are paid separately. -/
def edges : (k : ℕ) → (z : I → ℕ) → Branch L Q k z → E → ℕ
  | 0, z, _ => fun e => ∑ i, Y i e * z i
  | k + 1, z, p => (Q z).core p.1 + edges k ((Q z).next z p.1 + Stock.copies L 1) p.2

theorem edges_cost [Fintype E] {a : I → ℝ} (hc : ∀ i, (∑ e, Y i e : ℕ) ≤ a i)
    {B v : ℝ} {k : ℕ} {z : I → ℕ} (h : Runs L a Q B k z v) (p : Branch L Q k z) :
    v + (∑ e, edges L Q Y k z p e : ℕ) ≤ B := by
  induction k generalizing v z with
  | zero =>
    change v + Stock.total a z ≤ B at h
    refine le_trans ?_ h
    simp only [edges, Finset.sum_comm (s := (Finset.univ : Finset E)), ← Finset.sum_mul,
      Nat.cast_sum, Nat.cast_mul, Stock.total]
    apply add_le_add le_rfl
    apply Finset.sum_le_sum
    intro i _
    rw [mul_comm, ← Nat.cast_sum]
    exact mul_le_mul_of_nonneg_left (hc i) (Nat.cast_nonneg _)
  | succ k ih =>
    have hs := ih (h.2 p.1) p.2
    simpa only [edges, Pi.add_apply, Finset.sum_add_distrib, Nat.cast_add, Intervention.cost,
      add_assoc] using hs

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Addressing the copies of a substitution -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol.Layout

open Routing.WordSum

variable {S A X Y : Type} {m z n : ℕ}

def row (hn : n = m * z) : Fin z × Fin m ≃ Fin n :=
  finProdFinEquiv.trans (finCongr (by rw [hn, Nat.mul_comm]))

def addresses (t : A → ℕ) (z : ℕ) : Fin z × Address 1 t ≃ Address z t where
  toFun p := ⟨p.2.1, row (by simp) (p.1, p.2.2)⟩
  invFun p :=
    let yz := (row (m := t p.1 * 1) (z := z) (by simp)).symm p.2
    (yz.1, ⟨p.1, yz.2⟩)
  left_inv p := by obtain ⟨k, a, i⟩ := p; simp
  right_inv p := by obtain ⟨a, i⟩ := p; simp

variable (hn : n = m * z) (t : A → ℕ)

abbrev InPorts (X : Type) (m z : ℕ) := Fin z × (Fin m × X)
abbrev OutPorts (Y : Type) (t : A → ℕ) (m z : ℕ) :=
  Fin z × ((Fin m × A) ⊕ (Σ _ : Address 1 t, Y))

def input (x : InPorts X m z → Bool) (i : Fin n) (j : X) :=
  x (((row hn).symm i).1, ((row hn).symm i).2, j)

def code (x : OutPorts Y t m z → Bool) (i : Fin n) (j : A) :=
  x (((row hn).symm i).1, .inl (((row hn).symm i).2, j))

def supply (x : OutPorts Y t m z → Bool) (i : Address z t) (j : Y) :=
  x (((addresses t z).symm i).1, .inr ⟨((addresses t z).symm i).2, j⟩)

def assemble (u : Fin n → S → A → Bool) (v : Address z t → S → Y → Bool)
    (s : S) (p : OutPorts Y t m z) : Bool :=
  Sum.elim (fun k => u (row hn (p.1, k.1)) s k.2)
    (fun k => v (addresses t z (p.1, k.1)) s k.2) p.2

theorem code_assemble (u : Fin n → S → A → Bool) (v : Address z t → S → Y → Bool) (s : S) :
    code hn t (assemble hn t u v s) = fun i => u i s := by
  funext i j
  simp [code, assemble]

theorem supply_assemble (u : Fin n → S → A → Bool) (v : Address z t → S → Y → Bool) (s : S) :
    supply t (assemble hn t u v s) = fun i => v i s := by
  funext i j
  simp [supply, assemble]

def joined :
    (Fin n → S → A → Bool) × (Address z t → S → Y → Bool) ≃ (S → OutPorts Y t m z → Bool) where
  toFun p := assemble hn t p.1 p.2
  invFun f := (fun i s => code hn t (f s) i, fun j s => supply t (f s) j)
  left_inv p := by simp only [code_assemble, supply_assemble]
  right_inv f := by
    funext s ⟨k, p⟩
    rcases p with ⟨i, j⟩ | ⟨i, j⟩ <;> simp [assemble, code, supply]

end OAI.LinearAlgebra.MatrixExponent.Protocol.Layout
end

/-!
# Supplies for a fixed rounded histogram

The selector is encoded by one indicator bit per letter. Its tensor
is still bounded by the size of the alphabet, since only valid words
occur and all sites see the same word.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol

open Spectral Routing.WordSum Classical Finset

variable {K S A X Y : Type} [Field K] [Fintype S] [Nonempty S]
  [Fintype A] [DecidableEq A] [Fintype X] [Fintype Y]

def encode (a b : A) : Bool := decide (a = b)

def decode (a₀ : A) (x : A → Bool) : A :=
  if h : ∃ a, x a = true then h.choose else a₀

@[simp] theorem decode_encode (a₀ a : A) : decode a₀ (encode a) = a := by
  have h : ∃ b, encode a b = true := ⟨a, by simp [encode]⟩
  rw [decode, dite_eq_left h]
  exact (of_decide_eq_true h.choose_spec).symm

private theorem prod_delta {I Z : Type} [Fintype I] [DecidableEq Z] (x y : I → Z) :
    (∏ i, if x i = y i then (1 : K) else 0) = if x = y then 1 else 0 := by
  by_cases h : x = y
  · simp [h]
  rw [ite_eq_right h]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp h
  exact prod_eq_zero (mem_univ i) (ite_eq_right hi)

def selector (K S A : Type) [Field K] [Fintype S] [Fintype A] [DecidableEq A] : Binary K S :=
  Binary.of (fun x : S → A → Bool => ∑ a, if x = fun _ => encode a then 1 else 0)

theorem selector_bound : (selector K S A).tensor ≤ (Fintype.card A : Tensor K S) := by
  rw [← Tensor.diag_eq_natCast A]
  change (Raw.diag K S A).Restricts (selector K S A).raw
  refine ⟨fun _ (x : A → Bool) (a : A) => if x = encode a then 1 else 0, fun x => ?_⟩
  change S → A → Bool at x
  refine (Binary.raw_coeff (selector K S A) x).trans ?_
  change (∑ a, if x = fun _ => encode a then (1 : K) else 0) =
    ∑ a : A, ∏ s, ∑ j : A, (if x s = encode j then 1 else 0) * if j = a then 1 else 0
  simp only [mul_ite, mul_one, mul_zero, sum_ite_eq', mem_univ, ite_true]
  exact sum_congr rfl fun a _ => (prod_delta x (fun _ => encode a)).symm

def offer (P : A → (S → Y → Bool) → K) (m : ℕ) (t : A → ℕ) : Binary K S :=
  ((selector K S A).batch m).join (Binary.product fun j : Address 1 t => Binary.of (P j.1))

theorem offer_bound (P : A → (S → Y → Bool) → K) (m : ℕ) (t : A → ℕ) :
    (offer P m t).tensor ≤ (Fintype.card A : Tensor K S) ^ m * ∏ a, (Binary.of (P a)).tensor ^ t a := by
  let : MulLeftMono (Tensor K S) := ⟨fun c a b h => Tensor.mul_le_mul_left _ _ _ h⟩
  rw [offer, Binary.tensor_of_join, Binary.tensor_of_batch, Binary.tensor_of_product,
    Fintype.prod_sigma]
  simp only [prod_const, card_univ, Fintype.card_fin, mul_one]
  exact mul_le_mul_left (pow_le_pow_left' selector_bound m) _

variable {m z n : ℕ} (hn : n = m * z)

omit [Nonempty S] [Fintype S] in
theorem demand_value (T : (S → X → Bool) → K) (x : S → Layout.InPorts X m z → Bool) :
    (((Binary.of T).batch m).batch z).value x =
      ∏ i, T (fun s => Layout.input hn (x s) i) := by
  rw [← (Layout.row hn).prod_comp, Fintype.prod_prod_type]
  change (∏ i : Fin z, ∏ j : Fin m, T (fun s k => x s (i, j, k))) = _
  apply prod_congr rfl
  intro i _
  apply prod_congr rfl
  intro j _
  congr 1
  funext s k
  simp [Layout.input]

omit [Nonempty S] in
theorem offer_value (P : A → (S → Y → Bool) → K) (t : A → ℕ)
    (u : Fin n → S → A → Bool) (v : Address z t → S → Y → Bool) :
    ((offer P m t).batch z).value (Layout.assemble hn t u v) =
      (∑ w : Fin n → A, if u = fun i _ => encode (w i) then (1 : K) else 0) *
      ∏ j, P j.1 (v j) := by
  have h : (∏ i : Fin n, (selector K S A).value (u i)) =
      ∑ w : Fin n → A, if u = fun i _ => encode (w i) then (1 : K) else 0 := by
    change (∏ i : Fin n, ∑ a, if u i = fun _ => encode a then (1 : K) else 0) = _
    rw [Fintype.prod_sum]
    exact sum_congr rfl fun w _ => prod_delta u (fun i _ => encode (w i))
  rw [← h, ← (Layout.row hn).prod_comp, ← (Layout.addresses t z).prod_comp,
    Fintype.prod_prod_type, Fintype.prod_prod_type, ← prod_mul_distrib]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Local implementation of a word of selectors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Classical Routing Routing.WordSum

variable {K S A X Y : Type} [Field K] [Fintype S] [Nonempty S]
  [Fintype A] [DecidableEq A] [Fintype X] [Fintype Y] {n m z : ℕ}

variable (T : (S → X → Bool) → K) (P : A → (S → Y → Bool) → K)
  (L : A → S → (X → Bool) → (Y → Bool) → K) (U : A → S → (Y → Bool) → K)
  (a₀ : A) (hn : n = m * z) (t : A → ℕ)

def wordAction : Binary.Action (((Binary.of T).batch m).batch z) ((offer P m t).batch z) :=
  fun s x y =>
    let w := fun i => decode a₀ (Layout.code hn t y i)
    (if profile a₀ m z w = t then 1 else 0) *
      factor L U z w t s (Layout.input hn x) (Layout.supply t y)

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Coefficient identity for the scaled local maps -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Classical Routing Routing.WordSum Finset

variable {K S A X Y : Type} [Field K] [Fintype S] [Nonempty S]
  [Fintype A] [DecidableEq A] [Fintype X] [Fintype Y] {n m z : ℕ}

private theorem sum_codes {I J W : Type} [Fintype I] [Fintype J] [Fintype W] [DecidableEq I]
    (u : W → I) (f : I → J → K) (g : J → K) :
    (∑ i, ∑ j, f i j * ((∑ w, if i = u w then 1 else 0) * g j)) =
        ∑ w, ∑ j, f (u w) j * g j := by
  rw [sum_comm, sum_comm (s := (univ : Finset W))]
  apply sum_congr rfl
  intro j _
  simp only [sum_mul, mul_sum, ite_mul, mul_ite, one_mul, zero_mul, mul_zero]
  rw [sum_comm]
  simp

variable (T : (S → X → Bool) → K) (P : A → (S → Y → Bool) → K)
  (L : A → S → (X → Bool) → (Y → Bool) → K) (U : A → S → (Y → Bool) → K)
  (a₀ : A) (hn : n = m * z) (t : A → ℕ)

private theorem word_act (x : S → Layout.InPorts X m z → Bool) :
    Binary.act _ _ (wordAction T P L U a₀ hn t) x =
      ∑ w : Fin n → A, if profile a₀ m z w = t then
        ∑ y : Address z t → S → Y → Bool,
          (∏ s, factor L U z w t s (Layout.input hn (x s)) (fun i => y i s)) *
            ∏ i, P i.1 (y i) else 0 := by
  let f (u : Fin n → S → A → Bool) (v : Address z t → S → Y → Bool) :=
    ∏ s, wordAction T P L U a₀ hn t s (x s) (Layout.assemble hn t u v s)
  let g (v : Address z t → S → Y → Bool) := ∏ i, P i.1 (v i)
  let code (w : Fin n → A) : Fin n → S → A → Bool := fun i _ => encode (w i)
  have he : Binary.act _ _ (wordAction T P L U a₀ hn t) x =
      ∑ u, ∑ v, f u v * ((∑ w, if u = code w then 1 else 0) * g v) := by
    let e : _ ≃ ((offer P m t).batch z).Assign := Layout.joined hn t
    unfold Binary.act
    rw [← e.sum_comp, Fintype.sum_prod_type]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro v _
    exact congrArg (f u v * ·) (offer_value hn P t u v)
  rw [he, sum_codes]
  apply sum_congr rfl
  intro w _
  have key (v : Address z t → S → Y → Bool) (s : S) :
      wordAction T P L U a₀ hn t s (x s) (Layout.assemble hn t (code w) v s) =
        (if profile a₀ m z w = t then 1 else 0) *
          factor L U z w t s (Layout.input hn (x s)) (fun i => v i s) := by
    simp only [wordAction, Layout.code_assemble, Layout.supply_assemble, code, decode_encode]
  by_cases hh : profile a₀ m z w = t
  · rw [ite_eq_left hh]
    apply sum_congr rfl
    intro v _
    unfold f
    simp only [key, ite_eq_left hh, one_mul, g]
  · rw [ite_eq_right hh]
    apply sum_eq_zero
    intro v _
    have hv : f (code w) v = 0 := by
      apply prod_eq_zero (mem_univ (Classical.arbitrary S))
      rw [key, ite_eq_right hh, zero_mul]
    rw [hv, zero_mul]

theorem word_exact (hz : 0 < z)
    (hT : ∀ x, T x = ∑ a, ∑ y, (∏ s, L a s (x s) (y s)) * P a y)
    (hU : ∀ a, ∑ y, (∏ s, U a s (y s)) * P a y = 1)
    (x : (((Binary.of T).batch m).batch z).Assign) :
    (((Binary.of T).batch m).batch z).value x =
      ∑ t : ↥(histograms A (m + Fintype.card A)),
        Binary.act _ _ (wordAction T P L U a₀ hn t.val) x := by
  change S → Layout.InPorts X m z → Bool at x
  refine (demand_value hn T x).trans ((expand P L U hU T hT a₀ hn hz _).trans ?_)
  exact sum_congr rfl fun t _ => (word_act T P L U a₀ hn t.val x).symm

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Uniform implementation cost of a scaled word action -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol

open Classical Install Routing Routing.WordSum

variable {K S A X Y : Type}

/-- The word input and the two protocol ports name the same bits. -/
private def ports {k m z : ℕ} (hn : 2 ^ k = m * z) (t : A → ℕ) :
    Input A X Y k z t ≃ Layout.InPorts X m z ⊕ Layout.OutPorts Y t m z where
  toFun
    | .inl (i, .inl a) =>
      let j := (Layout.row hn).symm i
      .inr (j.1, .inl (j.2, a))
    | .inl (i, .inr x) =>
      let j := (Layout.row hn).symm i
      .inl (j.1, j.2, x)
    | .inr (i, y) =>
      let j := (Layout.addresses t z).symm i
      .inr (j.1, .inr ⟨j.2, y⟩)
  invFun
    | .inl (j, i, x) => .inl (Layout.row hn (j, i), .inr x)
    | .inr (j, .inl (i, a)) => .inl (Layout.row hn (j, i), .inl a)
    | .inr (j, .inr ⟨i, y⟩) => .inr (Layout.addresses t z (j, i), y)
  left_inv
    | .inl (i, .inl a) => by simp
    | .inl (i, .inr x) => by simp
    | .inr (i, y) => by simp
  right_inv
    | .inl (j, i, x) => by simp
    | .inr (j, .inl (i, a)) => by simp
    | .inr (j, .inr ⟨i, y⟩) => by simp

private theorem shift_scale (b h : ℕ) : scale (b + h) ≤ scale b * Binary.scale h := by
  unfold scale Binary.scale
  rw [pow_add, mul_mul_mul_comm, ← mul_pow]
  gcongr
  nlinarith

variable [Field K] [Fintype S] [Fintype A] [DecidableEq A] [Fintype X] [Fintype Y]
  (T : (S → X → Bool) → K) (P : A → (S → Y → Bool) → K)
  (L : A → S → (X → Bool) → (Y → Bool) → K) (U : A → S → (Y → Bool) → K) (a₀ : A)

/-- The constants may depend on the block and the alphabets. The same
bound holds for every additional dyadic power and rounded profile. -/
theorem word_cheap (b : ℕ) (hb : Fintype.card A ≤ 2 ^ b) :
    ∃ c : ℕ, ∀ h : ℕ, ∀ t : ↥(histograms A (2 ^ b + Fintype.card A)),
      Binary.Cheap _ _ (wordAction T P L U a₀ (pow_add 2 b h) t.val) (c * Binary.scale h) := by
  obtain ⟨M, hM⟩ := work_size (A := A) (R := A) (B := X) (C := Y)
  obtain ⟨N, hN⟩ := factor_net L U (decode a₀)
  obtain ⟨Q, hQ⟩ := check_net (K := K) a₀ (decode a₀)
  let c := 6 * M + 2 * Fintype.card A + Q + N
  refine ⟨c * scale b, fun h t s => ?_⟩
  let k := b + h
  let z := 2 ^ h
  have hn : 2 ^ k = 2 ^ b * z := pow_add 2 b h
  have ht (a) : t.val a * z ≤ 2 ^ (k + 1) := by
    have hta : t.val a ≤ 2 ^ b + Fintype.card A :=
      (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ a)).trans_eq
        (mem_histograms.mp t.property)
    rw [pow_succ, hn]
    calc
      _ ≤ (2 ^ b + 2 ^ b) * z := Nat.mul_le_mul_right z (hta.trans (Nat.add_le_add_left hb _))
      _ = _ := by ring
  let I := Input A X Y k z t.val
  let e (j : Row k × A) : I := .inl (j.1, .inl j.2)
  have test := (hQ k (2 ^ b) z hn (by positivity) t).pull e
  have net := (test.mul (hN k z t.val ht s)).rename (ports hn t.val)
  refine net.mono (le_trans (b := c * scale k) ?_ ?_)
  · have hi : Fintype.card I ≤ M * scale k :=
      (Fintype.card_le_of_injective Sum.inl Sum.inl_injective).trans (hM k z t.val ht)
    change 5 * Fintype.card I + (Fintype.card I + 2 * Fintype.card (Row k × A) +
      Q * 2 ^ k * (k + 1)) + N * 2 ^ k * (k + 1) ^ 3 ≤ c * scale k
    rw [Fintype.card_prod, Fintype.card_fin]
    unfold c
    unfold scale at hi ⊢
    ring_nf at hi ⊢
    omega
  · rw [mul_assoc]
    exact Nat.mul_le_mul_left _ (shift_scale b h)

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # A rounded substitution has a uniformly fast local implementation -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol

open Spectral Routing Classical Finset

variable {K S A X Y : Type} [Field K] [Fintype S] [Nonempty S]
  [Fintype A] [DecidableEq A] [Fintype X] [Fintype Y]

private theorem scalar (P : (S → Y → Bool) → K) (hP : 1 ≤ (Binary.of P).tensor) :
    ∃ U : S → (Y → Bool) → K, ∑ y, (∏ s, U s (y s)) * P y = 1 := by
  change (Binary.of P).raw.Restricts 1 at hP
  obtain ⟨U, h⟩ := (Raw.restricts_iff _ _).mp hP
  refine ⟨fun s => U s (), ?_⟩
  have he := h (fun _ => ())
  have h1 : (1 : Raw K S).coeff (fun _ => ()) = 1 := by
    change (∑ _ : Unit, ∏ _ : S, (1 : K)) = 1
    simp
  rw [h1] at he
  refine (sum_congr rfl fun y _ => ?_).trans he.symm
  exact congrArg _ (Binary.raw_coeff (Binary.of P) y).symm

theorem word_scalable (T : (S → X → Bool) → K) (P : A → (S → Y → Bool) → K) (a₀ : A)
    (hT : (Binary.of T).tensor ≤ ∑ a, (Binary.of (P a)).tensor)
    (hP : ∀ a, 1 ≤ (Binary.of (P a)).tensor) (b : ℕ) (hb : Fintype.card A ≤ 2 ^ b) :
    Binary.Scalable ((Binary.of T).batch (2 ^ b))
      (fun t : ↥(histograms A (2 ^ b + Fintype.card A)) => offer P (2 ^ b) t.val) := by
  obtain ⟨L, hL⟩ := (Binary.sum_action (Binary.of T) (fun a => Binary.of (P a))).mp hT
  choose U hU using fun a => scalar (P a) (hP a)
  obtain ⟨c, hc⟩ := word_cheap T P L U a₀ b hb
  exact ⟨c, fun h => ⟨fun t => wordAction T P L U a₀ (pow_add 2 b h) t.val,
    hc h, word_exact T P L U a₀ (pow_add 2 b h) (by positivity) hL hU⟩⟩

end OAI.LinearAlgebra.MatrixExponent.Protocol
end
