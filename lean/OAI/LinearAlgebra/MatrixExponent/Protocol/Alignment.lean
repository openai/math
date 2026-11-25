import OAI.LinearAlgebra.MatrixExponent.Protocol.Frame
import OAI.LinearAlgebra.MatrixExponent.Install.SumOut
import OAI.LinearAlgebra.MatrixExponent.Routing.Round

/-!
# Named tensor requests

Each slot belongs to one site. Relocating a presentation changes only
the owner map, retaining slot names and the underlying coefficients.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol

open Classical

structure Board (K S : Type) where
  slot : Type
  [finiteSlot : Fintype slot]
  owner : slot → S
  value : (slot → Bool) → K

attribute [instance] Board.finiteSlot

namespace Board

variable {K S T I : Type} (D : Board K S)

abbrev localPort (s : S) := {i : D.slot // D.owner i = s}

def binary : Binary K S where
  port s := D.localPort s
  value x := D.value (fun i => x (D.owner i) ⟨i, rfl⟩)

def move (f : S → T) : Board K T where
  slot := D.slot
  owner := f ∘ D.owner
  value := D.value

def ofBinary [Fintype S] (A : Binary K S) : Board K S where
  slot := Σ s, A.port s
  owner := Sigma.fst
  value x := A.value (fun s i => x ⟨s, i⟩)

variable [Field K]

def tensor [Fintype S] [Nonempty S] : Spectral.Tensor K S := D.binary.tensor

def link (K : Type) [Field K] (a b : S) : Board K S where
  slot := Bool
  owner i := if i then b else a
  value x := if x false = x true then 1 else 0

def union [Fintype I] (A : I → Board K S) : Board K S where
  slot := Σ i, (A i).slot
  owner x := (A x.1).owner x.2
  value x := ∏ i, (A i).value (fun j => x ⟨i, j⟩)

def orders [Fintype I] (A : I → Board K S) (z : I → ℕ) : Board K S :=
  union (fun i : Σ i, Fin (z i) => A i.1)

end Board
end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Local coordinates of orders indexed by kind and ordinal -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol

variable {K S S' I I' : Type}

abbrev Pin (T : I → Board K S) (s : S) := Σ i, (T i).localPort s

namespace Pin

variable {T : I → Board K S} {T' : I' → Board K S'} {s : S} {s' : S'}

def Same (e : Pin T s ≃ Pin T' s') (z : I → ℕ) (z' : I' → ℕ) : Prop :=
  ∀ i, z i.1 = z' (e i).1

variable [Field K] [Fintype I] [Fintype I'] {z : I → ℕ} {z' : I' → ℕ}

def atCopy (i : Pin T s) (j : Fin (z i.1)) : (Board.orders T z).localPort s :=
  ⟨⟨⟨i.1, j⟩, i.2.1⟩, i.2.2⟩

def slots (T : I → Board K S) (s : S) (z : I → ℕ) :
    (Σ i : Pin T s, Fin (z i.1)) ≃ (Board.orders T z).localPort s where
  toFun x := atCopy x.1 x.2
  invFun p := ⟨⟨p.1.1.1, ⟨p.1.2, p.2⟩⟩, p.1.1.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem exists_atCopy (p : (Board.orders T z).localPort s) :
    ∃ (i : Pin T s) (j : Fin (z i.1)), atCopy i j = p := by
  obtain ⟨⟨i, j⟩, h⟩ := (slots T s z).surjective p
  exact ⟨i, j, h⟩

def lift (e : Pin T s ≃ Pin T' s') (hz : Same e z z') :
    (Board.orders T z).localPort s ≃ (Board.orders T' z').localPort s' :=
  (slots T s z).symm.trans ((Equiv.sigmaCongr e fun i => finCongr (hz i)).trans (slots T' s' z'))

theorem lift_atCopy (e : Pin T s ≃ Pin T' s') (hz : Same e z z')
    (i : Pin T s) (j : Fin (z i.1)) :
    lift e hz (atCopy i j) = atCopy (e i) (Fin.cast (hz i) j) := rfl

end Pin
end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Fast local maps are stable under wiring, products, and contraction -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol.Frame

open Classical Install Binary

variable {K X Y Z U V I : Type} [Field K] [Fintype X] [Fintype Y]
  [Fintype Z] [Fintype U] [Fintype V] [Fintype I]

private theorem scale_ge (h : ℕ) : 2 ^ h ≤ scale h :=
  Nat.le_mul_of_pos_right _ (by positivity)

theorem Fast.pull {f : Frame K X Y} (hf : Fast f) (i : X → U) (j : Y → V) :
    Fast (f.pull i j) := by
  obtain ⟨c, hc⟩ := hf
  refine ⟨Fintype.card (U ⊕ V) + 2 * Fintype.card (X ⊕ Y) + c, fun h => ?_⟩
  apply ((hc h).pull (Prod.map (Sum.map i j) id)).mono
  simp only [Fintype.card_prod, Fintype.card_fin, add_mul, mul_assoc]
  gcongr <;> exact scale_ge h

theorem Fast.product {f : I → Frame K X Y} (hf : ∀ i, Fast (f i)) :
    Fast (product f) := by
  choose c hc using hf
  let m := Finset.univ.sup c
  refine ⟨Fintype.card (X ⊕ Y) + Fintype.card I * (5 * Fintype.card (X ⊕ Y) + m), fun h => ?_⟩
  have k (i) : Weight K (weight (f i) h) (m * scale h) :=
    (hc i h).mono (Nat.mul_le_mul_right _ (Finset.le_sup (Finset.mem_univ i)))
  apply (Weight.finite_product _ k).mono
  simp only [Fintype.card_prod, Fintype.card_fin, add_mul, mul_assoc]
  gcongr <;> exact scale_ge h

theorem Fast.mul {f g : Frame K X Y} (hf : Fast f) (hg : Fast g) :
    Fast (fun h x y => f h x y * g h x y) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨5 * Fintype.card (X ⊕ Y) + c + d, fun h => ?_⟩
  apply ((hc h).mul (hd h)).mono
  simp only [Fintype.card_prod, Fintype.card_fin, add_mul, mul_assoc]
  gcongr
  exact scale_ge h

theorem Fast.compose {f : Frame K X Y} {g : Frame K Y Z} (hf : Fast f) (hg : Fast g) :
    Fast (f.compose g) := by
  obtain ⟨c, hc⟩ := hf
  obtain ⟨d, hd⟩ := hg
  refine ⟨10 * Fintype.card X + 12 * Fintype.card Y + 10 * Fintype.card Z + c + d, fun h => ?_⟩
  let N := Fin (2 ^ h)
  let i : (X ⊕ Y) × N → (X ⊕ Z) × N ⊕ Y × N
    | (.inl x, k) => .inl (.inl x, k)
    | (.inr y, k) => .inr (y, k)
  let j : (Y ⊕ Z) × N → (X ⊕ Z) × N ⊕ Y × N
    | (.inl y, k) => .inr (y, k)
    | (.inr z, k) => .inl (.inr z, k)
  have H := (((hc h).pull i).mul ((hd h).pull j)).sum_out
  let : DecidableEq (Y × N) := Classical.decEq _
  have e (x : (X ⊕ Z) × N → Bool) :
      (∑ y : Y × N → Bool, weight f h (Sum.elim x y ∘ i) * weight g h (Sum.elim x y ∘ j)) =
        weight (f.compose g) h x :=
    (Equiv.curry Y N Bool).sum_comp (fun y =>
      f h (fun j k => x (.inl j, k)) y * g h y (fun j k => x (.inr j, k)))
  rw [← funext e]
  apply H.mono
  simp only [N, Fintype.card_sum, Fintype.card_prod, Fintype.card_fin]
  nlinarith only [Nat.mul_le_mul_left (10 * Fintype.card X + 12 * Fintype.card Y + 10 * Fintype.card Z)
    (scale_ge h)]

theorem fast_diagonal (k : (X → Bool) → (Y → Bool) → K) : Fast (diagonal k) := by
  let f (x : X ⊕ Y → Bool) := k (x ∘ Sum.inl) (x ∘ Sum.inr)
  refine ⟨8 * 2 ^ Fintype.card (X ⊕ Y), fun h => ?_⟩
  apply (((Weight.dense K _ f).prod h).rename (Equiv.prodComm _ _)).mono
  rw [mul_comm (2 ^ h)]
  exact Nat.mul_le_mul_left _ (scale_ge h)

theorem fast_keep (K X : Type) [Field K] [Fintype X] : Fast (keep K X) := by
  let k (x y : X → Bool) := if x = y then (1 : K) else 0
  suffices keep K X = diagonal k by rw [this]; exact fast_diagonal k
  funext h x y
  by_cases e : x = y
  · simp [keep, diagonal, k, e]
  rw [keep, ite_eq_right e]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp e
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hi
  symm
  apply Finset.prod_eq_zero (Finset.mem_univ j)
  exact ite_eq_right (fun he => hj (congrFun he i))

end OAI.LinearAlgebra.MatrixExponent.Protocol.Frame
end

/-!
# Exact local expansions of named boards

An expansion exposes every local matrix. Its equation sums first
over the common choice and then over all independent supply slots.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol.Board

open Classical

variable {K S I : Type} [Field K] [Fintype S]
  (D V : Board K S)

def eval (h : ℕ) (x : Lines h D.slot) : K :=
  ∏ i : Fin (2 ^ h), D.value (fun j => x j i)

def view {h : ℕ} (s : S) (x : Lines h D.slot) : Lines h (D.localPort s) :=
  x ∘ Subtype.val

def fibers (h : ℕ) : Lines h D.slot ≃ ((s : S) → Lines h (D.localPort s)) where
  toFun x s := D.view s x
  invFun x j := x (D.owner j) ⟨j, rfl⟩
  left_inv _ := rfl
  right_inv x := by funext s ⟨j, hj⟩; subst s; rfl

abbrev Kernel := ∀ s, Frame K (D.localPort s) (V.localPort s)

def Kernel.prod (k : Kernel D V) (h : ℕ) (x : Lines h D.slot) (y : Lines h V.slot) :=
  ∏ s, k s h (D.view s x) (V.view s y)

structure Expansion [Fintype I] (V : I → Board K S) where
  kernel : ∀ i, Kernel D (V i)
  fast : ∀ i s, Frame.Fast (kernel i s)
  identity : ∀ h x, D.eval h x = ∑ i, ∑ y, Kernel.prod D (V i) (kernel i) h x y * (V i).eval h y

def binaryLines (h : ℕ) : Lines h D.slot ≃ (D.binary.batch (2 ^ h)).Assign where
  toFun x _ p := x p.2.val p.1
  invFun y j i := y (D.owner j) (i, ⟨j, rfl⟩)
  left_inv _ := rfl
  right_inv y := by funext s ⟨i, j, hj⟩; subst s; rfl

/-- Compile the selected scaler only for a fixed local shape. -/
def realize [Fintype I] (V : I → Board K S)
    (h : Binary.Scalable D.binary (fun i => (V i).binary)) : Expansion D V := by
  let c := h.choose
  let k (d : ℕ) := (h.choose_spec d).choose
  have hk (d : ℕ) := (h.choose_spec d).choose_spec
  let f (i : I) : Kernel D (V i) := fun s d x y =>
    k d i s (fun j => x j.2 j.1) (fun j => y j.2 j.1)
  refine ⟨f, ?_, ?_⟩
  · intro i s
    refine ⟨c, fun d => ?_⟩
    let e := (Equiv.prodSumDistrib (Fin (2 ^ d)) (D.localPort s) ((V i).localPort s)).symm.trans
      (Equiv.prodComm _ _)
    exact ((hk d).1 i s).rename e
  · intro d x
    have he := (hk d).2 (D.binaryLines d x)
    refine he.trans (Finset.sum_congr rfl fun i _ => ?_)
    unfold Binary.act
    rw [← ((V i).binaryLines d).sum_comp]
    rfl

end OAI.LinearAlgebra.MatrixExponent.Protocol.Board
end

/-! # Composing exact board expansions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol.Board

open Classical Finset

variable {K S I : Type} [Field K] [Fintype S] [Fintype I]

section Sequential

variable {D V W : Board K S}

theorem compose_prod (f : Kernel D V) (g : Kernel V W) (h : ℕ)
    (x : Lines h D.slot) (y : Lines h W.slot) :
    Kernel.prod D W (fun s => Frame.compose (f s) (g s)) h x y =
      ∑ z : Lines h V.slot, Kernel.prod D V f h x z * Kernel.prod V W g h z y := by
  let L (s : S) (v : Lines h (V.localPort s)) := f s h (D.view s x) v * g s h v (W.view s y)
  have eq : Kernel.prod D W (fun s => Frame.compose (f s) (g s)) h x y = ∏ s, ∑ v, L s v := by
    apply prod_congr rfl
    intro s _
    exact sum_congr (by ext; simp) fun _ _ => rfl
  rw [eq, Fintype.prod_sum, ← (V.fibers h).sum_comp]
  unfold Kernel.prod L
  exact sum_congr rfl fun _ _ => prod_mul_distrib

variable {J : I → Type} [∀ i, Fintype (J i)]
  {P : I → Board K S} {Q : ∀ i, J i → Board K S}

def Expansion.comp (a : Expansion D P) (b : ∀ i, Expansion (P i) (Q i)) :
    Expansion D (fun j : Σ i, J i => Q j.1 j.2) where
  kernel j s := Frame.compose (a.kernel j.1 s) ((b j.1).kernel j.2 s)
  fast j s := (a.fast j.1 s).compose ((b j.1).fast j.2 s)
  identity h x := by
    rw [a.identity, Fintype.sum_sigma]
    apply sum_congr rfl
    intro i _
    simp only [compose_prod, sum_mul, (b i).identity, mul_sum, mul_assoc]
    rw [sum_comm]
    exact sum_congr rfl fun j _ => sum_comm

end Sequential

section Parallel

variable {A : I → Type} [∀ i, Fintype (A i)]
  (D : I → Board K S)

def component (s : S) (i : I) (j : (D i).localPort s) : (union D).localPort s :=
  ⟨⟨i, j.1⟩, j.2⟩

def parts (h : ℕ) : Lines h (union D).slot ≃ (∀ i, Lines h (D i).slot) where
  toFun x i j := x ⟨i, j⟩
  invFun x j := x j.1 j.2
  left_inv _ := rfl
  right_inv _ := rfl

omit [Fintype S] in
theorem eval_union (h : ℕ) (x : Lines h (union D).slot) :
    (union D).eval h x = ∏ i, (D i).eval h (parts D h x i) :=
  prod_comm

variable {D} {V : ∀ i, A i → Board K S} (a : ∀ i, Expansion (D i) (V i))

def Expansion.parallel [DecidableEq I] :
    Expansion (union D) (fun c : ∀ i, A i => union fun i => V i (c i)) where
  kernel c s := Frame.product fun i => Frame.pull ((a i).kernel (c i) s)
    (component D s i) (component (fun i => V i (c i)) s i)
  fast c s := Frame.Fast.product (fun i => ((a i).fast (c i) s).pull _ _)
  identity h x := by
    rw [eval_union]
    simp_rw [(a _).identity]
    rw [Fintype.prod_sum]
    apply sum_congr rfl
    intro c _
    rw [Fintype.prod_sum, ← (parts (fun i => V i (c i)) h).sum_comp]
    apply sum_congr rfl
    intro y _
    rw [prod_mul_distrib, eval_union]
    apply congrArg₂ (· * ·) _ rfl
    unfold Kernel.prod Frame.product
    exact prod_comm

end Parallel
end OAI.LinearAlgebra.MatrixExponent.Protocol.Board
end

/-!
# Port bijections for inventories of boards

These bijections preserve the owner of every bit and the entire tensor
on those bits. They do not introduce local linear maps.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol.Board

open Routing

variable {K S I J : Type}

/-- Change only the names of the bit positions. -/
structure Rename (D V : Board K S) where
  eqv : D.slot ≃ V.slot
  owner_eq : ∀ i, V.owner (eqv i) = D.owner i
  value_eq : ∀ x, D.value (x ∘ eqv) = V.value x

def join [Field K] (D V : Board K S) : Board K S where
  slot := D.slot ⊕ V.slot
  owner := Sum.elim D.owner V.owner
  value x := D.value (x ∘ Sum.inl) * V.value (x ∘ Sum.inr)

namespace Rename

variable {D V W X : Board K S}

def refl (D : Board K S) : Rename D D := ⟨.refl _, fun _ => rfl, fun _ => rfl⟩

def trans (h : Rename D V) (k : Rename V W) : Rename D W where
  eqv := h.eqv.trans k.eqv
  owner_eq i := (k.owner_eq _).trans (h.owner_eq i)
  value_eq x := (h.value_eq (x ∘ k.eqv)).trans (k.value_eq x)

def symm (h : Rename D V) : Rename V D where
  eqv := h.eqv.symm
  owner_eq i := by rw [← h.owner_eq, Equiv.apply_symm_apply]
  value_eq x := by rw [← h.value_eq]; simp [Function.comp_def]

variable [Field K]

def join (h : Rename D V) (k : Rename W X) : Rename (D.join W) (V.join X) where
  eqv := h.eqv.sumCongr k.eqv
  owner_eq := by rintro (i | j); exact h.owner_eq i; exact k.owner_eq j
  value_eq x := congrArg₂ (· * ·) (h.value_eq (x ∘ Sum.inl)) (k.value_eq (x ∘ Sum.inr))

def union [Fintype I] {D V : I → Board K S} (h : ∀ i, Rename (D i) (V i)) :
    Rename (Board.union D) (Board.union V) where
  eqv := Equiv.sigmaCongrRight (fun i => (h i).eqv)
  owner_eq i := (h i.1).owner_eq i.2
  value_eq x := Finset.prod_congr rfl (fun i _ => (h i).value_eq (fun j => x ⟨i, j⟩))

end Rename

variable [Field K] [Fintype I] [Fintype J]

def union_equiv (D : J → Board K S) (e : I ≃ J) : Rename (union (D ∘ e)) (union D) where
  eqv := Equiv.sigmaCongrLeft (β := fun i => (D i).slot) e
  owner_eq _ := rfl
  value_eq x := e.prod_comp (fun i => (D i).value (fun j => x ⟨i, j⟩))

def union_sigma {P : I → Type} [∀ i, Fintype (P i)] (D : (i : I) → P i → Board K S) :
    Rename (union (fun j : Σ i, P i => D j.1 j.2)) (union (fun i => union (D i))) where
  eqv := Equiv.sigmaAssoc (fun i j => (D i j).slot)
  owner_eq _ := rfl
  value_eq x := Fintype.prod_sigma (fun j : Σ i, P i =>
    (D j.1 j.2).value (fun k => x ⟨j.1, ⟨j.2, k⟩⟩))

def union_split (D : I ⊕ J → Board K S) :
    Rename (union D) ((union (D ∘ Sum.inl)).join (union (D ∘ Sum.inr))) where
  eqv := Equiv.sumSigmaDistrib (fun i => (D i).slot)
  owner_eq := by rintro ⟨i | j, k⟩ <;> rfl
  value_eq x := Fintype.prod_sum_type _

def union_join (D V : I → Board K S) :
    Rename (union (fun i => (D i).join (V i))) ((union D).join (union V)) where
  eqv := Equiv.sigmaSumDistrib (fun i => (D i).slot) (fun i => (V i).slot)
  owner_eq := by rintro ⟨i, j | k⟩ <;> rfl
  value_eq _ := Finset.prod_mul_distrib

def union_swap (D : I → J → Board K S) :
    Rename (union (fun i => union (D i))) (union (fun j => union (fun i => D i j))) where
  eqv := {
    toFun := fun x => ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
    invFun := fun x => ⟨x.2.1, ⟨x.1, x.2.2⟩⟩
    left_inv := fun _ => rfl
    right_inv := fun _ => rfl }
  owner_eq _ := rfl
  value_eq _ := Finset.prod_comm

def orders_union (T : I → Board K S) (z : I → ℕ) :
    Rename (orders T z) (union (fun i => union (fun _ : Fin (z i) => T i))) :=
  union_sigma (fun i (_ : Fin (z i)) => T i)

def orders_add (T : I → Board K S) (x y : I → ℕ) :
    Rename (orders T (fun i => x i + y i)) ((orders T x).join (orders T y)) := by
  let D (i : I) (_ : Fin (x i) ⊕ Fin (y i)) := T i
  let e i := (union_equiv (D i) finSumFinEquiv.symm).trans (union_split (D i))
  exact (orders_union T _).trans <| (Rename.union e).trans <|
    (union_join _ _).trans ((orders_union T x).symm.join (orders_union T y).symm)

def orders_sum (T : I → Board K S) (z : J → I → ℕ)
    (e : ∀ i, Fin (∑ j, z j i) ≃ Σ j, Fin (z j i)) :
    Rename (orders T (fun i => ∑ j, z j i)) (union (fun j => orders T (z j))) := by
  let r (i : I) := (union_equiv (fun _ => T i) (e i)).trans
    (union_sigma (fun j (_ : Fin (z j i)) => T i))
  exact (orders_union T _).trans <| (Rename.union r).trans <|
    (union_swap _).trans (Rename.union fun j => (orders_union T (z j)).symm)

def orders_split (T : I ⊕ J → Board K S) (z : I ⊕ J → ℕ) :
    Rename (orders T z)
      ((orders (T ∘ Sum.inl) (z ∘ Sum.inl)).join (orders (T ∘ Sum.inr) (z ∘ Sum.inr))) :=
  (orders_union T z).trans <| (union_split _).trans
    ((orders_union _ _).symm.join (orders_union _ _).symm)

private def collectEquiv [DecidableEq I] (g : J → I) (hg : Function.Injective g) (z : J → ℕ) :
    (Σ j, Fin (z j)) ≃ Σ i, Fin (Stock.collect g z i) := by
  let f (p : Σ j, Fin (z j)) : Σ i, Fin (Stock.collect g z i) :=
    ⟨g p.1, Fin.cast (Stock.collect_inj hg z p.1).symm p.2⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · rintro ⟨j, a⟩ ⟨k, b⟩ h
    have hj : j = k := hg (congrArg Sigma.fst h)
    subst k
    have hab : a = b := Fin.ext (congrArg (fun p => p.2.val) h)
    rw [hab]
  · rintro ⟨i, a⟩
    obtain ⟨j, rfl, _⟩ := Stock.collect_nonzero (Nat.ne_of_gt a.pos)
    exact ⟨⟨j, Fin.cast (Stock.collect_inj hg z j) a⟩, rfl⟩

def orders_collect [DecidableEq I] (T : I → Board K S) (g : J → I)
    (hg : Function.Injective g) (z : J → ℕ) :
    Rename (orders T (Stock.collect g z)) (orders (T ∘ g) z) :=
  (union_equiv (fun p : Σ i, Fin (Stock.collect g z i) => T p.1) (collectEquiv g hg z)).symm

end OAI.LinearAlgebra.MatrixExponent.Protocol.Board
end

/-! # Relocation, reindexing, and unchanged slots in local expansions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol.Board

open Classical

variable {K S T I : Type} {D D' : Board K S} {V V' : I → Board K S}

def Rename.local (e : Rename D D') (s : S) : D.localPort s → D'.localPort s :=
  fun i => ⟨e.eqv i, (e.owner_eq i).trans i.property⟩

variable [Field K]

theorem Rename.eval_eq (e : Rename D D') (n : ℕ) (x : Lines n D'.slot) :
    D.eval n (x ∘ e.eqv) = D'.eval n x :=
  Finset.prod_congr rfl fun i _ => e.value_eq (fun j => x j i)

variable [Fintype S] [Fintype I]

def Expansion.rename (h : Expansion D V) (e : Rename D D') (g : ∀ i, Rename (V i) (V' i)) :
    Expansion D' V' where
  kernel i s := (h.kernel i s).pull (e.local s) ((g i).local s)
  fast i s := (h.fast i s).pull _ _
  identity n x := by
    rw [← e.eval_eq, h.identity]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ((g i).eqv.symm.arrowCongr (Equiv.refl (Fin (2 ^ n) → Bool))).sum_comp]
    exact Finset.sum_congr rfl fun y _ => congrArg _ ((g i).eval_eq n y)

def movePort (D : Board K S) (f : S → T) {t : T} (s : {s // f s = t}) :
    D.localPort s → (D.move f).localPort t :=
  fun i => ⟨i.val, (congrArg f i.property).trans s.property⟩

def Expansion.place [Fintype T] (h : Expansion D V) (f : S → T) :
    Expansion (D.move f) (fun i => (V i).move f) where
  kernel i t := Frame.product fun s : {s // f s = t} =>
    (h.kernel i s).pull (D.movePort f s) ((V i).movePort f s)
  fast i t := Frame.Fast.product fun s => (h.fast i s).pull _ _
  identity n x := by
    refine (h.identity n x).trans (Finset.sum_congr rfl fun i _ =>
      Finset.sum_congr rfl fun y _ => ?_)
    exact congrArg (· * (V i).eval n y)
      (Fintype.prod_fiberwise f (fun s => h.kernel i s n (D.view s x) ((V i).view s y))).symm

def joinLeft (D X : Board K S) (s : S) : D.localPort s → (D.join X).localPort s :=
  fun i => ⟨.inl i.val, i.property⟩

def joinRight (D X : Board K S) (s : S) : X.localPort s → (D.join X).localPort s :=
  fun i => ⟨.inr i.val, i.property⟩

omit [Fintype S] in
theorem eval_join (D X : Board K S) (n : ℕ) (x : Lines n (D.join X).slot) :
    (D.join X).eval n x = D.eval n (x ∘ Sum.inl) * X.eval n (x ∘ Sum.inr) :=
  Finset.prod_mul_distrib

private theorem delta (X : Board K S) (n : ℕ) (x y : Lines n X.slot) :
    (∏ s, Frame.keep K (X.localPort s) n (X.view s x) (X.view s y)) =
      if x = y then 1 else 0 := by
  by_cases e : x = y
  · simp [Frame.keep, e]
  obtain ⟨i, hi⟩ := Function.ne_iff.mp e
  rw [ite_eq_right e]
  apply Finset.prod_eq_zero (Finset.mem_univ (X.owner i))
  exact ite_eq_right (fun h => hi (congrFun h ⟨i, rfl⟩))

def Kernel.keep (k : Kernel D D') (X : Board K S) : Kernel (D.join X) (D'.join X) :=
  fun s n x y => k s n (x ∘ D.joinLeft X s) (y ∘ D'.joinLeft X s) *
    Frame.keep K (X.localPort s) n (x ∘ D.joinRight X s) (y ∘ D'.joinRight X s)

private theorem Kernel.keep_prod (k : Kernel D D') (X : Board K S)
    (n : ℕ) (x : Lines n (D.join X).slot) (y : Lines n D'.slot) (z : Lines n X.slot) :
    Kernel.prod _ _ (k.keep X) n x (Sum.elim y z) =
      Kernel.prod D D' k n (x ∘ Sum.inl) y * (if x ∘ Sum.inr = z then 1 else 0) := by
  rw [← delta X]
  exact Finset.prod_mul_distrib

def Expansion.keep (h : Expansion D V) (X : Board K S) :
    Expansion (D.join X) (fun i => (V i).join X) where
  kernel i := (h.kernel i).keep X
  fast i s := ((h.fast i s).pull (D.joinLeft X s) ((V i).joinLeft X s)).mul
    ((Frame.fast_keep K (X.localPort s)).pull (D.joinRight X s) ((V i).joinRight X s))
  identity n x := by
    rw [eval_join, h.identity, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    let e : Lines n (V i).slot × Lines n X.slot ≃ Lines n ((V i).join X).slot :=
      (Equiv.sumArrowEquivProdArrow _ _ _).symm
    rw [← e.sum_comp, Fintype.sum_prod_type, Finset.sum_mul]
    refine Finset.sum_congr rfl fun y _ => ?_
    symm
    calc
      _ = ∑ z : Lines n X.slot,
          (Kernel.prod D (V i) (h.kernel i) n (x ∘ Sum.inl) y *
            (if x ∘ Sum.inr = z then 1 else 0)) * ((V i).eval n y * X.eval n z) :=
        Finset.sum_congr rfl fun z _ => congrArg₂ (· * ·)
          ((h.kernel i).keep_prod X n x y z) (eval_join (V i) X n (Sum.elim y z))
      _ = _ := by simp [mul_ite, ite_mul, mul_assoc]

end OAI.LinearAlgebra.MatrixExponent.Protocol.Board
end

/-! # Local maps in different port coordinates -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol

open Classical

namespace Frame

variable {K X X' Y Y' Z Z' U U' V V' : Type}

def Rel (e : X ≃ X') (g : Y ≃ Y') (f : Frame K X Y) (f' : Frame K X' Y') : Prop :=
  ∀ h x y, f h (x ∘ e) (y ∘ g) = f' h x y

variable {e : X ≃ X'} {g : Y ≃ Y'} {f : Frame K X Y} {f' : Frame K X' Y'}

theorem Rel.refl (f : Frame K X Y) : Rel (.refl X) (.refl Y) f f := fun _ _ _ => rfl

theorem Rel.symm (hf : Rel e g f f') : Rel e.symm g.symm f' f := by
  intro h x y
  rw [← hf]
  simp only [Function.comp_def, Equiv.symm_apply_apply]

theorem Rel.trans {a : X' ≃ U} {b : Y' ≃ V} {l : Frame K U V}
    (hf : Rel e g f f') (hl : Rel a b f' l) : Rel (e.trans a) (g.trans b) f l :=
  fun h x y => (hf h (x ∘ a) (y ∘ b)).trans (hl h x y)

theorem Rel.pull (hf : Rel e g f f') {i : X → U} {j : Y → V} {i' : X' → U'} {j' : Y' → V'}
    {a : U ≃ U'} {b : V ≃ V'} (hi : ∀ x, a (i x) = i' (e x)) (hj : ∀ y, b (j y) = j' (g y)) :
    Rel a b (f.pull i j) (f'.pull i' j') := by
  intro h x y
  unfold Frame.pull
  rw [← hf]
  simp only [Function.comp_def, hi, hj]

variable [Field K]

theorem Rel.mul {k : Frame K X Y} {k' : Frame K X' Y'}
    (hf : Rel e g f f') (hk : Rel e g k k') :
    Rel e g (fun h x y => f h x y * k h x y) (fun h x y => f' h x y * k' h x y) :=
  fun h x y => congrArg₂ (· * ·) (hf h x y) (hk h x y)

theorem Rel.product {I J : Type} [Fintype I] [Fintype J] (i : I ≃ J)
    {k : I → Frame K X Y} {l : J → Frame K X' Y'} (hk : ∀ j, Rel e g (k j) (l (i j))) :
    Rel e g (product k) (product l) := by
  intro h x y
  unfold Frame.product
  rw [← i.prod_comp (fun j => l j h x y)]
  exact Finset.prod_congr rfl fun j _ => hk j h x y

theorem Rel.compose [Fintype Y] [Fintype Y'] {a : Z ≃ Z'} {k : Frame K Y Z} {k' : Frame K Y' Z'}
    (hf : Rel e g f f') (hk : Rel g a k k') : Rel e a (f.compose k) (f'.compose k') := by
  intro h x z
  unfold Frame.compose
  rw [← (g.symm.arrowCongr (Equiv.refl (Fin (2 ^ h) → Bool))).sum_comp]
  exact Finset.sum_congr rfl fun y _ => congrArg₂ (· * ·) (hf h x y) (hk h y z)

theorem keep_rel (e : X ≃ X') : Rel e e (keep K X) (keep K X') := by
  intro h x y
  have he : x ∘ e = y ∘ e ↔ x = y := (e.symm.arrowCongr (Equiv.refl (Fin (2 ^ h) → Bool))).injective.eq_iff
  simp only [keep, he]

end Frame

namespace Board

variable {K S S' : Type} [Field K] {D V W : Board K S} {D' V' W' : Board K S'} {s : S} {s' : S'}

private def splitJoin (D V : Board K S) (s : S) :
    (D.join V).localPort s ≃ D.localPort s ⊕ V.localPort s where
  toFun
    | ⟨.inl i, h⟩ => .inl ⟨i, h⟩
    | ⟨.inr i, h⟩ => .inr ⟨i, h⟩
  invFun := Sum.elim (D.joinLeft V s) (D.joinRight V s)
  left_inv := by rintro ⟨i|i, h⟩ <;> rfl
  right_inv := by rintro (i|i) <;> rfl

def joinPorts (e : D.localPort s ≃ D'.localPort s') (g : V.localPort s ≃ V'.localPort s') :
    (D.join V).localPort s ≃ (D'.join V').localPort s' :=
  (splitJoin D V s).trans ((e.sumCongr g).trans (splitJoin D' V' s').symm)

@[simp] theorem joinPorts_left (e : D.localPort s ≃ D'.localPort s')
    (g : V.localPort s ≃ V'.localPort s') (i : D.localPort s) :
    joinPorts e g (D.joinLeft V s i) = D'.joinLeft V' s' (e i) := rfl

@[simp] theorem joinPorts_right (e : D.localPort s ≃ D'.localPort s')
    (g : V.localPort s ≃ V'.localPort s') (i : V.localPort s) :
    joinPorts e g (D.joinRight V s i) = D'.joinRight V' s' (g i) := rfl

theorem Kernel.keep_rel {k : Kernel D V} {k' : Kernel D' V'}
    {e : D.localPort s ≃ D'.localPort s'} {g : V.localPort s ≃ V'.localPort s'}
    (hk : Frame.Rel e g (k s) (k' s')) (w : W.localPort s ≃ W'.localPort s') :
    Frame.Rel (joinPorts e w) (joinPorts g w) (k.keep W s) (k'.keep W' s') :=
  (hk.pull (joinPorts_left e w) (joinPorts_left g w)).mul
    ((Frame.keep_rel w).pull (joinPorts_right e w) (joinPorts_right g w))

end Board
end OAI.LinearAlgebra.MatrixExponent.Protocol
end

section
/-! # Assigning stock positions to concurrent interventions -/

namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Routing

/-- The control can choose its own local ordering of the centers. -/
structure Allocation {I E J : Type} [Fintype J] [DecidableEq J] (q : J → Intervention I E) where
  take : ∀ i, Fin ((Intervention.parallel q).take i) ≃ Σ j, Fin ((q j).take i)
  put : ∀ (h : (j : J) → (q j).choice) i,
    Fin ((Intervention.parallel q).put h i) ≃ Σ j, Fin ((q j).put (h j) i)
  core : ∀ (h : (j : J) → (q j).choice) e,
    Fin ((Intervention.parallel q).core h e) ≃ Σ j, Fin ((q j).core (h j) e)

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Implementing a simultaneous stock intervention by local matrix kernels -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol

open Routing Board

variable {K S I E J : Type} [Field K]

def Board.rotate (D V W : Board K S) : Rename ((D.join V).join W) ((W.join D).join V) where
  eqv := (Equiv.sumComm _ _).trans (Equiv.sumAssoc _ _ _).symm
  owner_eq := by rintro ((x|x)|x) <;> rfl
  value_eq x := by
    change (D.value (fun j => x (.inl (.inr j))) * V.value (fun j => x (.inr j))) *
      W.value (fun j => x (.inl (.inl j))) =
      (W.value (fun j => x (.inl (.inl j))) * D.value (fun j => x (.inl (.inr j)))) *
        V.value (fun j => x (.inr j))
    ac_rfl

def Board.swap (D V : Board K S) : Rename (D.join V) (V.join D) where
  eqv := Equiv.sumComm _ _
  owner_eq := by rintro (x|x) <;> rfl
  value_eq _ := mul_comm _ _

variable [Fintype S] [Fintype I] [Fintype E] (T : I → Board K S) (V : E → Board K S)

abbrev Executes (q : Intervention I E) :=
  Expansion (orders T q.take) (fun u => (orders T (q.put u)).join (orders V (q.core u)))

def Board.orders_eq {x y : I → ℕ} (h : x = y) : Rename (orders T x) (orders T y) :=
  union_equiv (fun j : Σ i, Fin (y i) => T j.1) (Equiv.sigmaCongrRight fun i => finCongr (congrFun h i))

variable {T V}

def Executes.parallel [Fintype J] [DecidableEq J] {q : J → Intervention I E}
    (e : Allocation q) (r : ∀ j, Executes T V (q j)) : Executes T V (Intervention.parallel q) :=
  (Expansion.parallel r).rename (orders_sum T _ e.take).symm fun u =>
    (union_join _ _).trans ((orders_sum T _ (e.put u)).symm.join (orders_sum V _ (e.core u)).symm)

def Executes.takeStep {q : Intervention I E} (r : Executes T V q) (z : I → ℕ) (hz : q.take ≤ z) :
    Expansion (orders T z) (fun j => (orders T (q.next z j)).join (orders V (q.core j))) := by
  let w := fun i => z i - q.take i
  have he : (fun i => q.take i + w i) = z := by
    funext i
    exact Nat.add_sub_of_le (hz i)
  exact (r.keep (orders T w)).rename
    ((orders_add T q.take w).symm.trans (orders_eq T he)) fun j =>
      (rotate _ _ _).trans ((orders_add T w (q.put j)).symm.join (.refl _))

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-!
# Coordinates of the inventory bijections

Slots within each copy are unchanged. For a sum of inventories,
the copy ordinal is determined by the supplied allocation.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol.Board

variable {K S I J : Type} [Field K] [Fintype I] [Fintype J]

private theorem inverse_slot {X Y Z : Type} (e : X ≃ Y) (j : Y) (s : Z) :
    (Equiv.sigmaCongrLeft (β := fun _ => Z) e).symm ⟨j, s⟩ = ⟨e.symm j, s⟩ := by
  apply (Equiv.sigmaCongrLeft (β := fun _ => Z) e).injective
  rw [Equiv.apply_symm_apply]
  change (⟨j, s⟩ : Σ _ : Y, Z) = ⟨e (e.symm j), s⟩
  rw [Equiv.apply_symm_apply]

private def embedOrdinal (T : I → Board K S) (a : I → ℕ) (i : I)
    (p : Σ _ : Fin (a i), (T i).slot) : (orders T a).slot :=
  ⟨⟨i, p.1⟩, p.2⟩

theorem orders_add_left (T : I → Board K S) (a b : I → ℕ)
    (i : I) (r : Fin (a i)) (s : (T i).slot) :
    (orders_add T a b).symm.eqv (.inl ⟨⟨i, r⟩, s⟩) = ⟨⟨i, Fin.castAdd (b i) r⟩, s⟩ := by
  exact congrArg (embedOrdinal T (fun i => a i + b i) i)
    (inverse_slot (finSumFinEquiv (m := a i) (n := b i)).symm (.inl r) s)

theorem orders_add_right (T : I → Board K S) (a b : I → ℕ)
    (i : I) (r : Fin (b i)) (s : (T i).slot) :
    (orders_add T a b).symm.eqv (.inr ⟨⟨i, r⟩, s⟩) = ⟨⟨i, Fin.natAdd (a i) r⟩, s⟩ := by
  exact congrArg (embedOrdinal T (fun i => a i + b i) i)
    (inverse_slot (finSumFinEquiv (m := a i) (n := b i)).symm (.inr r) s)

theorem orders_sum_slot (T : I → Board K S) (z : J → I → ℕ)
    (e : ∀ i, Fin (∑ j, z j i) ≃ Σ j, Fin (z j i))
    (j : J) (i : I) (r : Fin (z j i)) (s : (T i).slot) :
    (orders_sum T z e).symm.eqv ⟨j, ⟨⟨i, r⟩, s⟩⟩ = ⟨⟨i, (e i).symm ⟨j, r⟩⟩, s⟩ := by
  exact congrArg (embedOrdinal T (fun i => ∑ j, z j i) i) (inverse_slot (e i) ⟨j, r⟩ s)

theorem orders_split_left (T : I ⊕ J → Board K S) (z : I ⊕ J → ℕ)
    (i : I) (r : Fin (z (.inl i))) (s : (T (.inl i)).slot) :
    (orders_split T z).symm.eqv (.inl ⟨⟨i, r⟩, s⟩) = ⟨⟨.inl i, r⟩, s⟩ := rfl

theorem orders_split_right (T : I ⊕ J → Board K S) (z : I ⊕ J → ℕ)
    (j : J) (r : Fin (z (.inr j))) (s : (T (.inr j)).slot) :
    (orders_split T z).symm.eqv (.inr ⟨⟨j, r⟩, s⟩) = ⟨⟨.inr j, r⟩, s⟩ := rfl

theorem orders_collect_slot [DecidableEq I] (T : I → Board K S) (g : J → I)
    (hg : Function.Injective g) (z : J → ℕ) (j : J) (r : Fin (z j)) (s : (T (g j)).slot) :
    (orders_collect T g hg z).symm.eqv ⟨⟨j, r⟩, s⟩ =
      ⟨⟨g j, Fin.cast (Routing.Stock.collect_inj hg z j).symm r⟩, s⟩ := rfl

theorem orders_eq_slot (T : I → Board K S) {a b : I → ℕ} (h : a = b)
    (i : I) (r : Fin (a i)) (s : (T i).slot) :
    (orders_eq T h).eqv ⟨⟨i, r⟩, s⟩ = ⟨⟨i, Fin.cast (congrFun h i) r⟩, s⟩ := rfl

theorem union_join_left (T V : I → Board K S) (i : I) (s : (T i).slot) :
    (union_join T V).eqv ⟨i, .inl s⟩ = .inl ⟨i, s⟩ := rfl

theorem union_join_right (T V : I → Board K S) (i : I) (s : (V i).slot) :
    (union_join T V).eqv ⟨i, .inr s⟩ = .inr ⟨i, s⟩ := rfl

variable (D V W : Board K S)

theorem swap_left (s : D.slot) : (swap D V).eqv (.inl s) = .inr s := rfl
theorem swap_right (s : V.slot) : (swap D V).eqv (.inr s) = .inl s := rfl

theorem rotate_left (s : D.slot) : (rotate D V W).eqv (.inl (.inl s)) = .inl (.inr s) := rfl
theorem rotate_middle (s : V.slot) : (rotate D V W).eqv (.inl (.inr s)) = .inr s := rfl
theorem rotate_right (s : W.slot) : (rotate D V W).eqv (.inr s) = .inl (.inl s) := rfl

end OAI.LinearAlgebra.MatrixExponent.Protocol.Board
end

/-! # Tracking copy ordinals across concurrent expansions -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol

open Routing Board Finset

variable {K S S' I I' E J J' : Type} [Field K] [Fintype I] [Fintype I'] [Fintype E]
  [Fintype J] [Fintype J'] {T : I → Board K S} {T' : I' → Board K S'}
  {V : E → Board K S} {s : S} {s' : S'} {u : Finset J} {u' : Finset J'}

/-- A move is invisible at a site if it uses no incident slots and its local scalar is one. -/
structure Silent [Fintype S] (s : S) {q : Intervention I E} (r : Executes T V q)
    (t : q.choice) : Prop where
  take : ∀ i : Pin T s, q.take i.1 = 0
  put : ∀ i : Pin T s, q.put t i.1 = 0
  core : ∀ i : Pin V s, q.core t i.1 = 0
  one : ∀ h x y, r.kernel t s h x y = 1

namespace Pin

abbrev Assignment (z : J → I → ℕ) := ∀ i, Fin (∑ j, z j i) ≃ Σ j, Fin (z j i)

variable {z : J → I → ℕ} {z' : J' → I' → ℕ}

/-- Corresponding copies are assigned the same ordinal in the aggregate stock. -/
def Align (e : Pin T s ≃ Pin T' s') (g : ↥u ≃ ↥u') (a : Assignment z) (b : Assignment z') :
    Prop :=
  ∀ (j : ↥u) (i : Pin T s) (r : Fin (z j i.1)) (r' : Fin (z' (g j) (e i).1)),
    r.val = r'.val → ((a i.1).symm ⟨j, r⟩).val = ((b (e i).1).symm ⟨g j, r'⟩).val

def assign (T : I → Board K S) (a : Assignment z) (j : J) (s : S) :
    (orders T (z j)).localPort s → (orders T (fun i => ∑ j, z j i)).localPort s :=
  (orders_sum T z a).symm.local s ∘ component (fun j => orders T (z j)) s j

theorem assign_atCopy (a : Assignment z) (j : J) (i : Pin T s) (r : Fin (z j i.1)) :
    assign T a j s (atCopy i r) = atCopy i ((a i.1).symm ⟨j, r⟩) :=
  Subtype.ext (orders_sum_slot T z a j i.1 r i.2.val)

theorem Align.assign {e : Pin T s ≃ Pin T' s'} {g : ↥u ≃ ↥u'}
    {a : Assignment z} {b : Assignment z'} (h : Align e g a b)
    (ht : Same e (fun i => ∑ j, z j i) (fun i => ∑ j, z' j i))
    (j : ↥u) (hj : Same e (z j) (z' (g j))) (x : (orders T (z j)).localPort s) :
    lift e ht (Pin.assign T a j s x) = Pin.assign T' b (g j) s' (lift e hj x) := by
  obtain ⟨i, r, rfl⟩ := exists_atCopy x
  rw [assign_atCopy, lift_atCopy, lift_atCopy, assign_atCopy]
  exact congrArg (atCopy (e i)) (Fin.ext (h j i r _ rfl))

end Pin

end OAI.LinearAlgebra.MatrixExponent.Protocol
end
