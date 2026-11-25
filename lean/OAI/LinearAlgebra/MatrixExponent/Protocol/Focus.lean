import OAI.LinearAlgebra.MatrixExponent.Protocol.Frame
import OAI.LinearAlgebra.MatrixExponent.Install.SumOut
import OAI.LinearAlgebra.MatrixExponent.Protocol.Alignment
import OAI.LinearAlgebra.MatrixExponent.Routing.Uniform.System
import OAI.LinearAlgebra.MatrixExponent.Routing.Packets
import OAI.LinearAlgebra.MatrixExponent.Routing.Control.Keys
import OAI.LinearAlgebra.MatrixExponent.Routing.Fixed
import OAI.LinearAlgebra.MatrixExponent.Protocol.Wired

/-! # Common binary local coordinates for finitely many tensor classes -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol.Binary

open Spectral Classical

variable {K S : Type} [Field K] [Fintype S] [Nonempty S]

private theorem representAt (R : Raw K S) (d : ℕ)
    (h : ∀ s, Fintype.card (R.leg s) ≤ 2 ^ d) :
    ∃ f : (S → Fin d → Bool) → K, (of f).tensor = Tensor.ofRaw R := by
  by_cases e : ∀ s, Nonempty (R.leg s)
  · let := e
    have hem (s : S) : Nonempty (R.leg s ↪ (Fin d → Bool)) :=
      Function.Embedding.nonempty_of_card_le (by simpa using h s)
    let enc s := Classical.choice (hem s)
    let dec s := Function.invFun (enc s)
    let f (x : S → Fin d → Bool) := R.coeff (fun s => dec s (x s))
    refine ⟨f, Tensor.ofRaw_eq ⟨?_, ?_⟩⟩
    · refine Raw.Restricts.pullback (fun s => enc s) fun x => ?_
      calc
        _ = R.coeff (fun s => dec s (enc s (x s))) :=
          congrArg R.coeff (funext fun s => (Function.leftInverse_invFun (enc s).injective _).symm)
        _ = _ := (raw_coeff (of f) (fun s => enc s (x s))).symm
    · exact Raw.Restricts.pullback dec (raw_coeff (of f))
  · have z : Tensor.ofRaw R = 0 :=
      (Tensor.ofRaw_eq_zero _).mpr fun x => (e (fun s => ⟨x s⟩)).elim
    refine ⟨fun _ => 0, ?_⟩
    rw [z]
    exact (Tensor.ofRaw_eq_zero _).mpr (raw_coeff (of (fun _ : S → Fin d → Bool => (0 : K))))

/-- Choose a single register width accommodating every local coordinate in the family. -/
theorem represent {I : Type} [Fintype I] (T : I → Tensor K S) :
    ∃ d : ℕ, ∃ A : I → (S → Fin d → Bool) → K, ∀ i, (of (A i)).tensor = T i := by
  let R (i : I) : Raw K S := Quotient.out (T i)
  let size (j : I × S) := Fintype.card ((R j.1).leg j.2)
  let d := Finset.univ.sup size
  have each (i : I) : ∃ f : (S → Fin d → Bool) → K, (of f).tensor = T i := by
    have h (s : S) : Fintype.card ((R i).leg s) ≤ 2 ^ d :=
      (Finset.le_sup (f := size) (Finset.mem_univ (i, s))).trans Nat.lt_two_pow_self.le
    obtain ⟨f, hf⟩ := representAt (R i) d h
    exact ⟨f, hf.trans (Quotient.out_eq _)⟩
  choose A hA using each
  exact ⟨d, A, hA⟩

end OAI.LinearAlgebra.MatrixExponent.Protocol.Binary
end

/-! # Composition of restrictions with bounded local implementations -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol.Binary

open Spectral Install Classical

variable {K S : Type} [Field K] [Fintype S] {D V W : Binary K S}

def compose (k : Action D V) (l : Action V W) : Action D W :=
  fun s x y => ∑ z, k s x z * l s z y

theorem compose_act (k : Action D V) (l : Action V W) (x : D.Assign) :
    act D W (compose k l) x = ∑ z : V.Assign, (∏ s, k s (x s) (z s)) * act V W l z := by
  simp only [act, compose, Fintype.prod_sum, Finset.sum_mul, Finset.prod_mul_distrib, Finset.mul_sum]
  rw [Finset.sum_comm]
  simp only [mul_assoc]

theorem Cheap.compose {k : Action D V} {l : Action V W} {b c : ℕ}
    (hk : Cheap D V k b) (hl : Cheap V W l c) :
    Cheap D W (compose k l) (12 * (D.size + V.size + W.size) + b + c) := by
  intro s
  let i : D.port s ⊕ V.port s → (D.port s ⊕ W.port s) ⊕ V.port s :=
    Sum.map Sum.inl id
  let j : V.port s ⊕ W.port s → (D.port s ⊕ W.port s) ⊕ V.port s :=
    Sum.elim Sum.inr (Sum.inl ∘ Sum.inr)
  have ht := (((hk s).pull i).mul ((hl s).pull j)).sum_out
  refine ht.mono ?_
  simp only [Fintype.card_sum]
  have := D.card_le s
  have := V.card_le s
  have := W.card_le s
  omega

theorem batch_size_le (D : Binary K S) (h : ℕ) : (batch (2 ^ h) D).size ≤ D.size * scale h := by
  have hcard (s : S) : Fintype.card ((batch (2 ^ h) D).port s) = 2 ^ h * Fintype.card (D.port s) :=
    (Fintype.card_prod _ _).trans (by simp)
  simp only [size, hcard, ← Finset.mul_sum]
  rw [mul_comm (2 ^ h)]
  unfold scale
  exact Nat.mul_le_mul_left _ (Nat.le_mul_of_pos_right _ (by positivity))

theorem cheap_batch_compose {h b c : ℕ} {k : Action (batch (2 ^ h) D) (batch (2 ^ h) V)}
    {l : Action (batch (2 ^ h) V) (batch (2 ^ h) W)}
    (hk : Cheap _ _ k (b * scale h)) (hl : Cheap _ _ l (c * scale h)) :
    Cheap _ _ (compose k l) ((12 * (D.size + V.size + W.size) + b + c) * scale h) := by
  apply (hk.compose hl).mono
  nlinarith only [batch_size_le D h, batch_size_le V h, batch_size_le W h]

variable [Nonempty S] {A : Type} [Fintype A] {U : A → Binary K S}

theorem Scalable.left (h : Scalable V U) (he : D.tensor ≤ V.tensor) : Scalable D U := by
  obtain ⟨l, hl⟩ := (single_action D V).mp he
  obtain ⟨c, h⟩ := h
  let b := 8 * 2 ^ (D.size + V.size)
  let size := ∑ i, (U i).size
  refine ⟨12 * (D.size + V.size + size) + b + c, fun n => ?_⟩
  obtain ⟨k, hk, he⟩ := h n
  let L := diagonalAction D V l (2 ^ n)
  refine ⟨fun i => compose L (k i), fun i => ?_, fun x => ?_⟩
  · have hs : (U i).size ≤ size :=
      Finset.single_le_sum (f := fun i => (U i).size) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
    apply (cheap_batch_compose (diagonal_cheap D V l n) (hk i)).mono
    apply Nat.mul_le_mul_right
    unfold b
    omega
  · simp_rw [compose_act]
    rw [Finset.sum_comm]
    simp only [← Finset.mul_sum, ← he]
    change _ = act _ _ L x
    rw [show act _ _ L x = _ from diagonal_act D V l (2 ^ n) x]
    change (∏ i, D.value (rows D (2 ^ n) x i)) = _
    exact Finset.prod_congr rfl fun i _ => hl (rows D (2 ^ n) x i)

theorem Scalable.right {V : A → Binary K S} (h : Scalable D U)
    (he : ∀ i, (U i).tensor ≤ (V i).tensor) : Scalable D V := by
  choose l hl using fun i => (single_action _ _).mp (he i)
  obtain ⟨b, h⟩ := h
  let c i := 12 * (D.size + (U i).size + (V i).size) + b + 8 * 2 ^ ((U i).size + (V i).size)
  refine ⟨∑ i, c i, fun n => ?_⟩
  obtain ⟨k, hk, he⟩ := h n
  let L i := diagonalAction (U i) (V i) (l i) (2 ^ n)
  refine ⟨fun i => compose (k i) (L i), fun i => ?_, fun x => ?_⟩
  · apply (cheap_batch_compose (hk i) (diagonal_cheap _ _ (l i) n)).mono
    exact Nat.mul_le_mul_right _ (Finset.single_le_sum (f := c) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i))
  · rw [he]
    apply Finset.sum_congr rfl
    intro i _
    rw [compose_act]
    apply Finset.sum_congr rfl
    intro y _
    refine congrArg _ ?_
    rw [show act _ _ (L i) y = _ from diagonal_act _ _ (l i) (2 ^ n) y]
    change (∏ j, (U i).value (rows (U i) (2 ^ n) y j)) = _
    exact Finset.prod_congr rfl fun j _ => hl i (rows (U i) (2 ^ n) y j)

end OAI.LinearAlgebra.MatrixExponent.Protocol.Binary
end

/-! # Tensor classes of flat boards -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol.Board

open Spectral Routing Classical

variable {K S T I : Type} [Field K] [Fintype S] [Nonempty S]

private def binPorts (A : Binary K S) (s : S) :
    A.port s ≃ (ofBinary A).localPort s where
  toFun i := ⟨⟨s, i⟩, rfl⟩
  invFun i := i.property ▸ i.val.2
  left_inv _ := rfl
  right_inv := by rintro ⟨⟨t, i⟩, rfl⟩; rfl

theorem tensor_ofBinary (A : Binary K S) : (ofBinary A).tensor = A.tensor :=
  Binary.tensor_relabel (binPorts A) (fun _ => rfl)

private def unionPorts [Fintype I] (A : I → Board K S) (s : S) :
    (Σ i, (A i).localPort s) ≃ (union A).localPort s where
  toFun j := ⟨⟨j.1, j.2.1⟩, j.2.2⟩
  invFun j := ⟨j.val.1, ⟨j.val.2, j.property⟩⟩
  left_inv _ := rfl
  right_inv _ := rfl

theorem tensor_union [Fintype I] (A : I → Board K S) :
    (union A).tensor = ∏ i, (A i).tensor := by
  unfold tensor
  rw [← Binary.tensor_of_product]
  exact Binary.tensor_relabel (unionPorts A) (fun _ => rfl)

theorem tensor_orders [Fintype I] (A : I → Board K S) (z : I → ℕ) :
    (orders A z).tensor = Stock.bundle (fun i => (A i).tensor) z := by
  rw [orders, tensor_union, Fintype.prod_sigma]
  simp [Stock.bundle]

theorem tensor_move [Fintype T] [Nonempty T] [DecidableEq S] [DecidableEq T]
    (D : Board K S) (f : S → T) :
    (D.move f).tensor = Tensor.place f D.tensor := by
  apply Tensor.ofRaw_eq
  constructor
  · refine .pullback (fun t x i => x ⟨D.owner i.val, i.property⟩ ⟨i.val, rfl⟩) fun x => ?_
    erw [Raw.coeff_group, Binary.raw_coeff, Binary.raw_coeff]
    rfl
  · refine .pullback (fun t x s i => x ⟨i.val, (congrArg f i.property).trans s.property⟩)
      fun x => ?_
    erw [Raw.coeff_group, Binary.raw_coeff, Binary.raw_coeff]
    rfl

private def baseLink (K : Type) [Field K] : Board K Bool where
  slot := Bool
  owner := id
  value x := if x false = x true then 1 else 0

private def oneBit (K : Type) [Field K] (s : Bool) :
    ((baseLink K).localPort s → Bool) ≃ Bool where
  toFun x := x ⟨s, rfl⟩
  invFun b _ := b
  left_inv x := by funext ⟨i, h⟩; change i = s at h; subst i; rfl
  right_inv _ := rfl

private theorem tensor_baseLink (K : Type) [Field K] :
    (baseLink K).tensor = Tensor.wire K false true 2 := by
  rw [Tensor.wire, show ({false, true} : Finset Bool) = Finset.univ by decide,
    Tensor.shared_all, ← Fintype.card_bool, ← Tensor.diag_eq_natCast]
  apply Tensor.ofRaw_eq
  refine Raw.equiv_coeff (oneBit K) fun x => ?_
  rw [Binary.raw_coeff]
  let v (s : Bool) := oneBit K s (x s)
  change (if v false = v true then (1 : K) else 0) =
    ∑ j : Bool, ∏ s : Bool, if v s = j then 1 else 0
  simp [mul_ite]
  simp only [eq_comm (a := v true)]

theorem tensor_link [DecidableEq S] (K : Type) [Field K] (a b : S) :
    (link K a b).tensor = Tensor.wire K a b 2 := by
  let f (i : Bool) := if i then b else a
  change ((baseLink K).move f).tensor = _
  rw [tensor_move, tensor_baseLink, Tensor.place_wire]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Protocol.Board
end

/-!
# Repeating a single restriction by independent local maps
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Classical
variable {K S : Type} [Field K] [Fintype S] [Nonempty S]

theorem Binary.single_scalable (D V : Binary K S) (he : D.tensor ≤ V.tensor) :
    D.Scalable (fun _ : Unit => V) := by
  obtain ⟨k, hk⟩ := (Binary.single_action D V).mp he
  refine ⟨8 * 2 ^ (D.size + V.size), fun h =>
    ⟨fun _ => Binary.diagonalAction D V k (2 ^ h), fun _ => D.diagonal_cheap V k h, fun x => ?_⟩⟩
  rw [Fintype.sum_unique, Binary.diagonal_act]
  change (∏ i : Fin (2 ^ h), D.value (D.rows _ x i)) = ∏ i, D.act V k (D.rows _ x i)
  exact Finset.prod_congr rfl fun i _ => hk (D.rows _ x i)

def Board.single (D V : Board K S) (he : D.tensor ≤ V.tensor) :
    D.Expansion (fun _ : Unit => V) :=
  Board.realize D _ (Binary.single_scalable D.binary V.binary he)

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Local and global bit presentations of the same commodities -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol

open Spectral Routing Classical

variable {K S I : Type} [Field K] [Fintype S] [Nonempty S] {N : ℕ}

def commodity (A : Finset (Tensor K S)) (i : Fin A.card) : Board K S :=
  Board.ofBinary (Binary.of ((Binary.represent (fun j => (A.equivFin.symm j).val)).choose_spec.choose i))

theorem tensor_commodity (A : Finset (Tensor K S)) (i : Fin A.card) :
    (commodity A i).tensor = (A.equivFin.symm i).val := by
  rw [commodity, Board.tensor_ofBinary]
  exact (Binary.represent (fun j => (A.equivFin.symm j).val)).choose_spec.choose_spec i

variable (s : Shape N) (b : Market I N) (A : Finset (Tensor K S))

def localRequest : s.Req A → Board K (Fin s.1.val)
  | none => Board.link K s.2.src s.2.dst
  | some (z, j) => (commodity A j).move z

def localEdge (K : Type) [Field K] (s : Shape N) (e : s.2.edges) : Board K (Fin s.1.val) :=
  Board.link K e.val.1 e.val.2

def goods : s.2.Goods A → Board K (Fin s.1.val) :=
  Sum.elim (localRequest s A) (localEdge K s)

def request : b.Request A → Board K I
  | .inl i => Board.link K i (b.name i (b.shape i).dst)
  | .inr (z, j) => (commodity A j).move z.val

def edge (K : Type) [Field K] (b : Market I N) (e : b.Edge) : Board K I :=
  Board.link K (b.name e.1 e.2.val.1) (b.name e.1 e.2.val.2)

def request_move (i : I) (j : (b.code i).Req A) :
    Board.Rename ((localRequest (b.code i) A j).move (b.name i)) (request b A (b.request A i j)) := by
  cases j with
  | none =>
    refine ⟨Equiv.refl Bool, ?_, fun _ => rfl⟩
    intro x
    cases x
    · exact (b.origin i).symm
    · rfl
  | some z => exact .refl _

def edge_move (K : Type) [Field K] (b : Market I N) (i : I) (e : (b.shape i).edges) :
    Board.Rename ((localEdge K (b.code i) e).move (b.name i)) (edge K b ⟨i, e⟩) :=
  ⟨Equiv.refl Bool, by intro x; cases x <;> rfl, fun _ => rfl⟩

variable [DecidableEq S] [Nonempty (Fin s.1.val)]

theorem tensor_goods (j : s.2.Goods A) : (goods s A j).tensor = s.2.tensor A j := by
  rcases j with (_ | ⟨z, i⟩) | e
  · exact Board.tensor_link K _ _
  · change ((commodity A i).move z).tensor = _
    rw [Board.tensor_move, tensor_commodity]
    rfl
  · exact Board.tensor_link K _ _

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-!
# Terminal kernels for fixed local routes

Choose the implementing restriction on the bounded shape before
placing it at global labels. Placement preserves all port names.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Spectral Routing
open scoped Classical

variable {K I S : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype I] [DecidableEq I] {N t : ℕ} (A : Finset (Tensor K S)) (d M : ℕ)

def localSupply (s : Shape N) (x : s.Req A)
    (h : s.2.Direct K (s.2.tensor A (.inl x)) (s.priceCap A d M x)) :
    (localRequest s A x).Expansion (fun _ : Unit => Board.orders (localEdge K s) (s.route A d M x)) := by
  let _ : Nonempty (Fin s.1.val) := ⟨s.2.src⟩
  apply Board.single
  rw [Board.tensor_orders]
  have he : (fun i => (localEdge K s i).tensor) = s.2.wire K :=
    funext fun i => tensor_goods s A (.inr i)
  rw [he, show (localRequest s A x).tensor = s.2.tensor A (.inl x) from tensor_goods s A (.inl x)]
  exact (s.route_spec A d M x h).2

variable (b : Market I N) (g : b.Ports t) (hr : b.ready A d) (hc : UniformCap N A M)

def fromTally (u : b.Source A) : b.Edge → ℕ :=
  Stock.collect (fun e => ⟨u.1, e⟩) ((b.code u.1).route A d M u.2)

include hr hc in
def supplyFrom (x : b.Request A) (u : b.Source A) (he : b.request A u.1 u.2 = x) :
    (request b A x).Expansion (fun _ : Unit => Board.orders (edge K b) (fromTally A d M b u)) := by
  let z := (b.code u.1).route A d M u.2
  let f (e : (b.shape u.1).edges) : b.Edge := ⟨u.1, e⟩
  have hf : Function.Injective f := fun _ _ e => eq_of_heq (Sigma.mk.inj e).2
  let v := localSupply A d M (b.code u.1) u.2 (b.local_route A d M hr hc _ _)
  let h₁ : Board.Rename ((localRequest (b.code u.1) A u.2).move (b.name u.1)) (request b A x) :=
    he ▸ request_move b A u.1 u.2
  let h₂ : Board.Rename ((Board.orders (localEdge K (b.code u.1)) z).move (b.name u.1))
      (Board.orders (edge K b ∘ f) z) :=
    Board.Rename.union fun p : Σ e, Fin (z e) => edge_move K b u.1 p.1
  exact (v.place (b.name u.1)).rename h₁ fun _ =>
    h₂.trans (Board.orders_collect (edge K b) f hf z).symm

include hr hc in
def supplyAt (x : b.Request A) :
    (request b A x).Expansion (fun _ : Unit => Board.orders (edge K b) (b.tally A d M g x)) :=
  supplyFrom A d M b hr hc x (b.depot A g x) (b.depot_spec A g x).1

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-!
# Supplying a full terminal inventory

Copies using an edge are numbered by the local request at its depot
and the ordinal of the copy. The ordering therefore depends only
on data at that center.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Spectral Routing
open scoped Classical

variable {K I S : Type} [Field K] [Fintype S]

def Board.Expansion.singly [Fintype I] {D V : I → Board K S}
    (r : ∀ i, (D i).Expansion (fun _ : Unit => V i)) :
    (Board.union D).Expansion (fun _ : Unit => Board.union V) := by
  let a := Board.Expansion.parallel r
  exact ⟨fun _ => a.kernel default, fun _ => a.fast default, fun h x => by
    rw [a.identity]
    simp only [Fintype.sum_unique]⟩

variable [DecidableEq S] [Nonempty S] [Fintype I] [DecidableEq I] {N t : ℕ}
  (A : Finset (Tensor K S)) (d M : ℕ) (b : Market I N) (g : b.Ports t)

theorem tally_origin (x : b.Request A) (e : b.Edge) (h : b.tally A d M g x e ≠ 0) :
    (b.depot A g x).1 = e.1 := by
  obtain ⟨j, hj, _⟩ := Stock.collect_nonzero h
  exact congrArg Sigma.fst hj

def supplyIndex (x : b.Source A) := (Fintype.equivFin ((b.code x.1).Req A) x.2).val

omit [Fintype I] [DecidableEq I] [Nonempty S] in
private theorem supplyIndex_inj (x y : b.Source A) (he : x.1 = y.1)
    (h : supplyIndex A b x = supplyIndex A b y) : x = y := by
  rcases x with ⟨i, x⟩
  rcases y with ⟨j, y⟩
  change i = j at he
  subst j
  have e : x = y := (Fintype.equivFin ((b.code i).Req A)).injective (Fin.ext h)
  rw [e]

variable (z : b.Request A → ℕ)
abbrev Units := Σ i, Fin (z i)

def supplyKey (x : Units A b z) :=
  Encodable.encode (supplyIndex A b (b.depot A g x.1), x.2.val)

theorem supplyOrdered (e : b.Edge) :
    Ordered (fun x : Units A b z => b.tally A d M g x.1 e) (supplyKey A b g z) := by
  rintro ⟨x, i⟩ ⟨y, j⟩ hx hy hh
  have h := Encodable.encode_injective hh
  have hs := supplyIndex_inj A b _ _
    ((tally_origin A d M b g x e hx).trans (tally_origin A d M b g y e hy).symm)
    (congrArg Prod.fst h)
  have he : x = y := (b.depot_spec A g x).1.symm.trans
    ((congrArg (b.requestOf A) hs).trans (b.depot_spec A g y).1)
  subst y
  have hij : i = j := Fin.ext (congrArg Prod.snd h)
  rw [hij]

def terminal (hr : b.ready A d) (hc : UniformCap N A M) :
    (Board.orders (request b A) z).Expansion
      (fun _ : Unit => Board.orders (edge K b) (fun e => ∑ i, b.tally A d M g i e * z i)) := by
  let Y (i : Units A b z) := b.tally A d M g i.1
  let r := Board.Expansion.singly (fun j : Units A b z => supplyAt A d M b g hr hc j.1)
  let u := Board.orders_sum (edge K b) Y (fun e => (pack _ _ (supplyOrdered A d M b g z e)).symm)
  have he : (fun e => ∑ j, Y j e) = (fun e => ∑ i, b.tally A d M g i e * z i) := by
    funext e
    simp only [Y, Units, Fintype.sum_sigma, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul, Nat.cast_id]
    exact Finset.sum_congr rfl fun _ _ => mul_comm _ _
  exact r.rename (.refl _) fun _ => u.symm.trans (Board.orders_eq (edge K b) he)

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-!
# Compiling an inventory schedule to local maps

Reserve the remaining payload as part of the stock. Core edges of
each step precede the later ones in the final enumeration.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol

open Board Routing

variable {K S I E : Type} [Field K] [Fintype S] [Fintype I] [DecidableEq I] [Fintype E]
  (T : I → Board K S) (V : E → Board K S)
  (L : Finset I) (Q : (I → ℕ) → Intervention I E) (Y : I → E → ℕ)

abbrev Settlement := ∀ z : I → ℕ, Expansion (orders T z)
  (fun _ : Unit => orders V (fun e => ∑ i, Y i e * z i))

variable (close : Settlement T V Y) (run : ∀ z, Executes T V (Q z))

def execute {a : I → ℝ} {budget : ℝ} (k : ℕ) (z : I → ℕ) (v : ℝ)
    (h : Runs L a Q budget k z v) :
    Expansion (orders T (z + Stock.copies L k))
      (fun j : Branch L Q k z => orders V (edges L Q Y k z j)) := by
  cases k with
  | zero =>
    have he : z = z + Stock.copies L 0 := by ext i; simp [Stock.copies]
    exact (close z).rename (orders_eq T he) (fun _ => .refl _)
  | succ k =>
    let q := Q z
    let Z := z + Stock.copies L (k + 1)
    let z' j := q.next z j + Stock.copies L 1
    have hq : q.take ≤ Z := fun i => (h.1 i).trans (Nat.le_add_right _ _)
    have he (j : q.choice) : z' j + Stock.copies L k = q.next Z j := by
      funext i
      have hh : q.take i ≤ z i := h.1 i
      by_cases hi : i ∈ L <;> simp [Intervention.next, Stock.copies, z', Z, hi]
      omega
    let first := (run z).takeStep Z hq
    let rest (j : q.choice) := execute k (z' j) (v + q.cost j) (h.2 j)
    let finish (j : q.choice) : Expansion ((orders T (q.next Z j)).join (orders V (q.core j)))
        (fun i : Branch L Q k (z' j) => orders V (q.core j + edges L Q Y k (z' j) i)) :=
      ((rest j).keep _).rename ((orders_eq T (he j)).join (.refl _)) fun i =>
        (swap _ _).trans (orders_add V _ _).symm
    exact first.comp finish

def execute_start {a : I → ℝ} {budget : ℝ} {k : ℕ} (h : Runs L a Q budget k 0 0) :
    Expansion (orders T (Stock.copies L k))
      (fun j : Branch L Q k 0 => orders V (edges L Q Y k 0 j)) :=
  (execute T V L Q Y close run k 0 0 h).rename (orders_eq T (zero_add _)) (fun _ => .refl _)

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-!
# Scalable local substitutions

The fixed alphabet of rounded histograms serves every scale. The supply
bundle pays separately for the common selector and the goods of each letter.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol

open Spectral Routing Routing.Stock Finset

variable {K S I : Type} [Field K] [Fintype S] [Nonempty S] [Fintype I] [DecidableEq I]
  {T : I → Tensor K S} {H : ℝ}

theorem flex_scalable
    (q : Proposal T H) (u : Finset I)
    (hu : (2 : Tensor K S) ≤ ∏ i ∈ u, T i) (hT : ∀ i, 1 ≤ T i)
    (b : ℕ) (hb : Fintype.card q.move.letter ≤ 2 ^ b) (D : Binary K S)
    (V : ↥(histograms q.move.letter (2 ^ b + Fintype.card q.move.letter)) → Binary K S)
    (hd : D.tensor ≤ bundle T (Stock.copies q.demand (q.move.block * 2 ^ b)))
    (hv : ∀ t, bundle T (q.output u (2 ^ b + Fintype.card q.move.letter) t.val) ≤ (V t).tensor) :
    Binary.Scalable D V := by
  classical
  let : MulLeftMono (Tensor K S) := ⟨fun c a b h => Tensor.mul_le_mul_left _ _ _ h⟩
  have lo (s : Finset I) (n : ℕ) : 1 ≤ (∏ i ∈ s, T i) ^ n := by
    exact one_le_pow_of_one_le' (one_le_prod fun i _ => hT i) _
  have hn : Nonempty q.move.letter := by
    by_contra! h
    have h₁ := (lo q.demand q.move.block).trans q.move.covers
    rw [sum_of_isEmpty] at h₁
    exact one_ne_zero (le_antisymm h₁ (Tensor.zero_le _))
  obtain ⟨_, F, hF⟩ := Binary.represent (fun _ : Unit => (∏ i ∈ q.demand, T i) ^ q.move.block)
  obtain ⟨_, G, hG⟩ := Binary.represent (fun j => bundle T (q.orders j))
  have cover : (Binary.of (F ())).tensor ≤ ∑ j, (Binary.of (G j)).tensor := by
    simp only [hF, hG, Proposal.orders, bundle_collect]
    exact q.move.covers
  have goods (j) : 1 ≤ (Binary.of (G j)).tensor := by
    rw [hG]
    exact one_le_prod fun i _ => one_le_pow_of_one_le' (hT i) _
  have cost : (Fintype.card q.move.letter : Tensor K S) ≤ (∏ i ∈ u, T i) ^ q.move.bits := by
    refine (Tensor.natCast_le q.move.fits).trans ?_
    rw [Nat.cast_pow, Nat.cast_ofNat]
    exact pow_le_pow_left' hu _
  have h := word_scalable (F ()) G hn.some cover goods b hb
  refine (h.left ?_).right fun t => (offer_bound G _ _).trans (le_trans ?_ (hv t))
  · rw [Binary.tensor_of_batch, hF, ← pow_mul, ← bundle_copies]
    exact hd
  · simp only [hG]
    unfold Proposal.output
    rw [bundle_add, bundle_copies, bundle_sum, pow_mul]
    apply mul_le_mul_left
    exact (pow_le_pow_left' cost _).trans
      (pow_le_pow_right' (lo u q.move.bits) (Nat.le_add_right _ _))

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-!
# Local implementations for the finite menu of shapes

Choose the scalable maps on the canonical shape. Moving to another
market changes only the site and slot names.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol

open Spectral Routing Board Stock Classical

variable {K S I : Type} [Field K] [Fintype S] [Nonempty S] [DecidableEq S]
  {N : ℕ} (s : Shape N) (A : Finset (Tensor K S))

/-- This choice uses only the shape and move, independently of the
location or total number of sites in the ambient market. -/
def localAction (q : s.Move A) (h : ℕ) (ha : 0 ∉ A) (hb : Fintype.card q.move.letter ≤ 2 ^ h) :
    Expansion (orders (goods s A) (Stock.copies q.demand (q.move.block * 2 ^ h)))
      (fun t : ↥(histograms q.move.letter (2 ^ h + Fintype.card q.move.letter)) =>
        orders (goods s A) (q.output (s.2.links A) (2 ^ h + Fintype.card q.move.letter) t.val)) := by
  let _ : Nonempty (Fin s.1.val) := ⟨s.2.src⟩
  apply Board.realize
  have eq (z : s.2.Goods A → ℕ) :
      (orders (goods s A) z).binary.tensor = bundle (s.2.tensor A) z := by
    change (orders (goods s A) z).tensor = _
    rw [tensor_orders, show (fun i => (goods s A i).tensor) = s.2.tensor A from
      funext (tensor_goods s A)]
  exact flex_scalable q _ (s.2.broadcast A) (fun j => Tensor.one_le _ (s.2.nonzero A ha j))
    h hb _ _ (eq _).le (fun t => (eq _).ge)

variable [Fintype I] [DecidableEq I] (b : Market I N) (i : I)

def globalBoard : b.Good A → Board K I := Sum.elim (request b A) (edge K b)

def goods_move (j : (b.shape i).Goods A) :
    Rename ((goods (b.code i) A j).move (b.name i)) (globalBoard A b (b.assign A i j)) :=
  match j with
  | .inl r => request_move b A i r
  | .inr e => edge_move K b i e

local instance : DecidableEq (b.Good A) := @instDecidableEqSum (b.Request A) b.Edge inferInstance inferInstance

def post (z : (b.shape i).Goods A → ℕ) :
    Rename ((orders (goods (b.code i) A) z).move (b.name i))
      ((orders (request b A) (collect (b.assign A i) z ∘ Sum.inl)).join
        (orders (edge K b) (collect (b.assign A i) z ∘ Sum.inr))) :=
  (Rename.union (fun r : Σ j, Fin (z j) => goods_move A b i r.1)).trans <|
    (orders_collect (globalBoard A b) (b.assign A i) (b.assign_injective A i) z).symm.trans
      (orders_split (globalBoard A b) _)

def Board.dropEmpty {E : Type} [Fintype E] (D : Board K I) (V : E → Board K I)
    (z : E → ℕ) (hz : ∀ e, z e = 0) : Rename (D.join (orders V z)) D := by
  letI : IsEmpty (Σ i, Fin (z i)) := ⟨fun p => Fin.elim0 (Fin.cast (hz _) p.2)⟩
  letI : IsEmpty (orders V z).slot := ⟨fun p => isEmptyElim p.1⟩
  refine ⟨Equiv.sumEmpty _ _, ?_, fun x => ?_⟩
  · rintro (j|j)
    · rfl
    · exact isEmptyElim j
  · change D.value x * (∏ r : Σ j, Fin (z j), _) = _
    rw [Finset.prod_of_isEmpty, mul_one]

def applyMove (q : (b.code i).Move A) (h : ℕ) (ha : 0 ∉ A)
    (hb : Fintype.card q.move.letter ≤ 2 ^ h)
    (hd : ∀ j ∈ q.demand, ∃ l, b.assign A i j = .inl l) :
    Executes (request b A) (edge K b) (q.flex (b.assign A i) ((b.shape i).links A) (2 ^ h)) := by
  let r := (localAction (b.code i) A q h ha hb).place (b.name i)
  let d := Stock.copies q.demand (q.move.block * 2 ^ h)
  let e := (post A b i d).trans (Board.dropEmpty _ _ _ (q.take_core (b.assign A i) (2 ^ h) hd))
  exact r.rename e (fun _ => post A b i _)

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Identifying the initial payload requests with permutation wires -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Spectral Routing Board Classical

variable {F S : Type} [Field F] [Fintype S] [Nonempty S] [DecidableEq S] {h N : ℕ}

local instance : DecidableEq (Transport.Site h) := Classical.decEq _

def demandRename (b : Market (Transport.Site h) N) (A : Finset (Tensor F S))
    (σ : Coloring.B h → Coloring.B h) (W : ℕ)
    (hσ : ∀ i, b.name i (b.shape i).dst = inflate h σ i) :
    Rename (orders (request b A) (Stock.copies (b.payload A) W)) (Demand F σ W) := by
  let m := Stock.copies (b.payload A) W
  have hl : m ∘ Sum.inl = fun _ : Transport.Site h => W := by
    funext i
    simp [m, Stock.copies, Market.payload]
  have hr : ∀ i, (m ∘ Sum.inr) i = 0 := by
    intro i
    simp [m, Stock.copies, Market.payload]
  let first := (orders_split (request b A) m).trans (dropEmpty _ _ _ hr)
  let name (i : Transport.Site h) : Rename (request b A (.inl i)) (Board.link F i (inflate h σ i)) :=
    ⟨Equiv.refl Bool, fun v => by cases v <;> first | rfl | exact (hσ i).symm, fun _ => rfl⟩
  exact (first.trans (orders_eq _ hl)).trans (Rename.union (fun j : Σ _ : Transport.Site h, Fin W =>
    name j.1))

theorem demandRename_apply (b : Market (Transport.Site h) N) (A : Finset (Tensor F S))
    (σ : Coloring.B h → Coloring.B h) (W : ℕ)
    (hσ : ∀ i, b.name i (b.shape i).dst = inflate h σ i)
    (i : Transport.Site h) (u : Fin (Stock.copies (b.payload A) W (.inl i)))
    (j : Fin W) (he : u.val = j.val) (v : Bool) :
    (demandRename b A σ W hσ).eqv ⟨⟨.inl i, u⟩, v⟩ = ⟨⟨i, j⟩, v⟩ := by
  obtain ⟨u, hu⟩ := u
  obtain ⟨j, hj⟩ := j
  change u = j at he
  subst j
  rfl

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Implementing the protocol at all dyadic widths -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol

open Spectral Routing
open scoped Classical

variable {K I S : Type} [Field K] [Fintype S] [Nonempty S] [DecidableEq S]
  [Fintype I] [DecidableEq I] {N M t : ℕ} {ρ : ℝ} (b : Market I N)
  {A : Finset (Tensor K S)} (a : Atlas N A M ρ) (g : b.Ports t)
  (h : ℕ) (ha : 0 ∉ A) (hh : a.Room (2 ^ h))

def perform (p : b.Request A → ℝ) :
    Executes (request b A) (edge K b) (b.policy a p (2 ^ h)) :=
  Executes.parallel (b.allocation a p (2 ^ h) g) fun i =>
    applyMove A b i (b.moveAt a p i) h ha (hh _ _ (b.moving a p i).1).1 (b.demand_slot a p i)

variable (μ d W : ℕ) (hr : b.ready A d) (hc : UniformCap N A M)
  (hw : Runs (b.payload A) (b.cap A d M) (b.decision a μ d (2 ^ h))
    (1203 * Fintype.card I * W) W 0 0)

def program :
    (Board.orders (request b A) (Stock.copies (b.payload A) W)).Expansion
      (fun j : Branch (b.payload A) (b.decision a μ d (2 ^ h)) W 0 =>
        Board.orders (edge K b)
          (edges (b.payload A) (b.decision a μ d (2 ^ h)) (b.tally A d M g) W 0 j)) :=
  execute_start _ _ _ _ _ (fun z => terminal A d M b g z hr hc)
    (fun z => perform b a g h ha hh (fun i => price μ (b.cap A d M i) (z i))) hw

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-!
# Local comparison of two inventory protocols

Only charts meeting the marked site can contribute nontrivial factors
there. Keep their shape and focus, and the identifications of all
incident commodity and core pins.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Routing Spectral Classical

variable {K S I I' : Type} [Field K] [Fintype S] [Nonempty S] [DecidableEq S]
  {N : ℕ} (A : Finset (Tensor K S))

abbrev Near (b : Market I N) (s : I) := Σ i : I, {u : Fin (b.size i).val // b.name i u = s}

def placeReq {b : Market I N} {s : I} (j : Near b s)
    (l : Pin (localRequest (b.code j.1) A) j.2.1) : Pin (request b A) s :=
  ⟨b.request A j.1 l.1, (request_move b A j.1 l.1).local s
    (Board.movePort _ (b.name j.1) j.2 l.2)⟩

def placeEdge (K : Type) [Field K] {b : Market I N} {s : I} (j : Near b s)
    (l : Pin (localEdge K (b.code j.1)) j.2.1) : Pin (edge K b) s :=
  ⟨⟨j.1, l.1⟩, (edge_move K b j.1 l.1).local s
    (Board.movePort _ (b.name j.1) j.2 l.2)⟩

structure Match (b : Market I N) (c : Market I' N) (s : I) (v : I') where
  req : Pin (request b A) s ≃ Pin (request c A) v
  core : Pin (edge K b) s ≃ Pin (edge K c) v
  near : Near b s ≃ Near c v
  same : ∀ j, b.code j.1 = c.code (near j).1
  focus : ∀ j, j.2.1.val = (near j).2.1.val
  req_eq : ∀ j l l', HEq l l' → req (placeReq A j l) = placeReq A (near j) l'
  core_eq : ∀ j l l', HEq l l' → core (placeEdge K j l) = placeEdge K (near j) l'

variable [Fintype I] [Fintype I'] [DecidableEq I] [DecidableEq I']
  {A} {b : Market I N} {c : Market I' N} {s : I} {v : I'}
  {t t' : ℕ} (r : Match A b c s v) (g : b.Ports t) (g' : c.Ports t')

def Match.keys : Prop :=
  ∀ (j : Near b s) (x : Pin (request b A) s),
    g.key (b.home A x.1) j.1 = g'.key (c.home A (r.req x).1) (r.near j).1

def Match.depots : Prop :=
  ∀ (j : Near b s) (x : (b.code j.1).Req A) (x' : (c.code (r.near j).1).Req A),
    HEq x x' →
    ((b.depot A g (b.request A j.1 x)).1 = j.1 ↔
      (c.depot A g' (c.request A (r.near j).1 x')).1 = (r.near j).1)

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Transport of a local kernel and its individual pins -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Routing Spectral Classical

namespace Board

variable {K S T I : Type} [Field K] [Fintype S] [Fintype T] [Fintype I]
  {D : Board K S} {V : I → Board K S} (r : Expansion D V) (f : S ↪ T) {s : T}

theorem Expansion.placed (j : {i // f i = s}) (t : I) :
    (r.place f).kernel t s = (r.kernel t j.val).pull (movePort D f j) (movePort (V t) f j) := by
  funext h x y
  apply Fintype.prod_eq_single j
  intro i hi
  exact (hi (Subtype.ext (f.injective (i.property.trans j.property.symm)))).elim

theorem Expansion.absent (hj : ∀ i, f i ≠ s) (t : I) :
    (r.place f).kernel t s = (fun _ _ _ => 1) := by
  funext h x y
  exact Finset.prod_eq_one fun i _ => (hj i i.property).elim

omit [Field K] [Fintype S] [Fintype T] in
theorem Rename.find_source {Q : Board K T} (e : Rename (D.move f) Q) (x : Q.localPort s) :
    ∃ (i : {i // f i = s}) (p : D.localPort i.val), e.local s (movePort D f i p) = x := by
  let y := e.symm.local s x
  refine ⟨⟨D.owner y.val, y.property⟩, ⟨y.val, rfl⟩, ?_⟩
  exact Subtype.ext (e.eqv.apply_symm_apply x.val)

end Board

variable {K S I I' : Type} [Field K] [Fintype S] [Nonempty S]
  {N : ℕ} {b : Market I N} {c : Market I' N} {s : I} {v : I'} {A : Finset (Tensor K S)}

abbrev Spot (N : ℕ) := Σ x : Shape N, Fin x.1.val
def spot (j : Near b s) : Spot N := ⟨b.code j.1, j.2.1⟩

theorem Match.spot_eq (r : Match A b c s v) (j : Near b s) :
    spot j = spot (r.near j) :=
  Sigma.ext (r.same j) ((Fin.heq_ext_iff (congrArg (fun x : Shape N => x.1.val) (r.same j))).mpr
    (r.focus j))

def Match.symm (r : Match A b c s v) : Match A c b v s where
  req := r.req.symm
  core := r.core.symm
  near := r.near.symm
  same j := by simpa using (r.same (r.near.symm j)).symm
  focus j := (congrArg (fun v : Near c _ => v.2.1.val) (r.near.apply_symm_apply j)).symm.trans
    (r.focus (r.near.symm j)).symm
  req_eq j x y he := by
    apply r.req.symm_apply_eq.mpr
    have h := r.req_eq (r.near.symm j)
    rw [r.near.apply_symm_apply] at h
    exact (h _ _ he.symm).symm
  core_eq j x y he := by
    apply r.core.symm_apply_eq.mpr
    have h := r.core_eq (r.near.symm j)
    rw [r.near.apply_symm_apply] at h
    exact (h _ _ he.symm).symm

theorem placeReq_surj (x : Pin (request b A) s) (i : I) (j : (b.code i).Req A)
    (h : b.request A i j = x.1) :
    ∃ (u : {u // b.name i u = s}) (p : (localRequest (b.code i) A j).localPort u.val),
      placeReq A (⟨i, u⟩ : Near b s) ⟨j, p⟩ = x := by
  obtain ⟨k, x⟩ := x
  change _ = k at h
  subst k
  obtain ⟨u, p, hp⟩ := Board.Rename.find_source (b.name i) (request_move b A i j) x
  exact ⟨u, p, congrArg (Sigma.mk _) hp⟩

theorem placeEdge_surj (x : Pin (edge K b) s) (i : I) (j : (b.shape i).edges)
    (h : ⟨i, j⟩ = x.1) :
    ∃ (u : {u // b.name i u = s}) (p : (localEdge K (b.code i) j).localPort u.val),
      placeEdge K (⟨i, u⟩ : Near b s) ⟨j, p⟩ = x := by
  obtain ⟨k, x⟩ := x
  change _ = k at h
  subst k
  obtain ⟨u, p, hp⟩ := Board.Rename.find_source (b.name i) (edge_move K b i j) x
  exact ⟨u, p, congrArg (Sigma.mk _) hp⟩

end OAI.LinearAlgebra.MatrixExponent.Protocol
end
