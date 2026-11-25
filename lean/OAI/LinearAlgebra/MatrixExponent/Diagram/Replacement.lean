import OAI.LinearAlgebra.MatrixExponent.Diagram.Basic
import OAI.LinearAlgebra.MatrixExponent.CompareExchange
import OAI.LinearAlgebra.MatrixExponent.Spectral.Rule

section
/-! # Comparing size and volume conventions -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagram

variable {F : Type} {a b : Wire} (G : Diagram F a b)

/-- Each internal edge contributes two argument positions and each
exterior bit contributes one. -/
theorem sum_arity : ∑ v, G.arity v = wd a + wd b + 2 * Fintype.card G.E := by
  have hi := Fintype.card_congr G.src
  have ho := Fintype.card_congr G.dst
  simp only [Fintype.card_sigma, Fintype.card_sum, card_slots] at hi ho
  simp only [arity, Finset.sum_add_distrib]
  omega

theorem cost_eq : G.cost = Fintype.card G.V + wd a + wd b + 2 * Fintype.card G.E := by
  simp [cost, Finset.sum_add_distrib, G.sum_arity, add_assoc]

theorem cost_trivalent (h : G.Trivalent) : G.cost ≤ 4 * Fintype.card G.V := by
  calc
    _ ≤ ∑ _ : G.V, 4 := Finset.sum_le_sum (fun v _ => Nat.add_le_add_left (h v) 1)
    _ = _ := by simp [mul_comm]

/-- Wire-inclusive volume is at most three times vertices plus exterior bits. -/
theorem volume_trivalent (h : G.Trivalent) :
    Fintype.card G.V + Fintype.card G.E + wd a + wd b ≤
      3 * (Fintype.card G.V + wd a + wd b) := by
  have := G.cost_trivalent h
  rw [cost_eq] at this
  omega

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

section
/-!
# A bipartite presentation

Insert one binary equality table on each internal and external wire.
Each of the original argument positions now has its own edge. All
these edges join an original vertex and a junction. Exterior positions
have distinct equality leaves and even an old loop is subdivided.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagram

variable {F : Type} {a b : Wire} (G : Diagram F a b)

abbrev Joint := slots a ⊕ slots b ⊕ G.E
abbrev End := (slots a ⊕ G.E) ⊕ slots b ⊕ G.E

def junction : G.End → G.Joint
  | .inl (.inl i) => .inl i
  | .inl (.inr e) => .inr (.inr e)
  | .inr (.inl j) => .inr (.inl j)
  | .inr (.inr e) => .inr (.inr e)

def station : G.End → G.V :=
  Sum.elim (fun i => (G.src.symm i).1) (fun j => (G.dst.symm j).1)

private def srcNorm : (slots a ⊕ G.E) ⊕ G.Joint ≃ slots a ⊕ G.End where
  toFun
    | .inl i => .inr (.inl i)
    | .inr (.inl i) => .inl i
    | .inr (.inr j) => .inr (.inr j)
  invFun
    | .inl i => .inr (.inl i)
    | .inr (.inl i) => .inl i
    | .inr (.inr j) => .inr (.inr j)
  left_inv := by rintro (i | i | j) <;> rfl
  right_inv := by rintro (i | i | j) <;> rfl

private def dstNorm : (slots b ⊕ G.E) ⊕ G.Joint ≃ slots b ⊕ G.End where
  toFun
    | .inl j => .inr (.inr j)
    | .inr (.inl i) => .inr (.inl (.inl i))
    | .inr (.inr (.inl j)) => .inl j
    | .inr (.inr (.inr e)) => .inr (.inl (.inr e))
  invFun
    | .inl j => .inr (.inr (.inl j))
    | .inr (.inl (.inl i)) => .inr (.inl i)
    | .inr (.inl (.inr e)) => .inr (.inr (.inr e))
    | .inr (.inr j) => .inl j
  left_inv := by rintro (j | i | j | e) <;> rfl
  right_inv := by rintro (j | (i | e) | j) <;> rfl

abbrev normalized [Field F] : Diagram F a b where
  V := G.V ⊕ G.Joint
  E := G.End
  table := Sum.elim G.table (fun _ => ⟨.bit, .bit, fun i j => if i = j then 1 else 0⟩)
  src := (Equiv.sumSigmaDistrib _).trans
    ((G.src.sumCongr (Equiv.sigmaUnique G.Joint (fun _ => Unit))).trans G.srcNorm)
  dst := (Equiv.sumSigmaDistrib _).trans
    ((G.dst.sumCongr (Equiv.sigmaUnique G.Joint (fun _ => Unit))).trans G.dstNorm)

theorem card_end : Fintype.card G.End = wd a + wd b + 2 * Fintype.card G.E := by
  simp only [End, Fintype.card_sum, card_slots]
  omega

theorem card_joint : Fintype.card G.Joint = wd a + wd b + Fintype.card G.E := by
  simp only [Joint, Fintype.card_sum, card_slots, add_assoc]

variable [Field F]

theorem cost_normalized : G.normalized.cost ≤ 4 * G.cost := by
  rw [cost_eq, cost_eq, Fintype.card_sum, card_joint, card_end]
  omega

theorem admits_normalized {u : ℕ} {L : Set (Table F)} (hu : 2 ≤ u) (h : G.Admits u L) :
    G.normalized.Admits u L := by
  rintro (v|v)
  · exact h v
  · exact ⟨hu, Or.inl (by change 2 ≤ 3; decide)⟩

theorem trivalent_normalized (h : G.Trivalent) : G.normalized.Trivalent := by
  rintro (v|v)
  · exact h v
  · change 2 ≤ 3
    decide

theorem bipartite (e : G.End) :
    G.normalized.source e = Sum.inl (G.station e) ∧
      G.normalized.target e = Sum.inr (G.junction e) ∨
    G.normalized.target e = Sum.inl (G.station e) ∧
      G.normalized.source e = Sum.inr (G.junction e) := by
  rcases e with (i | e) | (j | e)
  · exact .inl ⟨rfl, rfl⟩
  · exact .inl ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩
  · exact .inr ⟨rfl, rfl⟩

theorem normalized_loopless (e : G.End) : G.normalized.source e ≠ G.normalized.target e := by
  rcases G.bipartite e with ⟨h, g⟩ | ⟨g, h⟩ <;> rw [h, g] <;> simp

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

section
/-! # The degree of an original station in the subdivided network -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagram

variable {F : Type} {a b : Wire} (G : Diagram F a b)

abbrev Port (v : G.V) := slots (G.table v).1 ⊕ slots (G.table v).2.1

def portEquiv : (Σ v, G.Port v) ≃ G.End :=
  (Equiv.sigmaSumDistrib _ _).trans (G.src.sumCongr G.dst)

theorem station_port (p : Σ v, G.Port v) : G.station (G.portEquiv p) = p.1 := by
  rcases p with ⟨v, i|j⟩
  · exact congrArg Sigma.fst (G.src.symm_apply_apply ⟨v, i⟩)
  · exact congrArg Sigma.fst (G.dst.symm_apply_apply ⟨v, j⟩)

private def atStation (v : G.V) : G.Port v ≃ {p : Σ x, G.Port x // p.1 = v} where
  toFun i := ⟨⟨v, i⟩, rfl⟩
  invFun p := p.2 ▸ p.1.2
  left_inv _ := rfl
  right_inv := by rintro ⟨⟨x, i⟩, rfl⟩; rfl

def incident (v : G.V) : G.Port v ≃ {e : G.End // G.station e = v} :=
  (G.atStation v).trans (G.portEquiv.subtypeEquiv (fun p => by rw [station_port]))

theorem degree [DecidableEq G.V] (v : G.V) :
    Fintype.card {e : G.End // G.station e = v} = G.arity v := by
  rw [← Fintype.card_congr (G.incident v)]
  simp only [Port, Fintype.card_sum, card_slots, arity]

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

/-!
# Networks with unoriented local functions

Use one owner per port rather than specifying a local port order. Evaluating
a station only needs the values on its own ports. Choosing an enumeration
converts such a description into a diagram with the same edges and weights.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagram
open Classical

variable {V E I F : Type} [Fintype V] [Fintype E] {a b : Wire}

private abbrev bundle [Fintype I] (f : I → V) (v : V) :=
  word (Fintype.card {i // f i = v})

private def port [Fintype I] (f : I → V) (v : V) :
    slots (bundle f v) ≃ {i // f i = v} :=
  Fintype.equivOfCardEq (by rw [card_slots, wd_word])

private def connect [Fintype I] (f : I → V) : (Σ v, slots (bundle f v)) ≃ I :=
  (Equiv.sigmaCongrRight (port f)).trans (Equiv.sigmaFiberEquiv f)

private def fill [Fintype I] (f : I → V) (v : V) (x : Val (bundle f v)) (i : I) :=
  if h : f i = v then bits (bundle f v) x ((port f v).symm ⟨i, h⟩) else false

omit [Fintype V] in
private theorem fill_read [Fintype I] (f : I → V) (v : V) (x : I → Bool)
    (i : I) (hi : f i = v) :
    fill f v ((bits (bundle f v)).symm (fun j => x (connect f ⟨v, j⟩))) i = x i := by
  rw [fill, dite_eq_left hi, Equiv.apply_symm_apply]
  change x ((port f v) ((port f v).symm ⟨i, hi⟩)).val = _
  rw [Equiv.apply_symm_apply]

variable (src : slots a ⊕ E → V) (dst : slots b ⊕ E → V)
variable (k : V → (slots a ⊕ E → Bool) → (slots b ⊕ E → Bool) → F)

def Local : Prop :=
  ∀ v x y x' y', (∀ i, src i = v → x i = x' i) → (∀ i, dst i = v → y i = y' i) →
    k v x y = k v x' y'

abbrev ofLocal : Diagram F a b where
  V := V
  E := E
  table v := ⟨bundle src v, bundle dst v, fun x y => k v (fill src v x) (fill dst v y)⟩
  src := connect src
  dst := connect dst

theorem arity_ofLocal (v : V) :
    (ofLocal src dst k).arity v =
      Fintype.card {i // src i = v} + Fintype.card {i // dst i = v} := by
  simp only [arity, wd_word]

theorem source_ofLocal (e : E) : (ofLocal src dst k).source e = src (.inr e) := rfl

theorem target_ofLocal (e : E) : (ofLocal src dst k).target e = dst (.inr e) := rfl

theorem vertex_ofLocal (hk : Local src dst k)
    (x : Val a) (y : Val b) (z : E → Bool) (v : V) :
    (ofLocal src dst k).vertex x y z v =
      k v (Sum.elim (bits a x) z) (Sum.elim (bits b y) z) :=
  hk _ _ _ _ _ (fill_read src _ _) (fill_read dst _ _)

variable (G : Diagram F a b)

/-- Allow the two ends of an edge to carry different values until contraction. -/
def weight (v : G.V) (x : slots a ⊕ G.E → Bool) (y : slots b ⊕ G.E → Bool) : F :=
  (G.table v).2.2
    ((bits (G.table v).1).symm (fun i => x (G.src ⟨v, i⟩)))
    ((bits (G.table v).2.1).symm (fun j => y (G.dst ⟨v, j⟩)))

theorem local_weight :
    Local (fun i => (G.src.symm i).1) (fun j => (G.dst.symm j).1) G.weight := by
  intro v x y x' y' hx hy
  unfold weight
  apply congrArg₂ (G.table v).2.2 <;> apply congrArg
  · funext i; exact hx _ (by simp)
  · funext i; exact hy _ (by simp)

/-- Local weights are independent of the chosen enumeration of ports. -/
theorem weight_ofLocal (hk : Local src dst k) (v : V) (x : slots a ⊕ E → Bool)
    (y : slots b ⊕ E → Bool) : (ofLocal src dst k).weight v x y = k v x y :=
  hk _ _ _ _ _ (fill_read src _ _) (fill_read dst _ _)

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

/-!
# Contracting clusters

Split the old edges into the visible edges and a disjoint family of
edges internal to the clusters. Sum the latter inside each new table.
This identity allows loops, empty clusters and scalar vertices.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagram
open Classical

variable {F : Type} {a b : Wire} (G : Diagram F a b) (V E : Type)

structure Clustering where
  owner : G.V → V
  hidden : V → Type
  [finite : ∀ v, Fintype (hidden v)]
  edges : E ⊕ (Σ v, hidden v) ≃ G.E
  src_hidden : ∀ v e, owner (G.source (edges (.inr ⟨v, e⟩))) = v
  dst_hidden : ∀ v e, owner (G.target (edges (.inr ⟨v, e⟩))) = v

attribute [instance] Clustering.finite

namespace Clustering

variable {G V E} (C : Clustering G V E)

def src (i : slots a ⊕ E) : V :=
  C.owner (G.src.symm (i.map id (fun e => C.edges (.inl e)))).1

def dst (i : slots b ⊕ E) : V :=
  C.owner (G.dst.symm (i.map id (fun e => C.edges (.inl e)))).1

abbrev Inside := ∀ v, C.hidden v → Bool

private def assignments : (E → Bool) × C.Inside ≃ (G.E → Bool) :=
  ((Equiv.refl _).prodCongr (Equiv.piCurry (fun v (_ : C.hidden v) => Bool)).symm).trans
    ((Equiv.sumArrowEquivProdArrow _ _ _).symm.trans (C.edges.arrowCongr (Equiv.refl _)))

def lift {X : Type} (x : X ⊕ E → Bool) (w : C.Inside) : X ⊕ G.E → Bool :=
  Sum.elim (x ∘ Sum.inl) (C.assignments (x ∘ Sum.inr, w))

private theorem lift_local {X : Type} (o : X ⊕ G.E → V)
    (ho : ∀ v e, o (.inr (C.edges (.inr ⟨v, e⟩))) = v)
    {v : V} {x x' : X ⊕ E → Bool} {w w' : C.Inside}
    (hx : ∀ i, o (i.map id (fun e => C.edges (.inl e))) = v → x i = x' i)
    (hw : w v = w' v) (i : X ⊕ G.E) (hi : o i = v) : C.lift x w i = C.lift x' w' i := by
  rcases i with i|e
  · exact hx (.inl i) hi
  obtain ⟨j, rfl⟩ := C.edges.surjective e
  change Sum.elim (x ∘ Sum.inr) _ (C.edges.symm (C.edges j)) =
    Sum.elim (x' ∘ Sum.inr) _ (C.edges.symm (C.edges j))
  rw [Equiv.symm_apply_apply]
  rcases j with j|⟨u, t⟩
  · exact hx (.inr j) hi
  · rw [ho] at hi
    subst u
    exact congrFun hw t

variable [Field F]

private def term (v : V) (x : slots a ⊕ E → Bool) (y : slots b ⊕ E → Bool)
    (w : C.Inside) : F :=
  ∏ t : {t // C.owner t = v}, G.weight t (C.lift x w) (C.lift y w)

private theorem term_local {v : V} {x x' y y'} {w w' : C.Inside}
    (hx : ∀ i, C.src i = v → x i = x' i) (hy : ∀ i, C.dst i = v → y i = y' i)
    (hw : w v = w' v) : C.term v x y w = C.term v x' y' w' := by
  apply Finset.prod_congr rfl
  intro t _
  apply G.local_weight
  · intro i hi
    exact C.lift_local (fun i => C.owner (G.src.symm i).1) C.src_hidden hx hw i
      ((congrArg C.owner hi).trans t.property)
  · intro i hi
    exact C.lift_local (fun i => C.owner (G.dst.symm i).1) C.dst_hidden hy hw i
      ((congrArg C.owner hi).trans t.property)

private def total (v : V) (x : slots a ⊕ E → Bool) (y : slots b ⊕ E → Bool) : F :=
  ∑ w : C.hidden v → Bool, C.term v x y (Function.update (fun _ _ => false) v w)

private theorem total_local : Local C.src C.dst C.total := by
  intro v x y x' y' hx hy
  exact Finset.sum_congr rfl fun _ _ => C.term_local hx hy rfl

variable [Fintype V] [Fintype E]

abbrev collapse : Diagram F a b := ofLocal C.src C.dst C.total

/-- The local kernel at one cluster uses only its own hidden bits.
It can be read in any port order. -/
theorem weight_collapse (v : V) (x : slots a ⊕ E → Bool) (y : slots b ⊕ E → Bool) :
    C.collapse.weight v x y =
      ∑ z : C.hidden v → Bool, ∏ t : {t // C.owner t = v},
        G.weight t (C.lift x (Function.update (fun _ _ => false) v z))
          (C.lift y (Function.update (fun _ _ => false) v z)) :=
  weight_ofLocal _ _ _ C.total_local _ _ _

theorem eval_collapse : C.collapse.eval = G.eval := by
  funext x y
  have prod_eq (z : E → Bool) :
      (∏ v, C.collapse.vertex x y z v) =
        ∑ w : C.Inside, ∏ v, G.vertex x y (C.assignments (z, w)) v := by
    simp only [collapse, vertex_ofLocal _ _ _ C.total_local, total, Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro w _
    rw [← Fintype.prod_fiberwise C.owner]
    apply Finset.prod_congr rfl
    intro v _
    change C.term v _ _ _ = C.term v (Sum.elim (bits a x) z) (Sum.elim (bits b y) z) w
    exact C.term_local (fun _ _ => rfl) (fun _ _ => rfl) (Function.update_self _ _ _)
  unfold eval
  simp_rw [prod_eq]
  rw [← Equiv.sum_comp C.assignments, Fintype.sum_prod_type]

end Clustering

variable {V} (o : G.V → V)

/-- Keep only wires that cross the partition. -/
abbrev Between := {e : G.E // o (G.source e) ≠ o (G.target e)}

def partition : Clustering G V (G.Between o) where
  owner := o
  hidden v := {e : {e : G.E // o (G.source e) = o (G.target e)} // o (G.source e) = v}
  edges :=
    ((Equiv.refl _).sumCongr (Equiv.sigmaFiberEquiv _)).trans
      ((Equiv.sumComm _ _).trans (Equiv.sumCompl (fun e => o (G.source e) = o (G.target e))))
  src_hidden _ e := e.property
  dst_hidden _ e := e.val.property.symm.trans e.property

variable [Field F] [Fintype V]

abbrev coarsen := (G.partition o).collapse

theorem eval_coarsen : (G.coarsen o).eval = G.eval := (G.partition o).eval_collapse

theorem source_coarsen (e : G.Between o) : (G.coarsen o).source e = o (G.source e) := rfl

theorem target_coarsen (e : G.Between o) : (G.coarsen o).target e = o (G.target e) := rfl

theorem cost_coarsen : (G.coarsen o).cost =
    Fintype.card V + wd a + wd b + 2 * Fintype.card (G.Between o) :=
  (G.coarsen o).cost_eq

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

/-!
# Expanding a network by a simultaneous wire identity

Cut each edge into two half-edges. Insert the two copies of its bit
into the demand ports of the packet. The new sites and the old stations
are disjoint, even when several demands have a common endpoint.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagram
open Classical

variable {F : Type} [Field F] {a b : Wire} (G : Diagram F a b)
variable {S I : Type} {J : I → Type} [Fintype S] [Fintype I] [∀ i, Fintype (J i)]
variable {D : G.E → S × S} {W : (i : I) → J i → S × S}

namespace Expansion

abbrev Edge (T : Type) := G.E ⊕ G.E ⊕ T

def src {T : Type} (D : G.E → S × S) (w : T → S × S) : slots a ⊕ Edge G T → G.V ⊕ S
  | .inl i => .inl (G.src.symm (.inl i)).1
  | .inr (.inl e) => .inl (G.source e)
  | .inr (.inr (.inl e)) => .inr (D e).2
  | .inr (.inr (.inr j)) => .inr (w j).1

def dst {T : Type} (D : G.E → S × S) (w : T → S × S) : slots b ⊕ Edge G T → G.V ⊕ S
  | .inl i => .inl (G.dst.symm (.inl i)).1
  | .inr (.inl e) => .inr (D e).1
  | .inr (.inr (.inl e)) => .inl (G.target e)
  | .inr (.inr (.inr j)) => .inr (w j).2

def entry (P : Spectral.Packet.Rule F D W) (i : I) (v : G.V ⊕ S)
    (x : slots a ⊕ Edge G (J i) → Bool) (y : slots b ⊕ Edge G (J i) → Bool) : F :=
  match v with
  | .inl t => G.weight t (Sum.elim (x ∘ Sum.inl) (fun e => x (.inr (.inl e))))
      (Sum.elim (y ∘ Sum.inl) (fun e => y (.inr (.inr (.inl e)))))
  | .inr s => P.entry i s (fun e => y (.inr (.inl e))) (fun e => x (.inr (.inr (.inl e))))
      (fun j => if (W i j).1 = s then x (.inr (.inr (.inr j))) else y (.inr (.inr (.inr j))))

theorem entry_local (P : Spectral.Packet.Rule F D W) (i : I) :
    Local (src G D (W i)) (dst G D (W i)) (entry G P i) := by
  rintro (v|s) x y x' y' hx hy
  · apply G.local_weight
    · rintro (t|e) he
      · exact hx (.inl t) (congrArg Sum.inl he)
      · exact hx (.inr (.inl e)) (congrArg Sum.inl he)
    · rintro (t|e) he
      · exact hy (.inl t) (congrArg Sum.inl he)
      · exact hy (.inr (.inr (.inl e))) (congrArg Sum.inl he)
  · apply P.local'
    · exact fun e he => hy (.inr (.inl e)) (congrArg Sum.inr he)
    · exact fun e he => hx (.inr (.inr (.inl e))) (congrArg Sum.inr he)
    · intro j hj
      by_cases h : (W i j).1 = s
      · simpa only [ite_eq_left h] using hx (.inr (.inr (.inr j))) (congrArg Sum.inr h)
      · simpa only [ite_eq_right h] using hy (.inr (.inr (.inr j))) (congrArg Sum.inr (hj.resolve_left h))

end Expansion

abbrev expanded (P : Spectral.Packet.Rule F D W) (i : I) :=
  ofLocal (Expansion.src G D (W i)) (Expansion.dst G D (W i)) (Expansion.entry G P i)


theorem weight_expanded (P : Spectral.Packet.Rule F D W) (i : I) (v : G.V ⊕ S)
    (x : slots a ⊕ Expansion.Edge G (J i) → Bool)
    (y : slots b ⊕ Expansion.Edge G (J i) → Bool) :
    (G.expanded P i).weight v x y = Expansion.entry G P i v x y :=
  weight_ofLocal _ _ _ (Expansion.entry_local G P i) v x y

private theorem eval_split {U V T : Type} [Fintype U] [Fintype V] [Fintype T]
    (g : G.E ≃ U ⊕ V ⊕ T) (x : Val a) (y : Val b) :
    G.eval x y = ∑ l : U → Bool, ∑ r : V → Bool, ∑ z : T → Bool,
      ∏ v, G.vertex x y (Sum.elim l (Sum.elim r z) ∘ g) v := by
  let e : (G.E → Bool) ≃ (U → Bool) × (V → Bool) × (T → Bool) :=
    ((g.arrowCongr (Equiv.refl Bool)).trans (Equiv.sumArrowEquivProdArrow _ _ _)).trans
      ((Equiv.refl _).prodCongr (Equiv.sumArrowEquivProdArrow _ _ _))
  unfold eval
  rw [← Equiv.sum_comp e.symm]
  simp only [Fintype.sum_prod_type]
  rfl

theorem eval_expanded (P : Spectral.Packet.Rule F D W) (x : Val a) (y : Val b) :
    ∑ i, (G.expanded P i).eval x y = G.eval x y := by
  let H (l r : G.E → Bool) := ∏ v, G.weight v (Sum.elim (bits a x) l) (Sum.elim (bits b y) r)
  have each (i : I) : (G.expanded P i).eval x y =
      ∑ l, ∑ r, H l r * ∑ z, ∏ s, P.entry i s l r z := by
    rw [eval_split (G.expanded P i) (U := G.E) (V := G.E) (T := J i) (Equiv.refl _)]
    simp_rw [expanded, vertex_ofLocal _ _ _ (Expansion.entry_local G P i)]
    refine Finset.sum_congr rfl fun l _ => ?_
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun z _ => ?_
    rw [Fintype.prod_sum_type]
    simp only [Expansion.entry, Function.comp_apply, Equiv.refl_apply, Sum.elim_inl, Sum.elim_inr, ite_self]
    rfl
  simp_rw [each]
  rw [Finset.sum_comm]
  unfold eval
  apply Finset.sum_congr rfl
  intro l _
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum, ← P.eval]
  simp only [mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

/-!
# Contracting a summand of the simultaneous wire identity

The partition may depend on the selector. When each cut end meets its
assigned packet site, the surviving graph has just the crossing supplies.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Diagram
open Classical

variable {F : Type} [Field F] {a b : Wire} (G : Diagram F a b)
variable {S I : Type} {J : I → Type} [Fintype S] [Fintype I] [∀ i, Fintype (J i)]
variable {D : G.E → S × S} {W : (i : I) → J i → S × S} (P : Spectral.Packet.Rule F D W)
variable {V : Type} [Fintype V] (o : I → G.V → V) (q : I → S → V)

abbrev replaced (i : I) := (G.expanded P i).coarsen (Sum.elim (o i) (q i))

theorem eval_replaced (x : Val a) (y : Val b) :
    ∑ i, (G.replaced P o q i).eval x y = G.eval x y := by
  simp only [replaced, eval_coarsen, eval_expanded]

def Aligned (D : G.E → S × S) : Prop :=
  ∀ i e, o i (G.source e) = q i (D e).1 ∧ o i (G.target e) = q i (D e).2

abbrev Cut (i : I) := {e : J i // q i (W i e).1 ≠ q i (W i e).2}

def cutEdges (h : G.Aligned o q D) (i : I) :
    Cut (W := W) q i ≃ (G.replaced P o q i).E := by
  let f : Cut (W := W) q i → (G.replaced P o q i).E :=
    fun e => ⟨.inr (.inr e.val), e.property⟩
  refine Equiv.ofBijective f ⟨?_, ?_⟩
  · intro e t he
    exact Subtype.ext (Sum.inr.inj (Sum.inr.inj (congrArg Subtype.val he)))
  · rintro ⟨e | e | j, he⟩
    · exact (he (h i e).1).elim
    · exact (he (h i e).2.symm).elim
    · exact ⟨⟨j, he⟩, rfl⟩

theorem source_cut (h : G.Aligned o q D) (i : I) (e : Cut (W := W) q i) :
    (G.replaced P o q i).source (G.cutEdges P o q h i e) = q i (W i e).1 := rfl

theorem target_cut (h : G.Aligned o q D) (i : I) (e : Cut (W := W) q i) :
    (G.replaced P o q i).target (G.cutEdges P o q h i e) = q i (W i e).2 := rfl

theorem cost_replaced (h : G.Aligned o q D) (i : I) :
    (G.replaced P o q i).cost =
      Fintype.card V + wd a + wd b + 2 * Fintype.card (Cut (W := W) q i) := by
  rw [cost_eq, Fintype.card_congr (G.cutEdges P o q h i)]

theorem source_exterior (i : I) (t : slots a) :
    ((G.replaced P o q i).src.symm (.inl t)).1 = o i (G.src.symm (.inl t)).1 := rfl

theorem target_exterior (i : I) (t : slots b) :
    ((G.replaced P o q i).dst.symm (.inl t)).1 = o i (G.dst.symm (.inl t)).1 := rfl

omit [Fintype V] in
private theorem ends_le {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (u : X ⊕ Y → V) (f : X → V) (g : Z → V) (m : Y ↪ Z)
    (he : ∀ x, u (.inl x) = f x) (hi : ∀ y, u (.inr y) = g (m y)) (v : V) :
    Fintype.card {t // u t = v} ≤ Fintype.card {t // f t = v} + Fintype.card {t // g t = v} := by
  let p : {t // u t = v} → {t // f t = v} ⊕ {t // g t = v}
    | ⟨.inl x, h⟩ => .inl ⟨x, (he x).symm.trans h⟩
    | ⟨.inr y, h⟩ => .inr ⟨m y, (hi y).symm.trans h⟩
  rw [← Fintype.card_sum]
  apply Fintype.card_le_of_injective p
  rintro ⟨x|y, h⟩ ⟨x'|y', h'⟩ eq
  · exact Subtype.ext (congrArg Sum.inl (congrArg Subtype.val (Sum.inl.inj eq)))
  · cases eq
  · cases eq
  · exact Subtype.ext (congrArg Sum.inr (m.injective (congrArg Subtype.val (Sum.inr.inj eq))))

/-- Including all local supplies only increases the bound on a cluster's arity. -/
theorem arity_replaced (h : G.Aligned o q D) (i : I) (v : V) :
    (G.replaced P o q i).arity v ≤
      (Fintype.card {t : slots a // o i (G.src.symm (.inl t)).1 = v} +
       Fintype.card {t : slots b // o i (G.dst.symm (.inl t)).1 = v}) +
      (Fintype.card {e : J i // q i (W i e).1 = v} +
       Fintype.card {e : J i // q i (W i e).2 = v}) := by
  let c := (G.expanded P i).partition (Sum.elim (o i) (q i))
  let inj := (G.cutEdges P o q h i).symm.toEmbedding.trans
    (Function.Embedding.subtype (fun j : J i => q i (W i j).1 ≠ q i (W i j).2))
  have h₁ := ends_le c.src (fun t => o i (G.src.symm (.inl t)).1) (fun e => q i (W i e).1) inj
    (fun _ => rfl) (fun e => by
      obtain ⟨t, rfl⟩ := (G.cutEdges P o q h i).surjective e
      simp only [inj, Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.symm_apply_apply,
        Function.Embedding.subtype_apply]
      rfl) v
  have h₂ := ends_le c.dst (fun t => o i (G.dst.symm (.inl t)).1) (fun e => q i (W i e).2) inj
    (fun _ => rfl) (fun e => by
      obtain ⟨t, rfl⟩ := (G.cutEdges P o q h i).surjective e
      simp only [inj, Function.Embedding.trans_apply, Equiv.toEmbedding_apply, Equiv.symm_apply_apply,
        Function.Embedding.subtype_apply]
      rfl) v
  change (ofLocal c.src c.dst _).arity v ≤ _
  rw [arity_ofLocal]
  exact (Nat.add_le_add h₁ h₂).trans_eq (add_add_add_comm _ _ _ _)

end OAI.LinearAlgebra.MatrixExponent.Diagram
end
