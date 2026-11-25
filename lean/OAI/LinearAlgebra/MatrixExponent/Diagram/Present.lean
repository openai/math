import OAI.LinearAlgebra.MatrixExponent.Diagram.Basic
import OAI.LinearAlgebra.MatrixExponent.CompareExchange

section
/-!
# Realizing a directed multigraph by structural network operations

Juxtapose the tables, keeping track of where each argument slot went.
Reorder the slots to expose the exterior bits and a copy of the internal
edge bundle on each side. One trace now sums over all edge assignments.
-/

namespace OAI.LinearAlgebra.MatrixExponent.Diagram

variable {V : Type} (T : V → Wire)

/-- A bundle containing exactly the argument positions indexed by `s`. -/
private structure Bundle (s : Finset V) where
  wire : Wire
  slot : slots wire → Σ v, slots (T v)
  inj : Function.Injective slot
  image : ∀ i, (∃ j, slot j = i) ↔ i.1 ∈ s

namespace Bundle

private def empty : Bundle T ∅ where
  wire := .unit
  slot := Empty.elim
  inj i := i.elim
  image i := by simp

variable {T} {s : Finset V}

private def cons [DecidableEq V] (v : V) (hv : v ∉ s) (b : Bundle T s) :
    Bundle T (insert v s) where
  wire := .pair (T v) b.wire
  slot := Sum.elim (fun i => ⟨v, i⟩) b.slot
  inj := by
    have h (i) : (b.slot i).1 ≠ v := fun e => hv (e ▸ (b.image _).mp ⟨i, rfl⟩)
    rintro (i | i) (j | j) he
    · cases he; rfl
    · exact (h j (congrArg Sigma.fst he.symm)).elim
    · exact (h i (congrArg Sigma.fst he)).elim
    · exact congrArg Sum.inr (b.inj he)
  image := by
    rintro ⟨w, i⟩
    rw [Finset.mem_insert, ← b.image]
    constructor
    · rintro ⟨j | j, he⟩
      · exact .inl (congrArg Sigma.fst he.symm)
      · exact .inr ⟨j, he⟩
    · rintro (rfl | ⟨j, he⟩)
      · exact ⟨.inl i, rfl⟩
      · exact ⟨.inr j, he⟩

private def read (b : Bundle T s) (x : (Σ v, slots (T v)) → Bool) : Val b.wire :=
  (bits b.wire).symm (x ∘ b.slot)

private noncomputable def equiv [Fintype V] (b : Bundle T Finset.univ) :
    slots b.wire ≃ Σ v, slots (T v) :=
  Equiv.ofBijective b.slot ⟨b.inj, fun i => (b.image i).mpr (Finset.mem_univ _)⟩

end Bundle

variable {F : Type} [Field F] {a b : Wire}

theorem realize
    (N : (a b : Wire) → (Val a → Val b → F) → ℕ → Prop)
    (empty : N .unit .unit (fun _ _ => 1) 0)
    (par : ∀ {a b c d k l m n}, N a b k m → N c d l n →
      N (.pair a c) (.pair b d) (fun x y => k x.1 y.1 * l x.2 y.2) (m + n))
    (pre : ∀ {a b c f k m}, N b c k m → Rewire a b f → N a c (fun x y => k (f x) y) m)
    (post : ∀ {a b c f k m}, N a b k m → Rewire c b f → N a c (fun x y => k x (f y)) m)
    (trace : ∀ {a b c k m}, N (.pair a c) (.pair b c) k m →
      N a b (fun x y => ∑ z : Val c, k (x, z) (y, z)) m)
    (G : Diagram F a b) (m : G.V → ℕ)
    (ht : ∀ v, N (G.table v).1 (G.table v).2.1 (G.table v).2.2 (m v)) :
    N a b G.eval (∑ v, m v) := by
  classical
  let A v := (G.table v).1
  let B v := (G.table v).2.1
  have collect (s : Finset G.V) :
      ∃ (u : Bundle A s) (v : Bundle B s) (k : Val u.wire → Val v.wire → F),
        N u.wire v.wire k (∑ i ∈ s, m i) ∧
        ∀ x y z, k (u.read (Sum.elim (bits a x) z ∘ G.src))
          (v.read (Sum.elim (bits b y) z ∘ G.dst)) = ∏ i ∈ s, G.vertex x y z i := by
    induction s using Finset.induction_on with
    | empty => exact ⟨.empty A, .empty B, _, empty, by simp⟩
    | @insert i s hi ih =>
      obtain ⟨u, v, k, hk, he⟩ := ih
      rw [Finset.sum_insert hi]
      refine ⟨u.cons i hi, v.cons i hi, _, par (ht i) hk, ?_⟩
      intro x y z
      rw [Finset.prod_insert hi, ← he]
      rfl
  obtain ⟨u, v, k, hk, he⟩ := collect Finset.univ
  obtain ⟨c, hc⟩ : ∃ c, wd c = Fintype.card G.E := ⟨_, wd_word _⟩
  let e : G.E ≃ slots c := Fintype.equivOfCardEq ((card_slots c).trans hc).symm
  let h := (bits c).trans (e.symm.arrowCongr (Equiv.refl Bool))
  let index {T : G.V → Wire} {d : Wire} (w : Bundle T Finset.univ)
      (t : (Σ v, slots (T v)) ≃ slots d ⊕ G.E) : slots w.wire ≃ slots (.pair d c) :=
    (w.equiv.trans t).trans ((Equiv.refl _).sumCongr e)
  have read {T : G.V → Wire} {d : Wire} (w : Bundle T Finset.univ)
      (t : (Σ v, slots (T v)) ≃ slots d ⊕ G.E) (x : Val d) (z : Val c) :
      reindex (index w t) (x, z) = w.read (Sum.elim (bits d x) (h z) ∘ t) := by
    unfold reindex Bundle.read
    congr 1
    funext i
    change Sum.elim (bits d x) (bits c z) ((Sum.map id e) (t (w.slot i))) =
      Sum.elim (bits d x) (h z) (t (w.slot i))
    cases t (w.slot i) <;> rfl
  have eqn : G.eval = fun x y => ∑ z : Val c,
      k (reindex (index u G.src) (x, z)) (reindex (index v G.dst) (y, z)) := by
    funext x y
    simp_rw [read, he]
    exact (Equiv.sum_comp h _).symm
  rw [eqn]
  exact trace (post (pre hk (rewire_reindex (index u G.src))) (rewire_reindex (index v G.dst)))

theorem net (G : Diagram F a b) (h : G.Trivalent) :
    Net F a b G.eval (Fintype.card G.V) := by
  simpa using realize (Net F) Net.empty Net.par Net.pre Net.post Net.trace G
    (fun _ => 1) (fun i => Net.table _ _ _ (h i))

theorem wide (G : Diagram F a b) {u : ℕ} {L : Set (Table F)} (h : G.Admits u L) :
    Wide F u L a b G.eval G.cost :=
  realize (Wide F u L) Wide.empty Wide.par Wide.pre Wide.post Wide.trace G
    (fun i => 1 + G.arity i) (fun i => Wide.table _ _ _ (h i).1 (h i).2)

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

section
/-! # Disjoint unions of networks -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagram

variable {F : Type} {a b c d : Wire} (G : Diagram F a b) (H : Diagram F c d)

abbrev par : Diagram F (.pair a c) (.pair b d) where
  V := G.V ⊕ H.V
  E := G.E ⊕ H.E
  table := Sum.elim G.table H.table
  src := (Equiv.sumSigmaDistrib _).trans ((G.src.sumCongr H.src).trans (Equiv.sumSumSumComm _ _ _ _))
  dst := (Equiv.sumSigmaDistrib _).trans ((G.dst.sumCongr H.dst).trans (Equiv.sumSumSumComm _ _ _ _))

theorem cost_par : (G.par H).cost = G.cost + H.cost :=
  Fintype.sum_sum_type _

theorem card_par : Fintype.card (G.par H).V = Fintype.card G.V + Fintype.card H.V :=
  Fintype.card_sum

theorem admits_par {u : ℕ} {L : Set (Table F)} (hg : G.Admits u L) (hh : H.Admits u L) :
    (G.par H).Admits u L := by
  rintro (i | i)
  · exact hg i
  · exact hh i

theorem trivalent_par (hg : G.Trivalent) (hh : H.Trivalent) : (G.par H).Trivalent := by
  rintro (i | i)
  · exact hg i
  · exact hh i

private theorem value_left {A B : Wire} {X Y : Type} (x : Val (.pair A B))
    (s : X → Bool) (t : Y → Bool) (i : slots A ⊕ X) :
    Sum.elim (bits (.pair A B) x) (Sum.elim s t)
      (Equiv.sumSumSumComm (slots A) X (slots B) Y (.inl i)) = Sum.elim (bits A x.1) s i := by
  cases i <;> rfl

private theorem value_right {A B : Wire} {X Y : Type} (x : Val (.pair A B))
    (s : X → Bool) (t : Y → Bool) (i : slots B ⊕ Y) :
    Sum.elim (bits (.pair A B) x) (Sum.elim s t)
      (Equiv.sumSumSumComm (slots A) X (slots B) Y (.inr i)) = Sum.elim (bits B x.2) t i := by
  cases i <;> rfl

theorem vertex_left (x : Val (.pair a c)) (y : Val (.pair b d))
    (s : G.E → Bool) (t : H.E → Bool) (v : G.V) :
    (G.par H).vertex x y (Sum.elim s t) (.inl v) = G.vertex x.1 y.1 s v := by
  unfold vertex
  apply congrArg₂ (G.table v).2.2
  · exact congrArg (bits (G.table v).1).symm (funext fun i => value_left x s t (G.src ⟨v, i⟩))
  · exact congrArg (bits (G.table v).2.1).symm (funext fun i => value_left y s t (G.dst ⟨v, i⟩))

theorem vertex_right (x : Val (.pair a c)) (y : Val (.pair b d))
    (s : G.E → Bool) (t : H.E → Bool) (v : H.V) :
    (G.par H).vertex x y (Sum.elim s t) (.inr v) = H.vertex x.2 y.2 t v := by
  unfold vertex
  apply congrArg₂ (H.table v).2.2
  · exact congrArg (bits (H.table v).1).symm (funext fun i => value_right x s t (H.src ⟨v, i⟩))
  · exact congrArg (bits (H.table v).2.1).symm (funext fun i => value_right y s t (H.dst ⟨v, i⟩))

theorem eval_par [Field F] (x : Val (.pair a c)) (y : Val (.pair b d)) :
    (G.par H).eval x y = G.eval x.1 y.1 * H.eval x.2 y.2 := by
  classical
  unfold eval
  let _ : DecidableEq (G.E ⊕ H.E) := fun _ _ => Classical.propDecidable _
  let e := (Equiv.sumPiEquivProdPi (fun _ : G.E ⊕ H.E => Bool)).symm
  rw [← e.sum_comp, Fintype.sum_prod_type, Finset.sum_mul_sum]
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.sum_congr rfl
  intro t _
  change (∏ v, (G.par H).vertex x y (Sum.elim s t) v) = _
  rw [Fintype.prod_sum_type]
  exact congrArg₂ (· * ·)
    (Finset.prod_congr rfl (fun v _ => vertex_left G H x y s t v))
    (Finset.prod_congr rfl (fun v _ => vertex_right G H x y s t v))

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

section
/-! # Closing and permuting exterior slots -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagram

variable {F : Type} {a b c d : Wire}

abbrev close (G : Diagram F (.pair a c) (.pair b c)) : Diagram F a b where
  V := G.V
  E := slots c ⊕ G.E
  table := G.table
  src := G.src.trans (Equiv.sumAssoc _ _ _)
  dst := G.dst.trans (Equiv.sumAssoc _ _ _)

private theorem value_close {E : Type} (x : Val a) (z : Val c)
    (s : E → Bool) (i : (slots a ⊕ slots c) ⊕ E) :
    Sum.elim (bits a x) (Sum.elim (bits c z) s) (Equiv.sumAssoc _ _ _ i) =
      Sum.elim (bits (.pair a c) (x, z)) s i := by
  rcases i with (i | i) | i <;> rfl

theorem vertex_close (G : Diagram F (.pair a c) (.pair b c))
    (x : Val a) (y : Val b) (z : Val c) (s : G.E → Bool) (v : G.V) :
    G.close.vertex x y (Sum.elim (bits c z) s) v = G.vertex (x, z) (y, z) s v := by
  unfold vertex
  apply congrArg₂ (G.table v).2.2
  · exact congrArg (bits (G.table v).1).symm (funext fun i => value_close x z s (G.src ⟨v, i⟩))
  · exact congrArg (bits (G.table v).2.1).symm (funext fun i => value_close y z s (G.dst ⟨v, i⟩))

theorem eval_close [Field F] (G : Diagram F (.pair a c) (.pair b c)) (x : Val a) (y : Val b) :
    G.close.eval x y = ∑ z : Val c, G.eval (x, z) (y, z) := by
  classical
  unfold eval
  let _ : DecidableEq (slots c ⊕ G.E) := fun _ _ => Classical.propDecidable _
  let e := ((bits c).prodCongr (Equiv.refl (G.E → Bool))).trans
    (Equiv.sumPiEquivProdPi (fun _ : slots c ⊕ G.E => Bool)).symm
  rw [← e.sum_comp, Fintype.sum_prod_type]
  apply Finset.sum_congr rfl
  intro z _
  apply Finset.sum_congr rfl
  intro s _
  exact Finset.prod_congr rfl (fun v _ => vertex_close G x y z s v)

abbrev rename (G : Diagram F a b) (f : slots a ≃ slots c) (g : slots b ≃ slots d) :
    Diagram F c d where
  V := G.V
  E := G.E
  table := G.table
  src := G.src.trans (f.sumCongr (.refl _))
  dst := G.dst.trans (g.sumCongr (.refl _))

private theorem value_rename {E : Type} (f : slots a ≃ slots c) (x : Val c)
    (s : E → Bool) (i : slots a ⊕ E) :
    Sum.elim (bits c x) s ((f.sumCongr (.refl _)) i) = Sum.elim (bits a (reindex f x)) s i := by
  rcases i with i | i
  · exact (bits_reindex f x i).symm
  · rfl

theorem eval_rename [Field F] (G : Diagram F a b) (f : slots a ≃ slots c) (g : slots b ≃ slots d)
    (x : Val c) (y : Val d) : (G.rename f g).eval x y = G.eval (reindex f x) (reindex g y) := by
  classical
  unfold eval
  apply Finset.sum_congr rfl
  intro s _
  apply Finset.prod_congr rfl
  intro v _
  unfold vertex
  apply congrArg₂ (G.table v).2.2
  · exact congrArg (bits (G.table v).1).symm (funext fun i => value_rename f x s (G.src ⟨v, i⟩))
  · exact congrArg (bits (G.table v).2.1).symm (funext fun i => value_rename g y s (G.dst ⟨v, i⟩))

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

section
/-! # Networks with zero or one station -/

namespace OAI.LinearAlgebra.MatrixExponent.Diagram

variable {F : Type} {a b : Wire}

abbrev empty (F : Type) : Diagram F .unit .unit where
  V := Empty
  E := Empty
  table := Empty.elim
  src := ⟨fun i => i.1.elim, Sum.elim Empty.elim Empty.elim,
    fun i => i.1.elim, fun i => (Sum.elim id id i).elim⟩
  dst := ⟨fun i => i.1.elim, Sum.elim Empty.elim Empty.elim,
    fun i => i.1.elim, fun i => (Sum.elim id id i).elim⟩

theorem eval_empty [Field F] (x y : Val .unit) : (empty F).eval x y = 1 := by
  simp [eval]

private def singlePort (X : Type) : (Σ _ : Unit, X) ≃ X ⊕ Empty :=
  ⟨fun i => .inl i.2, Sum.elim (fun i => ⟨(), i⟩) Empty.elim,
    fun _ => rfl, by rintro (i|i); rfl; exact i.elim⟩

abbrev single (k : Val a → Val b → F) : Diagram F a b where
  V := Unit
  E := Empty
  table _ := ⟨a, b, k⟩
  src := singlePort _
  dst := singlePort _

theorem eval_single [Field F] (k : Val a → Val b → F) (x : Val a) (y : Val b) :
    (single k).eval x y = k x y := by
  unfold eval
  rw [Fintype.sum_unique, Fintype.prod_unique]
  change k ((bits a).symm (bits a x)) ((bits b).symm (bits b y)) = _
  rw [Equiv.symm_apply_apply, Equiv.symm_apply_apply]

end OAI.LinearAlgebra.MatrixExponent.Diagram
end

section
/-! # From compositional networks to indexed wiring diagrams -/

namespace OAI.LinearAlgebra.MatrixExponent

variable {F : Type} [Field F] {a b c d : Wire} {m n : ℕ}

private def Presents (P : Table F → Prop) (price : Table F → ℕ)
    (a b : Wire) (k : Val a → Val b → F) (m : ℕ) : Prop :=
  ∃ G : Diagram F a b, G.eval = k ∧ (∀ v, P (G.table v)) ∧ ∑ v, price (G.table v) = m

namespace Presents

variable {P : Table F → Prop} {price : Table F → ℕ} {k : Val a → Val b → F}

private theorem empty : Presents P price .unit .unit (fun _ _ => 1) 0 :=
  ⟨.empty F, funext fun x => funext (Diagram.eval_empty x), fun v => v.elim, by simp⟩

private theorem table (h : P ⟨a, b, k⟩) : Presents P price a b k (price ⟨a, b, k⟩) :=
  ⟨.single k, funext fun x => funext (Diagram.eval_single k x), fun _ => h, Fintype.sum_unique _⟩

private theorem par {l : Val c → Val d → F}
    (h : Presents P price a b k m) (g : Presents P price c d l n) :
    Presents P price (.pair a c) (.pair b d) (fun x y => k x.1 y.1 * l x.2 y.2) (m + n) := by
  obtain ⟨G, rfl, hk, rfl⟩ := h
  obtain ⟨H, rfl, hl, rfl⟩ := g
  refine ⟨G.par H, funext fun x => funext (Diagram.eval_par G H x), ?_, Fintype.sum_sum_type _⟩
  rintro (v | v)
  · exact hk v
  · exact hl v

private theorem trace {l : Val (.pair a c) → Val (.pair b c) → F}
    (h : Presents P price (.pair a c) (.pair b c) l m) :
    Presents P price a b (fun x y => ∑ z : Val c, l (x, z) (y, z)) m := by
  obtain ⟨G, rfl, hp, hm⟩ := h
  exact ⟨G.close, funext fun x => funext (G.eval_close x), hp, hm⟩

private theorem rename {f : Val c → Val a} {g : Val d → Val b}
    (h : Presents P price a b k m) (hf : Rewire c a f) (hg : Rewire d b g) :
    Presents P price c d (fun x y => k (f x) (g y)) m := by
  obtain ⟨G, rfl, hp, hm⟩ := h
  obtain ⟨f, rfl⟩ := hf.reindex_exists
  obtain ⟨g, rfl⟩ := hg.reindex_exists
  exact ⟨G.rename f g, funext fun x => funext (G.eval_rename f g x), hp, hm⟩

private theorem comp {l : Val b → Val c → F}
    (h : Presents P price a b k m) (g : Presents P price b c l n) :
    Presents P price a c (fun x y => ∑ z : Val b, k x z * l z y) (m + n) :=
  ((h.par g).rename (.id _) (.swap _ _)).trace

end Presents

private def arity (A : Table F) := wd A.1 + wd A.2.1

variable {k : Val a → Val b → F}

theorem Net.diagram (h : Net F a b k m) :
    ∃ G : Diagram F a b, G.eval = k ∧ G.Trivalent ∧ Fintype.card G.V = m := by
  have hp : Presents (fun A => arity A ≤ 3) (fun _ => 1) a b k m := by
    induction h with
    | empty => exact .empty
    | table _ _ _ h => exact .table h
    | par _ _ ih ig => exact ih.par ig
    | comp _ _ ih ig => exact ih.comp ig
    | trace _ ih => exact ih.trace
    | pre _ hr ih => exact ih.rename hr (.id _)
    | post _ hr ih => exact ih.rename (.id _) hr
  obtain ⟨G, hg, ht, hm⟩ := hp
  exact ⟨G, hg, ht, by simpa using hm⟩

theorem Wide.diagram {u : ℕ} {L : Set (Table F)} (h : Wide F u L a b k m) :
    ∃ G : Diagram F a b, G.eval = k ∧ G.Admits u L ∧ G.cost = m := by
  change Presents (fun A => arity A ≤ u ∧ (arity A ≤ 3 ∨ A ∈ L))
    (fun A => 1 + arity A) a b k m
  induction h with
  | empty => exact .empty
  | table _ _ _ ht hl => exact .table ⟨ht, hl⟩
  | par _ _ ih ig => exact ih.par ig
  | comp _ _ ih ig => exact ih.comp ig
  | trace _ ih => exact ih.trace
  | pre _ hr ih => exact ih.rename hr (.id _)
  | post _ hr ih => exact ih.rename (.id _) hr

end OAI.LinearAlgebra.MatrixExponent
end
