import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Prefix
import OAI.LinearAlgebra.MatrixExponent.Packing.TetherHost
import OAI.LinearAlgebra.MatrixExponent.Spectral.Path
import OAI.LinearAlgebra.MatrixExponent.Assembly.Reset.Repost
import OAI.LinearAlgebra.MatrixExponent.Assembly.History.Dense
import OAI.LinearAlgebra.MatrixExponent.Packing.Frame
import OAI.LinearAlgebra.MatrixExponent.BatchDescent.Trail.Hop

section
/-! # The local product at a rotor and its gathering trees -/

namespace OAI.LinearAlgebra.MatrixExponent.Packing.Rotor
open Spectral.Packet

variable {F A : Type} [Field F] [Fintype A] {Y w n : ℕ}
  (R : Rotor F Y w) (p q : A → Fin Y) (σ : Fin n → Equiv.Perm (Fin Y))
  (lane : A → Fin n × Fin w) (inj : Function.Injective (fun a => (p a, lane a)))
  (route : ∀ a, σ (lane a).1 (p a) = q a)

theorem treeRule_entry (b : Bool) (v : R.Hardware) (x y : A → Bool) (u : PathEdge w A → Bool) :
    (R.treeRule p lane b).entry () v x y u =
      (Rule.path F (fun k a => R.walk b (p a) (lane a).2 k) (Nat.clog 2 w + 1)).entry () v x y u :=
  rfl

/-- At a hardware port the path variable on the first edge gives
the unique allowed value of the intermediate bit. -/
theorem deployRule_entry (v : R.Hardware) (x y : A → Bool) (u : R.Supply A n → Bool) :
    let s := fun e => u (.inl (0, e))
    let t := fun e => u (.inr (.inr (0, e)))
    (R.deployRule p q σ lane inj route).entry () v x y u =
      (R.treeRule p lane false).entry () v s x (u ∘ Sum.inl) *
        ((R.layerRule p q σ lane inj route).entry () v s t (u ∘ Sum.inr ∘ Sum.inl) *
          (R.treeRule q lane true).entry () v t y (u ∘ Sum.inr ∘ Sum.inr)) := by
  intro s t
  let f := R.treeRule p lane false
  let g := R.layerRule p q σ lane inj route
  let h := R.treeRule q lane true
  have hs := Rule.series_eval f.reverse (g.series h) v x y u s (by
    intro a ha _ e he
    exact Rule.path_head (K := F) (fun j e => R.walk false (p e) (lane e).2 j) v a x _ ha e he)
  have ht := Rule.series_eval g h v s y (u ∘ Sum.inr) t (by
    intro a _ ha e he
    exact Rule.path_head (K := F) (fun j e => R.walk true (q e) (lane e).2 j) v a y _ ha e he)
  rw [ht] at hs
  exact hs

end OAI.LinearAlgebra.MatrixExponent.Packing.Rotor
end

/-! # Reindexing a layer of a programmed rotor -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Packet.Rule
open scoped Classical
variable {F S A B E : Type} [Field F] [Fintype S] [Fintype A] [Fintype B]

def fill (i : A → E) (x : A → Bool) (a : E) :=
  if ha : ∃ b, i b = a then x ha.choose else false

theorem fill_eval (i : A → E) (x : A → Bool) (hi : Function.Injective i) (a : A) :
    fill i x (i a) = x a := by
  have ht := show ∃ b, i b = i a from ⟨a, rfl⟩
  simp only [fill, dite_eq_left ht, hi ht.choose_spec]

theorem fill_map (i : A → E) (j : B → E) (hi : Function.Injective i)
    (e : A ≃ B) (he : ∀ a, i a = j (e a)) (x : A → Bool) (y : B → Bool)
    (hx : ∀ a, x a = y (e a)) : fill i x = fill j y := by
  have hj : Function.Injective j := by
    intro b c hh
    obtain ⟨a, rfl⟩ := e.surjective b
    obtain ⟨d, rfl⟩ := e.surjective c
    rw [← he, ← he, hi.eq_iff] at hh
    rw [hh]
  funext v
  by_cases ht : ∃ a, i a = v
  · obtain ⟨a, rfl⟩ := ht
    rw [fill_eval i x hi, he, fill_eval j y hj, hx]
  have ht' : ¬∃ b, j b = v := by
    rintro ⟨b, h⟩
    exact ht ⟨e.symm b, by rw [he, e.apply_symm_apply, h]⟩
  simp only [fill, ht, ht', dite_false]

theorem path_map (n : ℕ) (P : ℕ → A → S) (Q : ℕ → B → S) (e : A ≃ B)
    (hp : ∀ k a, P k a = Q k (e a)) (v : S) (x y : A → Bool) (z : Fin n × A → Bool)
    (x' y' : B → Bool) (z' : Fin n × B → Bool)
    (hx : ∀ a, x a = x' (e a)) (hy : ∀ a, y a = y' (e a)) (hz : ∀ i a, z (i, a) = z' (i, e a)) :
    (Rule.path F P n).entry () v x y z = (Rule.path F Q n).entry () v x' y' z' := by
  have left (i : Fin (n + 1)) a :
      Fin.cons (α := fun _ => A → Bool) x (Function.curry z) i a =
        Fin.cons (α := fun _ => B → Bool) x' (Function.curry z') i (e a) := by
    induction i using Fin.cases <;> simp [hx, hz]
  have right (i : Fin (n + 1)) a :
      Fin.snoc (α := fun _ => A → Bool) (Function.curry z) y i a =
        Fin.snoc (α := fun _ => B → Bool) (Function.curry z') y' i (e a) := by
    induction i using Fin.lastCases <;> simp [hy, hz]
  simp only [path_entry, left, right, hp]
  congr! 2 with i
  constructor
  · intro h b; obtain ⟨a, rfl⟩ := e.surjective b; exact h a
  · exact fun h a => h _

end OAI.LinearAlgebra.MatrixExponent.Spectral.Packet.Rule

namespace OAI.LinearAlgebra.MatrixExponent.Packing.Rotor
open Spectral.Packet
open scoped Classical
variable {F A B : Type} [Field F] [Fintype A] [Fintype B] {Y w n : ℕ} (R : Rotor F Y w)

private def plug (p : A → Fin Y) (lane : A → Fin n × Fin w) (a : A) : Σ _ : Fin n, Fin Y × Fin w :=
  ⟨(lane a).1, p a, (lane a).2⟩

variable (p q : A → Fin Y) (p' q' : B → Fin Y) (σ : Fin n → Equiv.Perm (Fin Y))
  (l : A → Fin n × Fin w) (l' : B → Fin n × Fin w)
  (hi : Function.Injective (fun a => (p a, l a))) (hr : ∀ a, σ (l a).1 (p a) = q a)
  (hi' : Function.Injective (fun a => (p' a, l' a))) (hr' : ∀ a, σ (l' a).1 (p' a) = q' a)

theorem layer_map (e : A ≃ B) (hp : ∀ a, p a = p' (e a)) (hl : ∀ a, l a = l' (e a))
    (v : R.Hardware) (x y : A → Bool) (x' y' : B → Bool) (z : R.LayerEdge n → Bool)
    (hx : ∀ a, x a = x' (e a)) (hy : ∀ a, y a = y' (e a)) :
    (R.layerRule p q σ l hi hr).entry () v x y z =
      (R.layerRule p' q' σ l' hi' hr').entry () v x' y' z := by
  have he : Function.Injective (plug p l) := by
    intro a b hab
    simp only [plug, Sigma.mk.inj_iff, heq_eq_eq, Prod.mk.injEq] at hab
    exact hi (Prod.ext hab.2.1 (Prod.ext hab.1 hab.2.2))
  have ht : ∀ a, plug p l a = plug p' l' (e a) := by intro a; simp only [plug, hp, hl]
  have hx' := Rule.fill_map _ _ he e ht x x' hx
  have hy' := Rule.fill_map _ _ he e ht y y' hy
  let f := Rule.parallel_one (fun t : Fin n => (R.packet (σ t)).rule)
  let g := f.place (fun t => (Sum.inl t.2 : R.Hardware))
  change g.entry () v (Rule.fill (plug p l) x) (Rule.fill (plug p l) y) z =
    g.entry () v (Rule.fill (plug p' l') x') (Rule.fill (plug p' l') y') z
  rw [hx', hy']

def supplyMap {m : ℕ} (e : A ≃ B) (hn : n = m) : R.Supply A n → R.Supply B m
  | .inl (j, a) => .inl (j, e a)
  | .inr (.inl ⟨i, b⟩) => .inr (.inl ⟨i.cast hn, b⟩)
  | .inr (.inr (j, a)) => .inr (.inr (j, e a))

theorem deploy_map {m : ℕ} (σ' : Fin m → Equiv.Perm (Fin Y)) (l' : B → Fin m × Fin w)
    (hi' : Function.Injective (fun a => (p' a, l' a))) (hr' : ∀ a, σ' (l' a).1 (p' a) = q' a)
    (e : A ≃ B) (hn : n = m) (hp : ∀ a, p a = p' (e a)) (hq : ∀ a, q a = q' (e a))
    (hl : ∀ a, ((l a).1.cast hn, (l a).2) = l' (e a)) (hc : ∀ i, σ i = σ' (i.cast hn))
    (v : R.Hardware) (x y : A → Bool) (z : R.Supply A n → Bool) (x' y' : B → Bool)
    (z' : R.Supply B m → Bool)
    (hx : ∀ a, R.root false (p a) = v → x a = x' (e a))
    (hy : ∀ a, R.root true (q a) = v → y a = y' (e a))
    (hz : ∀ i, (R.supply p q l i).1 = v ∨ (R.supply p q l i).2 = v →
      z i = z' (R.supplyMap e hn i)) :
    (R.deployRule p q σ l hi hr).entry () v x y z =
      (R.deployRule p' q' σ' l' hi' hr').entry () v x' y' z' := by
  subst m
  have hσ : σ = σ' := funext hc
  subst σ'
  have hl' : ∀ a, l a = l' (e a) := hl
  have hh := (R.deployRule p q σ l hi hr).local' () v x y z (x' ∘ e) (y' ∘ e)
    (z' ∘ R.supplyMap e rfl) hx hy hz
  rw [hh, deployRule_entry, deployRule_entry]
  apply congrArg₂ (·*·)
  · rw [treeRule_entry, treeRule_entry]
    apply Rule.path_map _ _ _ e
    · intro k a; simp only [hp, hl']
    · intro; rfl
    · intro; rfl
    · intro _ _; rfl
  apply congrArg₂ (·*·)
  · exact R.layer_map p q p' q' σ l l' hi hr hi' hr' e hp hl' v _ _ _ _ _ (fun _ => rfl) (fun _ => rfl)
  rw [treeRule_entry, treeRule_entry]
  apply Rule.path_map _ _ _ e
  · intro k a; simp only [hq, hl']
  · intro; rfl
  · intro; rfl
  · intro _ _; rfl

end OAI.LinearAlgebra.MatrixExponent.Packing.Rotor
end

/-! # Evaluating one site's contribution in a parallel delivery -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Packet.Rule

open scoped Classical

theorem select_entry_equiv {K S A B E : Type} [Field K] [Fintype S] [Fintype A] [Fintype B]
    [Fintype E] {D : B → S × S} {W : E → S × S} (h : Rule K D (fun _ : Unit => W))
    (i : A ≃ B) (v : S) (x y : A → Bool) (z : E → Bool) :
    (h.select i.toEmbedding).entry () v x y z = h.entry () v (x ∘ i.symm) (y ∘ i.symm) z := by
  have he (x : A → Bool) : fill i x = x ∘ i.symm := by
    funext b
    obtain ⟨a, rfl⟩ := i.surjective b
    simp only [fill_eval i x i.injective, Function.comp_apply, Equiv.symm_apply_apply]
  rw [← he, ← he]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Spectral.Packet.Rule

namespace OAI.LinearAlgebra.MatrixExponent.Packing.Delivery
open Spectral.Packet Finset
open scoped Classical

variable {P U X W F : Type} [Fintype P] [Field F] [Fintype X] [Fintype U]
  {leaf : P → X} {point : U → Bool → P} {good : U → Prop}
  {edge : U → W} {outLeaf : W → Bool → X} {cap : W → ℝ} {Y w : ℕ}
  {out : ∀ x, Port outLeaf cap Y x ↪ Fin Y} {l : P → ℝ} {u : ℝ}
  (d : Delivery leaf point good edge outLeaf cap Y w out l u) (R : Rotor F Y w)

theorem deploy_entry (v : X) (t : R.Hardware) (x y : {e // good e} → Bool) (z : d.Wires R → Bool) :
    (d.deployRule R).entry () (v, t) x y z =
      (R.deployRule (d.inputAt v) (d.outputAt v) (d.config v) (d.lane v) (d.input v)
        (d.routes v)).entry () t (fun e => if e.val.2 then y e.val.1 else x e.val.1)
        (fun e => z (.inr e.val.1)) (fun b => z (.inl ⟨v, b⟩)) := by
  let s : Finset (Σ _ : X, R.Hardware) := univ.filter fun b => (b.1, b.2) = (v, t)
  have hs : s = {⟨v, t⟩} := by ext ⟨i, j⟩; simp [s]
  dsimp only [s] at hs
  simp only [deployRule, Rule.join_outputs, Rule.select_entry_equiv, Rule.place, hs, prod_singleton]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Packing.Delivery
end

/-! # Closure rules for compressed reset factors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Packet.Rule
open Assembly.History.Reset Classical

variable {F S E U : Type} [Field F] [Fintype S] [Fintype E] [Fintype U]
  {D : E → S × S} {W : U → S × S}

/-- Every way of plugging named bits or zero into this site gives
a product of trivalent factors. -/
def Simple (h : Rule F D (fun _ : Unit => W)) : Prop :=
  ∀ (J : Type) [Fintype J] (v : S) (x y : E → Option J) (z : U → Option J),
    (fun a => h.entry () v (readBit J a ∘ x) (readBit J a ∘ y) (readBit J a ∘ z)) ∈ simple F J

namespace Simple
variable {h : Rule F D (fun _ : Unit => W)}

theorem congr {D' W'} (hh : Simple h) (hd : D = D') (hw : W = W') :
    Simple (h.congr hd (congrArg (fun t _ => t) hw)) := by
  subst D' W'
  exact hh

theorem place {T : Type} [Fintype T] (hh : Simple h) (g : S → T) : Simple (h.place g) := by
  intro J _ v x y z
  exact prod_simple (Finset.univ.filter (fun w => g w = v)) _ (fun w _ => hh J w x y z)

theorem select {B : Type} [Fintype B] (hh : Simple h) (e : B ↪ E) : Simple (h.select e) := by
  intro J _ v x y z
  let fill (p : B → Option J) (i : E) := if hi : ∃ b, e b = i then p hi.choose else none
  have ext (a : J → Bool) (p : B → Option J) :
      (fun i => if hi : ∃ b, e b = i then readBit J a (p hi.choose) else false) =
        readBit J a ∘ fill p := by
    funext i
    unfold Function.comp fill
    split_ifs <;> rfl
  convert hh J v (fill x) (fill y) z using 1
  funext a
  rw [← ext, ← ext]
  rfl

theorem partition (G : E → Prop) [DecidablePred G] {Z : Type} [Fintype Z] {V : Z → S × S}
    {hf : Rule F (fun e : {i // G i} => D e.val) (fun _ : Unit => W)}
    {hg : Rule F (fun e : {i // ¬G i} => D e.val) (fun _ : Unit => V)}
    (f : Simple hf) (g : Simple hg) : Simple (Rule.partition G D hf hg) := by
  intro J _ v x y z
  exact (simple F J).mul_mem (f J v (x ∘ Subtype.val) (y ∘ Subtype.val) (z ∘ Sum.inl))
    (g J v (x ∘ Subtype.val) (y ∘ Subtype.val) (z ∘ Sum.inr))

theorem parallel {K : Type} [Fintype K] {S E U : K → Type}
    [∀ k, Fintype (S k)] [∀ k, Fintype (E k)] [∀ k, Fintype (U k)]
    {D : (k : K) → E k → S k × S k} {W : (k : K) → U k → S k × S k}
    {h : ∀ k, Rule F (D k) (fun _ : Unit => W k)} (hs : ∀ k, Simple (h k)) :
    Simple (Rule.parallel_one h) := by
  rintro J _ ⟨k, v⟩ x y z
  exact hs k J v (x ∘ Sigma.mk k) (y ∘ Sigma.mk k) (z ∘ Sigma.mk k)

theorem join_outputs {a b : E × Bool → S}
    {h : Rule F (fun e => (a e, b e)) (fun _ : Unit => W)} (hh : Simple h) :
    Simple h.join_outputs := by
  intro J _ v x y z
  let p (e : E × Bool) := if e.2 then y e.1 else x e.1
  convert hh J v p (fun e => z (.inr e.1)) (z ∘ Sum.inl) using 1
  funext a
  have he : readBit J a ∘ p = fun e => if e.2 then readBit J a (y e.1) else readBit J a (x e.1) := by
    funext e
    simp only [Function.comp_apply, p]
    split_ifs <;> rfl
  rw [he]
  rfl

end Simple

theorem path_simple (D : ℕ → E → S) (n : ℕ) : (Rule.path F D n).Simple := by
  intro J _ v x y z
  let a : Fin (n + 1) → E → Option J := Fin.cons x (Function.curry z)
  let b : Fin (n + 1) → E → Option J := Fin.snoc (Function.curry z) y
  let t := Finset.univ.filter (fun p : Fin (n + 1) × E => D p.1.val p.2 = v)
  have h := prod_simple t _ (fun p _ => check_simple (F := F) (a p.1 p.2) (b p.1 p.2))
  convert h using 1
  funext g
  rw [path_entry, Finset.prod_ite_zero, Finset.prod_const_one]
  have ha (i : Fin (n + 1)) e :
      Fin.cons (α := fun _ => E → Bool) (readBit J g ∘ x) (Function.curry (readBit J g ∘ z)) i e =
        readBit J g (a i e) := by induction i using Fin.cases <;> simp [a]
  have hb (i : Fin (n + 1)) e :
      Fin.snoc (α := fun _ => E → Bool) (Function.curry (readBit J g ∘ z)) (readBit J g ∘ y) i e =
        readBit J g (b i e) := by induction i using Fin.lastCases <;> simp [b]
  simp only [ha, hb, t, Finset.mem_filter, Finset.mem_univ, true_and, Prod.forall]

end OAI.LinearAlgebra.MatrixExponent.Spectral.Packet.Rule
end

/-! # Trivalent factors of a deployed rotor -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Packing.Rotor
open Assembly.History.Reset Spectral.Packet Classical
variable {F A : Type} [Field F] [Fintype A] {Y w n : ℕ}
  (R : Rotor F Y w)

theorem packet_simple (σ : Equiv.Perm (Fin Y)) : (R.packet σ).rule.Simple := by
  intro J _ v x y z
  let f : RotorEnd Y w R.E → Option J
    | .inl (false, i, j) => x (i, j)
    | .inl (true, i, j) => y (σ.symm i, j)
    | .inr (.inl i) => z i
    | .inr (.inr i) => z i
  apply local_table _ (fun i : {q // R.pos q = v} => f i.val) (R.degree v)
  intro a b he
  apply (R.packet σ).rule.local'
  · rintro ⟨i, j⟩ h
    exact he ⟨.inl (false, i, j), h⟩
  · rintro ⟨i, j⟩ h
    simpa only [f, Function.comp_apply, Equiv.symm_apply_apply] using he ⟨.inl (true, σ i, j), h⟩
  · rintro e (h|h)
    · exact he ⟨.inr (.inl e), h⟩
    · exact he ⟨.inr (.inr e), h⟩

variable (p q : A → Fin Y) (σ : Fin n → Equiv.Perm (Fin Y))
  (lane : A → Fin n × Fin w) (inj : Function.Injective (fun a => (p a, lane a)))
  (route : ∀ a, σ (lane a).1 (p a) = q a)

theorem layer_simple : (R.layerRule p q σ lane inj route).Simple := by
  unfold layerRule
  apply Rule.Simple.congr
  apply Rule.Simple.place
  apply Rule.Simple.select
  exact Rule.Simple.parallel (fun t => R.packet_simple (σ t))
  rfl

theorem tree_simple (b : Bool) : (R.treeRule p lane b).Simple := by
  intro J _ v x y z
  simp only [treeRule_entry]
  exact Rule.path_simple _ _ J v x y z

theorem deploy_simple : (R.deployRule p q σ lane inj route).Simple := by
  intro J _ v x y z
  let s := fun e => z (.inl (0, e))
  let t := fun e => z (.inr (.inr (0, e)))
  have h₁ := R.tree_simple p lane false J v s x (z ∘ Sum.inl)
  have h₂ := R.layer_simple p q σ lane inj route J v s t (z ∘ Sum.inr ∘ Sum.inl)
  have h₃ := R.tree_simple q lane true J v t y (z ∘ Sum.inr ∘ Sum.inr)
  convert (simple F J).mul_mem h₁ ((simple F J).mul_mem h₂ h₃) using 1
  funext a
  exact R.deployRule_entry p q σ lane inj route v _ _ _

end OAI.LinearAlgebra.MatrixExponent.Packing.Rotor
end

/-! # The load pays for visible spans, hidden bundles and inherited histories -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Coloring Packing Finset
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h u a : ℕ}
  {G : HostNet F L h u} {S : Scheme F} {r : S.format.obj} (p : S.Posting r G)
  {B' W : ℝ} {Hcap D : ℕ}
  (q : ResetResult F a G.N G.src G.dst G.ix G.load u B' W Hcap D)
  (v : Cell a × q.vertex)

theorem loaded_bound : push q.owner (Function.uncurry G.load) v ≤ 89 * B' :=
  (le_add_of_nonneg_right (by positivity)).trans (q.load v)

theorem hidden_bound : (Fintype.card (Hidden q v) : ℝ) * u ≤ 89 * B' := by
  let f := fun e => Prod.map q.owner q.owner (G.pair e)
  have hk : Fintype.card (Hidden q v) ≤ degree f v + degree q.supply v := by
    rw [Fintype.card_subtype, card_eq_sum_ones, sum_filter, degree_sum, degree_sum,
      Fintype.sum_sum_type, Fintype.sum_sum_type, ← add_assoc, ← sum_add_distrib]
    apply Nat.add_le_add
    · apply sum_le_sum
      intro e _
      simp [ends, arityCost, f, HostNet.pair]
      apply le_of_eq; congr
    · apply sum_le_sum
      intro e _
      by_cases he : q.supply e = (v, v) <;> simp [ends, he, arityCost]
  have hold : (degree f v : ℝ) * u ≤ push q.owner (Function.uncurry G.load) v := by
    unfold f
    rw [degree_map, Nat.cast_sum, sum_mul]
    apply sum_le_sum
    intro j _
    by_cases hj : q.owner j = v
    · simp only [ite_eq_left hj]
      exact (le_add_of_nonneg_left (Nat.cast_nonneg _)).trans (G.core_le_load _ _)
    · simp [hj]
  refine (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr hk) (Nat.cast_nonneg _)).trans ?_
  rw [Nat.cast_add, add_mul]
  exact (add_le_add_left hold _).trans (q.load v)

variable (hu : ∀ j, u ≤ p.toPresentation.borderWidth j)

include hu in
theorem width_floor (j : Port p q v) : u ≤ width p q v j := by
  rcases j with ⟨j|j, _⟩|j
  · exact hu j
  · exact le_rfl
  · exact le_rfl

include hu in
theorem visible_bound : (Fintype.card (Visible p q v) : ℝ) * u ≤ 89 * B' := by
  have hk : Fintype.card (Visible p q v) * u ≤ (q.contract G.units).arity v := by
    have eq := Fintype.card_congr (visibleBits p q v)
    simp only [Fintype.card_sigma, Fintype.card_fin, Diagram.Port, Fintype.card_sum, card_slots] at eq
    have hl (j : Visible p q v) : u ≤ visibleWidth p q j.val :=
      width_floor p q v hu (.inl j)
    have hh := sum_le_sum (s := univ) (fun j _ => hl j)
    rw [sum_const, card_univ, Nat.nsmul_eq_mul] at hh
    exact hh.trans_eq eq
  rw [← Nat.cast_mul]
  apply (Nat.cast_le.mpr hk).trans (q.arity_contract G.units ?_ v)
  intro i
  exact (le_add_of_nonneg_right (by positivity)).trans (G.core_le_load _ _)

include p in
private theorem live_cost (c : Live q v → ℝ) (mass : G.V × Cell h → ℝ)
    (hm : ∀ i, 0 ≤ mass i) (hc : ∀ w, c w ≤ mass (G.units.place w.val)) :
    (∑ w, c w) ≤ push q.owner mass v := by
  let f (t : G.V × Cell h) := if q.owner t = v then mass t else 0
  let e : Live q v ↪ G.V × Cell h := ⟨fun i => G.units.place i.val, by
    intro i j hij
    change G.units.place i.val = G.units.place j.val at hij
    apply Subtype.ext
    apply p.vertex.injective
    rw [p.vertex_eq, p.vertex_eq, hij]⟩
  have hh : push q.owner mass v = ∑ i, f i := by
    apply sum_congr rfl
    intro i _
    unfold f; congr
  rw [hh]
  calc
    _ ≤ ∑ w, f (e w) := sum_le_sum fun w _ => (hc w).trans_eq (ite_eq_left w.property.2).symm
    _ ≤ _ := by
      rw [← sum_map univ e]
      apply sum_le_sum_of_subset_of_nonneg (subset_univ _)
      intro i _ _
      unfold f
      split <;> first | exact hm i | exact le_rfl

def inherited (o : B S.ℓ ≃ B S.ℓ) := ∑ w : Live q v, Dense.used (o (oldLabel p w.val).1).val

theorem inherited_le (o : B S.ℓ ≃ B S.ℓ) (mass : G.V × Cell h → ℝ) (hm : ∀ i, 0 ≤ mass i)
    (hc : ∀ w, 0 < G.diagram.arity w → (Dense.used (o (oldLabel p w).1).val : ℝ) ≤ mass (G.units.place w)) :
    (inherited p q v o : ℝ) ≤ push q.owner mass v := by
  rw [inherited, Nat.cast_sum]
  exact live_cost p q v _ mass hm fun w => hc w.val w.property.1

include hu in
private theorem live_floor (w : Live q v) : u ≤ G.diagram.arity w.val := by
  have eq := Fintype.card_congr (p.pin w.val)
  simp only [Diagram.Port, Fintype.card_sum, card_slots] at eq
  change G.diagram.arity w.val = Fintype.card (S.LocalPin r (p.vertex w.val)) at eq
  obtain ⟨⟨j, t⟩⟩ := Fintype.card_pos_iff.mp (w.property.1.trans_eq eq)
  let m := oldMap p q v w.val w.property.2
  have hl : u ≤ S.width r (p.vertex w.val, j) :=
    (width_floor p q v hu _).trans_eq (m.size j t.pos)
  rw [eq]
  simp only [Scheme.LocalPin, Fintype.card_sigma]
  simp only [Fintype.card_fin]
  exact hl.trans (single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ j))

include hu in
theorem live_bound : (Fintype.card (Live q v) : ℝ) * u ≤ 89 * B' := by
  have hload (w : Live q v) : (u : ℝ) ≤ Function.uncurry G.load (G.units.place w.val) := by
    let t := G.units.place w.val
    have hv : (G.diagram.arity w.val : ℝ) ≤ push G.units.place (fun i => (G.diagram.arity i : ℝ)) t := by
      unfold push
      refine le_trans ?_ (single_le_sum (fun i _ => by split_ifs <;> positivity) (mem_univ w.val))
      simp [t]
    change _ ≤ G.load t.1 t.2
    rw [G.load_eq t]
    exact ((Nat.cast_le.mpr (live_floor p q v hu w)).trans hv).trans
      ((le_add_of_nonneg_right (mul_nonneg L.pos.le (push_nonneg _ _ L.nonneg _))).trans
        (le_add_of_nonneg_right (mul_nonneg G.rate_nonneg (Nat.cast_nonneg _))))
  have hc := live_cost p q v (fun _ => (u : ℝ)) (Function.uncurry G.load)
    (fun t => G.load_nonneg t.1 t.2) hload
  rw [sum_const, card_univ, nsmul_eq_mul] at hc
  exact hc.trans (loaded_bound q v)

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-! # Encoding station references and collecting the new factors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Packing Coloring
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h u a : ℕ}
  {G : HostNet F L h u} {S : Scheme F} {r : S.format.obj} (p : S.Posting r G)
  {B' W : ℝ} {Hcap D : ℕ}
  (q : ResetResult F a G.N G.src G.dst G.ix G.load u B' W Hcap D)
  (v : Cell a × q.vertex) {e : ℕ}
  (slot : Port p q v → Addr e) (o : B S.ℓ ≃ B S.ℓ)

def access (g : Addr e → ℕ → Bool) : Tape p q v := fun i j => g (slot i) j.val

private def instruction (i : Live q v) : Control S e :=
  (true, (oldLabel p i.val).2, fun j =>
    if hj : 0 < (original S (oldLabel p i.val)).width j then
      slot ((oldMap p q v i.val i.property.2).slot j hj)
    else .inl 0)

private theorem instruction_eq (i : Live q v) (g : Addr e → ℕ → Bool) :
    prior o (instruction p q v slot i) (o (oldLabel p i.val).1) g =
      previous p q v (access p q v slot g) i := by
  unfold prior
  rw [Equiv.symm_apply_apply]
  unfold instruction previous
  dsimp only [original, access]
  rw [ite_eq_left rfl]
  apply congrArg
  funext j t
  erw [dite_eq_left t.pos]
  rfl

theorem previous_code (n : Live q v ↪ B e) :
    ∃ c : B e → Control S e, ∃ t : B e → B S.ℓ, Dense.cost t = inherited p q v o ∧
      ∀ g : Addr e → ℕ → Bool,
      (∏ j, prior o (c j) (t j) g) = ∏ i, previous p q v (access p q v slot g) i := by
  let c := Function.extend n (instruction p q v slot) (fun _ => (false, 0, fun _ => Sum.inl 0))
  let t := Function.extend n (fun i => o (oldLabel p i.val).1) (fun _ => 0)
  refine ⟨c, t, ?_, ?_⟩
  · symm
    refine Fintype.sum_of_injective n n.injective _ _ ?_ ?_
    · intro j hj
      simp only [t, Function.extend_apply' _ _ _ hj]
      exact Dense.used_zero
    · intro j
      simp only [t, n.injective.extend_apply]
  · intro g
    symm
    refine Fintype.prod_of_injective n n.injective _ _ ?_ ?_
    · intro j hj
      simp only [c, Function.extend_apply' _ _ _ hj]
      rfl
    · intro j
      simp only [c, t, n.injective.extend_apply]
      exact (instruction_eq p q v slot o j g).symm

private def sourceRef (t : Bool) (i : G.E) : Option (Addr e) :=
  if h : demandSite q i t = v then some (slot (demand p q v i t h)) else none

private def wireRef (i : q.wire) : Option (Addr e) :=
  if h : supplySite q i false = v then some (slot (supply p q v i false h))
  else if h : supplySite q i true = v then some (slot (supply p q v i true h)) else none

theorem created_code (hs : q.rule.Simple) : ∃ c : Tables F (Addr e),
    ∀ g : Addr e → ℕ → Bool,
      (∏ j : Fin u, evaluate F (Addr e) c (fun i => g i j.val)) =
        created p q v (access p q v slot g) := by
  obtain ⟨c, hc⟩ := hs (Addr e) v (sourceRef p q v slot false)
    (sourceRef p q v slot true) (wireRef p q v slot)
  refine ⟨c, fun g => Finset.prod_congr rfl ?_⟩
  intro j _
  let y (i : Addr e) := g i j.val
  have src (t : Bool) : readBit _ y ∘ sourceRef p q v slot t =
      inBits p q v (access p q v slot g) t j := by
    funext i
    unfold Function.comp sourceRef inBits
    split_ifs <;> rfl
  have dest : readBit _ y ∘ wireRef p q v slot =
      outBits p q v (access p q v slot g) j := by
    funext i
    unfold Function.comp wireRef outBits
    split_ifs <;> rfl
  exact (congrFun hc y).trans (by rw [src, src, dest])

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-!
# Existence of a short recipe

The order of the hidden wires and of the previous stations is arbitrary.
Only the lengths of the occupied old labels contribute to the variable
part of a recipe.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Packing Coloring
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h u a : ℕ}
  {G : HostNet F L h u} {S : Scheme F} {r : S.format.obj} (p : S.Posting r G)
  {B' W : ℝ} {Hcap D : ℕ}
  (q : ResetResult F a G.N G.src G.dst G.ix G.load u B' W Hcap D)
  (v : Cell a × q.vertex) {e : ℕ}
  (seat : Visible p q v ↪ B e) (o : B S.ℓ ≃ B S.ℓ)

theorem describe (hs : q.rule.Simple)
    (hn : ∀ w, G.diagram.arity w = 0 → ∀ z, Transcript.sample (G.diagram.table w) z = 1)
    (hi : Fintype.card (Hidden q v) ≤ 2 ^ e) (hl : Fintype.card (Live q v) ≤ 2 ^ e) :
    ∃ a : Recipe S e, run o u a = localEval p q v seat ∧ Dense.cost a.2 = inherited p q v o := by
  let J := Fintype.equivFin (Hidden q v)
  let slot : Port p q v → Addr e := Sum.map seat (fun i => (J i).castLE hi)
  let b := J.prodCongr (Equiv.refl (Fin u))
  have hread (x : B e → ℕ → Bool) (z : Fin (Fintype.card (Hidden q v)) × Fin u → Bool) :
      access p q v slot (fetch x z) = tape p q v seat x (z ∘ b) := by
    funext j t
    cases j with
    | inl j => rfl
    | inr j =>
      change fetch x z (.inr ((J j).castLE hi)) t.val = z (J j, t)
      have ht : (J j).val < Fintype.card (Hidden q v) ∧ t.val < u := ⟨(J j).isLt, t.isLt⟩
      simp only [fetch, Fin.val_castLE, dite_eq_left ht]
      rfl
  let n := (Fintype.equivFin (Live q v)).toEmbedding.trans (Fin.castLEEmb hl)
  obtain ⟨c, t, ht, hc⟩ := previous_code p q v slot o n
  obtain ⟨d, hd⟩ := created_code p q v slot hs
  refine ⟨((⟨_, Nat.lt_succ_of_le hi⟩, c, d), t), ?_, ht⟩
  funext x
  rw [eval_formula p q v hn]
  unfold run
  refine Fintype.sum_equiv (b.symm.arrowCongr (Equiv.refl Bool)) _ _ ?_
  intro z
  change (∏ j, prior o (c j) (t j) (fetch x z)) *
    (∏ j : Fin u, evaluate F (Addr e) d (fun i => fetch x z i j.val)) = _
  rw [hc, hd, hread]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end

/-! # Recovering the predecessor of each exterior span after a reset -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset

open Packing Coloring
open scoped Classical

variable {T F : Type} [Field F] [Fintype T] {x y : Wire} {L : Fringe x y T} {h u a : ℕ}
  {G : HostNet F L h u} {S : Scheme F} {r : S.format.obj} (p : S.Posting r G)
  {B' W : ℝ} {Hcap D : ℕ}
  (q : ResetResult F a G.N G.src G.dst G.ix G.load u B' W Hcap D)

open BatchDescent.Trail

def facePointer : Face p q → Option (B 0 × Stub S)
  | .inl j => some (0, stub (p.vertex j.val.1, j.val.2))
  | .inr _ => none

namespace Allocation
variable {p q} {U : Scheme F} (A : Allocation p q U) (parent : B U.m → B S.m)

/-- A reset never imports an exterior span from a neighbor of the
parent host. All the predecessor pointers therefore have hop zero. -/
def move : Move S U 0 where
  nav i _ := parent i
  read := Function.extend A.span (facePointer p q) (fun _ => none)

@[simp] theorem read_span (j : Face p q) :
    (A.move parent).read (A.span j) = facePointer p q j :=
  A.span_injective.extend_apply (facePointer p q) (fun _ => none) j

theorem read_idle (s : U.Span) (hs : s ∉ Set.range A.span) : (A.move parent).read s = none :=
  Function.extend_apply' (facePointer p q) (fun _ => none) s hs

private theorem previous_span (hp : ∀ w, parent (A.host w) = p.host (q.origin w))
    (j : p.toPresentation.BorderSpan) :
    (A.move parent).previous (A.span (.inl j)) = some (p.vertex j.val.1, j.val.2) := by
  rw [Move.previous, read_span]
  change some ((parent (A.host (q.owner (G.units.place j.val.1)).2),
    (p.vertex j.val.1).2), j.val.2) = _
  rw [hp, q.origin_owner, p.vertex_eq]

private theorem boundary_val {x y : Wire} {G : Diagram F x y} {S : Scheme F}
    {r : S.format.obj} (p : S.Presentation r G) (i : slots x ⊕ slots y) :
    (p.boundary i).val = p.toSeating.ends (boundaryEnd G i) := by cases i <;> rfl

theorem move_agrees {out : U.format.obj} (l : A.Lengths out) (H : A.Agrees l)
    (parent : B U.m → B S.m) (hp : ∀ w, parent (A.host w) = p.host (q.origin w)) :
    (A.move parent).Agrees p.toPresentation (A.posting l H).toPresentation := by
  have he (j : p.toPresentation.BorderBit) :
      ((A.posting l H).toPresentation.boundary (p.toPresentation.exteriorBits j)).val =
        ⟨A.span (.inl j.1), j.2.cast (l.used (.inl j.1)).symm⟩ := by
    rw [boundary_val]
    exact A.exposed_pin l H j
  constructor
  · intro i
    obtain ⟨j, rfl⟩ := p.toPresentation.exteriorBits.surjective i
    rw [he, boundary_val, p.toPresentation.border_pin]
    exact ⟨A.previous_span parent hp _, l.used (.inl j.1), rfl⟩
  · intro s hs
    by_cases h : s ∈ Set.range A.span
    · obtain ⟨j|j, rfl⟩ := h
      · let t : p.toPresentation.BorderBit := ⟨j, ⟨0, j.property.1⟩⟩
        exact ⟨p.toPresentation.exteriorBits t, congrArg Sigma.fst (he t)⟩
      · rw [read_span] at hs
        cases hs
    · rw [A.read_idle parent s h] at hs
      cases hs

end Allocation
end OAI.LinearAlgebra.MatrixExponent.Assembly.History.Reset
end
