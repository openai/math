import OAI.LinearAlgebra.MatrixExponent.Spectral.Rank
import OAI.LinearAlgebra.MatrixExponent.Spectral.Transport
import Mathlib.Data.Fintype.Option
import OAI.LinearAlgebra.MatrixExponent.Spectral.Rule

/-!
# Direct sums as ordinary sums of restrictions

Expanding the source direct sum gives independent local matrices for
each summand. The formula holds in all characteristics.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Raw

variable {K S I : Type} [Field K] [Fintype S]

abbrev Local (A B : Raw K S) := (s : S) → B.leg s → A.leg s → K

def applyLocal (A : Raw K S) {B : Raw K S} (L : Local A B) (x : ∀ s, B.leg s) : K :=
  ∑ i : A.term, ∏ s, ∑ y : A.leg s, L s (x s) y * A.factor i s y

theorem applyLocal_add (A B C : Raw K S) (L : Local (A + B) C) (x : ∀ s, C.leg s) :
    (A + B).applyLocal L x =
      A.applyLocal (fun s u y => L s u (.inl y)) x +
      B.applyLocal (fun s u y => L s u (.inr y)) x := by
  change (∑ i : A.term ⊕ B.term, ∏ s, ∑ y : A.leg s ⊕ B.leg s,
    L s (x s) y * (A + B).factor i s y) = _
  simp only [Fintype.sum_sum_type]
  change
    (∑ i, ∏ s, ((∑ y, L s (x s) (.inl y) * A.factor i s y) +
      ∑ y : B.leg s, L s (x s) (.inr y) * 0)) +
    (∑ i, ∏ s, ((∑ y : A.leg s, L s (x s) (.inl y) * 0) +
      ∑ y, L s (x s) (.inr y) * B.factor i s y)) = _
  simp only [mul_zero, Finset.sum_const_zero, zero_add, add_zero, applyLocal]

private theorem sum_maps (A : I → Raw K S) (B : Raw K S) (s : Finset I) :
    ∃ C : Raw K S, Tensor.ofRaw C = ∑ i ∈ s, Tensor.ofRaw (A i) ∧
    (∀ L : Local C B, ∃ M : ∀ i, Local (A i) B,
      ∀ x, C.applyLocal L x = ∑ i ∈ s, (A i).applyLocal (M i) x) ∧
    (∀ M : ∀ i, Local (A i) B, ∃ L : Local C B,
      ∀ x, C.applyLocal L x = ∑ i ∈ s, (A i).applyLocal (M i) x) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    have e (L : Local 0 B) (x : ∀ s, B.leg s) : (0 : Raw K S).applyLocal L x = 0 :=
      Finset.sum_eq_zero fun i _ => Empty.elim i
    exact ⟨0, rfl, fun L => ⟨fun _ _ _ _ => 0, e L⟩, fun _ => ⟨fun _ _ _ => 0, e _⟩⟩
  | @insert i s hi ih =>
    obtain ⟨C, he, hl, hr⟩ := ih
    refine ⟨A i + C, by rw [Finset.sum_insert hi, Tensor.ofRaw_add, he], ?_, ?_⟩
    · intro L
      obtain ⟨M, hM⟩ := hl fun s u y => L s u (.inr y)
      refine ⟨Function.update M i (fun s u y => L s u (.inl y)), fun x => ?_⟩
      rw [applyLocal_add, hM, Finset.sum_insert hi, Function.update_self]
      refine congrArg _ (Finset.sum_congr rfl fun j hj => ?_)
      rw [Function.update_of_ne (ne_of_mem_of_not_mem hj hi)]
    · intro M
      obtain ⟨L, hL⟩ := hr M
      refine ⟨fun s u => Sum.elim (M i s u) (L s u), fun x => ?_⟩
      rw [applyLocal_add, Finset.sum_insert hi]
      exact congrArg _ (hL x)

theorem restriction_sum_iff (A : I → Raw K S) (B : Raw K S) (s : Finset I) :
    Tensor.ofRaw B ≤ ∑ i ∈ s, Tensor.ofRaw (A i) ↔
      ∃ M : ∀ i, Local (A i) B, ∀ x, B.coeff x = ∑ i ∈ s, (A i).applyLocal (M i) x := by
  obtain ⟨C, he, hl, hr⟩ := sum_maps A B s
  rw [← he, Tensor.ofRaw_le]
  constructor
  · rintro ⟨L, hL⟩
    obtain ⟨M, hM⟩ := hl L
    exact ⟨M, fun x => (hL x).trans (hM x)⟩
  · rintro ⟨M, hM⟩
    obtain ⟨L, hL⟩ := hr M
    exact ⟨L, fun x => (hM x).trans (hL x).symm⟩

end OAI.LinearAlgebra.MatrixExponent.Spectral.Raw
end

/-! # Bit-label coordinates for arbitrary products of wires -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

variable {K S E X Y : Type} [Field K] [Fintype S]

private theorem signals_relabel [Fintype X] [DecidableEq X] [Fintype Y] [DecidableEq Y]
    (f : S → X → X) (g : S → Y → Y) (e : X ≃ Y) (h : ∀ v x, e (f v x) = g v (e x)) :
    signals K f = signals K g := by
  apply ofRaw_eq
  refine Raw.relabel e (fun _ => e) (fun i v x => ?_)
  change (if x = f v i then (1 : K) else 0) = if e x = g v (e i) then 1 else 0
  simp only [← h, e.injective.eq_iff]

private def separate (E : Type) : (Option E → Bool) ≃ Fin 2 × (E → Bool) where
  toFun x := (finTwoEquiv.symm (x none), fun e => x (some e))
  invFun x e := e.elim (finTwoEquiv x.1) x.2
  left_inv x := by funext e; cases e <;> simp
  right_inv x := by simp

variable [DecidableEq S]

/-- Keep the bits incident to the given site. -/
def mask (D : E → S × S) (v : S) (x : E → Bool) (e : E) :=
  if (D e).1 = v ∨ (D e).2 = v then x e else false

/-- Each bit is visible at its two endpoints. Other sites see a fixed
dummy value in the same coordinate. -/
theorem signals_prod [Fintype E] [DecidableEq E] (D : E → S × S) :
    signals K (mask D) =
      ∏ e, wire K (D e).1 (D e).2 2 := by
  classical
  refine Fintype.induction_empty_option
    (P := fun T => ∀ [DecidableEq T] (D : T → S × S),
      signals K (mask D) = ∏ e, wire K (D e).1 (D e).2 2)
    ?_ ?_ ?_ E D
  · intro A B _ e ih _ F
    let := Fintype.ofEquiv B e.symm
    rw [← e.prod_comp (fun j => wire K (F j).1 (F j).2 2)]
    refine (signals_relabel _ _ (e.symm.arrowCongr (Equiv.refl Bool)) ?_).trans
      (ih (fun i => F (e i)))
    intro v x
    rfl
  · intro _ F
    rw [Finset.prod_of_isEmpty]
    apply ofRaw_eq
    let e := Equiv.ofUnique (PEmpty → Bool) Unit
    refine Raw.relabel e (fun _ => e) (fun i v x => ?_)
    change (if x = mask F v i then (1 : K) else 0) = 1
    rw [ite_eq_left (Subsingleton.elim _ _)]
  · intro A _ ih _ F
    rw [Fintype.prod_option, ← ih (fun i => F (some i)),
      ← signals_wire, ← signals_mul]
    apply signals_relabel _ _ (separate A)
    intro v x
    apply Prod.ext
    · change finTwoEquiv.symm (mask F v x none) = Raw.port _ v (finTwoEquiv.symm (x none))
      simp only [mask, Raw.port, Finset.mem_insert, Finset.mem_singleton,
        eq_comm (a := v)]
      split <;> rfl
    · rfl

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end

/-! # From a direct-sum restriction to local bit tables -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor

open Classical

variable {K S E I : Type} [Field K] [Fintype S] [DecidableEq S] [Fintype E]

private def expose (D : E → S × S) (v : S) (x y : E → Bool) (e : E) : Bool :=
  if (D e).1 = v then x e else if (D e).2 = v then y e else false

private def graph (K : Type) [Field K] (D : E → S × S) : Raw K S :=
  ⟨fun _ => E → Bool, E → Bool, fun i s x => if x = mask D s i then 1 else 0⟩

private theorem graph_coeff (D : E → S × S) (hd : ∀ e, (D e).1 ≠ (D e).2)
    (x y : E → Bool) :
    (graph K D).coeff (fun v => expose D v x y) = if x = y then 1 else 0 := by
  change (∑ i : E → Bool, ∏ v, if expose D v x y = mask D v i then (1 : K) else 0) = _
  rw [Fintype.sum_eq_single x]
  · by_cases h : x = y
    · subst y
      rw [ite_eq_left rfl]
      apply Finset.prod_eq_one
      intro v _
      apply ite_eq_left
      funext e
      by_cases ha : (D e).1 = v <;> simp [mask, expose, ha]
    · rw [ite_eq_right h]
      obtain ⟨e, he⟩ := Function.ne_iff.mp h
      apply Finset.prod_eq_zero (Finset.mem_univ (D e).2)
      apply ite_eq_right
      intro eq
      exact he (by simpa [expose, mask, hd e] using (congrFun eq e).symm)
  · intro i hi
    obtain ⟨e, he⟩ := Function.ne_iff.mp hi
    apply Finset.prod_eq_zero (Finset.mem_univ (D e).1)
    apply ite_eq_right
    intro eq
    exact he (by simpa [expose, mask] using (congrFun eq e).symm)

variable {J : I → Type} [Fintype I] [∀ i, Fintype (J i)]

private theorem packet_of_graph (D : E → S × S) (hd : ∀ e, (D e).1 ≠ (D e).2)
    (W : (i : I) → J i → S × S)
    (h : ofRaw (graph K D) ≤ ∑ i, ofRaw (graph K (W i))) :
    Packet K D W := by
  obtain ⟨L, hL⟩ := (Raw.restriction_sum_iff (fun i => graph K (W i)) (graph K D) Finset.univ).mp h
  change (i : I) → S → (E → Bool) → (J i → Bool) → K at L
  refine ⟨fun i v x y u => L i v (expose D v x y) (mask (W i) v u), ?_, ?_⟩
  · intro i v x y u x' y' u' hx hy hu
    apply congrArg₂ (L i v)
    · funext e
      unfold expose
      split
      · exact hx _ ‹_›
      split
      · exact hy _ ‹_›
      · rfl
    · funext e
      unfold mask
      split
      · exact hu _ ‹_›
      · rfl
  · intro x y
    refine (graph_coeff D hd x y).symm.trans ((hL _).trans ?_)
    change (∑ i, ∑ u : J i → Bool, ∏ v, ∑ z, L i v (expose D v x y) z *
      if z = mask (W i) v u then 1 else 0) = _
    simp [mul_ite]

/-- Expanding the direct sum and acting on the shared-label
coordinates gives one independent sum of local products per summand. -/
theorem packet_of_restriction (D : E → S × S) (hd : ∀ e, (D e).1 ≠ (D e).2)
    (W : (i : I) → J i → S × S)
    (h : (∏ e, wire K (D e).1 (D e).2 2) ≤ ∑ i, ∏ e, wire K (W i e).1 (W i e).2 2) :
    Packet K D W := by
  apply packet_of_graph D hd W
  have eq {A : Type} [Fintype A] (P : A → S × S) :
      ofRaw (graph K P) = ∏ e, wire K (P e).1 (P e).2 2 := signals_prod P
  simpa only [eq] using h

end OAI.LinearAlgebra.MatrixExponent.Spectral.Tensor
end

/-! # Serial composition of exact wire packets -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Packet

open Classical Finset

variable {K S E X Y : Type} [Field K] [Fintype S] [Fintype E] [Fintype X] [Fintype Y]

private def fill (b : E → S) (v : S) (x : {e // b e = v} → Bool) (e : E) :=
  if h : b e = v then x ⟨e, h⟩ else false

private theorem contract (b : E → S) (f : S → (E → Bool) → K)
    (loc : ∀ v x y, (∀ e, b e = v → x e = y e) → f v x = f v y) :
    (∏ v, ∑ z, f v (fill b v z)) = ∑ z, ∏ v, f v z := by
  let e : (E → Bool) ≃ (∀ v, {j // b j = v} → Bool) :=
    ((Equiv.sigmaFiberEquiv b).symm.arrowCongr (Equiv.refl _)).trans
      (Equiv.piCurry fun v (_ : {j // b j = v}) => Bool)
  rw [Fintype.prod_sum, ← e.sum_comp]
  apply sum_congr rfl
  intro z _
  exact prod_congr rfl fun v _ => loc _ _ _ (fun i hi => by rw [fill, dite_eq_left hi]; rfl)

/-- Joining the last endpoint of each first demand to the first endpoint
of its successor requires no additional wires, even when sites coincide. -/
def Rule.series {a b c : E → S} {W : X → S × S} {U : Y → S × S}
    (hf : Rule K (fun e => (a e, b e)) (fun _ : Unit => W))
    (hg : Rule K (fun e => (b e, c e)) (fun _ : Unit => U)) :
    Rule K (fun e => (a e, c e)) (fun _ : Unit => Sum.elim W U) := by
  obtain ⟨f, lf, sf⟩ := hf
  obtain ⟨g, lg, sg⟩ := hg
  let L (x y : E → Bool) (u : X ⊕ Y → Bool) (v : S) (z : E → Bool) :=
    f () v x z (u ∘ Sum.inl) * g () v z y (u ∘ Sum.inr)
  have loc x y u v z z' (hz : ∀ e, b e = v → z e = z' e) : L x y u v z = L x y u v z' :=
    congrArg₂ (· * ·)
      (lf _ _ _ _ _ _ _ _ (fun _ _ => rfl) hz (fun _ _ => rfl))
      (lg _ _ _ _ _ _ _ _ hz (fun _ _ => rfl) (fun _ _ => rfl))
  refine ⟨fun _ v x y u => ∑ z, L x y u v (fill b v z), ?_, ?_⟩
  · intro _ v x y u x' y' u' hx hy hu
    refine sum_congr rfl fun z _ => congrArg₂ (· * ·) ?_ ?_
    · exact lf _ _ _ _ _ _ _ _ hx (fun _ _ => rfl) (fun e h => hu (.inl e) h)
    · exact lg _ _ _ _ _ _ _ _ (fun _ _ => rfl) hy (fun e h => hu (.inr e) h)
  · intro x y
    simp only [Fintype.sum_unique] at sf sg ⊢
    simp_rw [contract b _ (loc x y _)]
    rw [sum_comm]
    have expand (z : E → Bool) :
        (∑ u, ∏ v, L x y u v z) =
          (if x = z then (1 : K) else 0) * (if z = y then 1 else 0) := by
      rw [sf x z, sg z y, sum_mul_sum,
        ← (Equiv.sumArrowEquivProdArrow X Y Bool).symm.sum_comp, Fintype.sum_prod_type]
      apply sum_congr rfl
      intro u _
      apply sum_congr rfl
      intro w _
      rw [← prod_mul_distrib]
      rfl
    calc
      _ = ∑ z, (if x = z then (1 : K) else 0) * (if z = y then 1 else 0) := by simp
      _ = _ := by
        apply sum_congr rfl
        intro z _
        exact (expand z).symm.trans (sum_congr (by ext; simp) (fun _ _ => rfl))

/-- Several paths may share sites. Their wire variables remain distinct. -/
def Rule.path (K : Type) [Field K] (D : ℕ → E → S) (n : ℕ) :
    Rule K (fun e => (D 0 e, D n e))
      (fun _ : Unit => fun q : Fin n × E => (D q.1.val q.2, D (q.1.val + 1) q.2)) := by
  let left (x : E → Bool) (u : Fin n × E → Bool) : Fin (n + 1) → E → Bool :=
    Fin.cons x (Function.curry u)
  let right (y : E → Bool) (u : Fin n × E → Bool) : Fin (n + 1) → E → Bool :=
    Fin.snoc (Function.curry u) y
  let ok v x y u := ∀ (i : Fin (n + 1)) e, D i.val e = v → left x u i e = right y u i e
  refine ⟨fun _ v x y u => if ok v x y u then 1 else 0, ?_, ?_⟩
  · intro _ v x y u x' y' u' hx hy hu
    have hl (i : Fin (n + 1)) e (he : D i.val e = v) : left x u i e = left x' u' i e := by
      induction i using Fin.cases with
      | zero => exact hx e he
      | succ i => simpa [left] using hu (i, e) (.inr he)
    have hr (i : Fin (n + 1)) e (he : D i.val e = v) : right y u i e = right y' u' i e := by
      induction i using Fin.lastCases with
      | last => simpa [right] using hy e he
      | cast i => simpa [right] using hu (i, e) (.inl he)
    have he : ok v x y u ↔ ok v x' y' u' :=
      ⟨fun h i e hi => (hl i e hi).symm.trans ((h i e hi).trans (hr i e hi)),
       fun h i e hi => (hl i e hi).trans ((h i e hi).trans (hr i e hi).symm)⟩
    simp only [he]
  · intro x y
    let z (p : Fin n × E) := x p.2
    have unique (u : Fin n × E → Bool) (hu : ∀ v, ok v x y u) : x = y ∧ u = z := by
      have eq (i : Fin (n + 1)) e : left x u i e = right y u i e := hu _ i e rfl
      have same (i : Fin (n + 1)) e : left x u i e = x e := by
        induction i using Fin.induction with
        | zero => rfl
        | succ i ih => simpa [left, right] using (eq i.castSucc e).symm.trans ih
      constructor
      · funext e
        simpa [right] using ((same (Fin.last n) e).symm.trans (eq (Fin.last n) e))
      · funext ⟨i, e⟩
        simpa [left, z] using same i.succ e
    have zero (u : Fin n × E → Bool) (hu : ¬(x = y ∧ u = z)) :
        (∏ v, if ok v x y u then (1 : K) else 0) = 0 := by
      obtain ⟨v, hv⟩ := not_forall.mp (fun h => hu (unique u h))
      exact prod_eq_zero (mem_univ v) (ite_eq_right hv)
    simp only [Fintype.sum_unique]
    rw [sum_eq_single z]
    rotate_left
    · exact fun u _ hu => zero u (fun h => hu h.2)
    · simp
    by_cases he : x = y
    · subst y
      have hl (i : Fin (n + 1)) e : left x z i e = x e := by
        induction i using Fin.cases <;> simp [left, z]
      have hr (i : Fin (n + 1)) e : right x z i e = x e := by
        induction i using Fin.lastCases <;> simp [right, z]
      simp [ok, hl, hr]
    · rw [ite_eq_right he, zero z (fun h => he h.1)]

theorem series {a b c : E → S} {W : X → S × S} {U : Y → S × S}
    (hf : Packet K (fun e => (a e, b e)) (fun _ : Unit => W))
    (hg : Packet K (fun e => (b e, c e)) (fun _ : Unit => U)) :
    Packet K (fun e => (a e, c e)) (fun _ : Unit => Sum.elim W U) :=
  (Rule.series hf.rule hg.rule).packet

theorem path (K : Type) [Field K] (D : ℕ → E → S) (n : ℕ) :
    Packet K (fun e => (D 0 e, D n e))
      (fun _ : Unit => fun q : Fin n × E => (D q.1.val q.2, D (q.1.val + 1) q.2)) :=
  (Rule.path K D n).packet

end OAI.LinearAlgebra.MatrixExponent.Spectral.Packet
end

/-! # Reindexing a packet and keeping extra wires unchanged -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Packet

open Classical

variable {K S U E Z I : Type} {J : I → Type} [Field K]

/-- Disjoint union of two indexed families of directed edges. -/
def together (D : E → S × S) (L : Z → U × U) : E ⊕ Z → (S ⊕ U) × (S ⊕ U)
  | .inl e => (.inl (D e).1, .inl (D e).2)
  | .inr e => (.inr (L e).1, .inr (L e).2)

variable [Fintype Z]

def checkAt (K : Type) [Field K] (l : Z → U) (v : U) (x u : Z → Bool) : K :=
  if ∀ e, l e = v → x e = u e then 1 else 0

private theorem check_congr {l : Z → U} {v : U} {x y u w : Z → Bool}
    (hx : ∀ e, l e = v → x e = y e) (hu : ∀ e, l e = v → u e = w e) :
    checkAt K l v x u = checkAt K l v y w := by
  have he : (∀ e, l e = v → x e = u e) ↔ (∀ e, l e = v → y e = w e) := by
    constructor <;> intro h e hv
    · rw [← hx e hv, ← hu e hv, h e hv]
    · rw [hx e hv, hu e hv, h e hv]
  simp only [checkAt, he]

variable [Fintype U]

private theorem check_prod (l : Z → U) (x u : Z → Bool) :
    (∏ v, checkAt K l v x u) = if x = u then 1 else 0 := by
  by_cases h : x = u
  · simp [checkAt, h]
  obtain ⟨e, he⟩ := Function.ne_iff.mp h
  rw [ite_eq_right h]
  exact Finset.prod_eq_zero (Finset.mem_univ (l e)) (ite_eq_right (fun h => he (h e rfl)))

variable [Fintype S] [Fintype E] [Fintype I] [∀ i, Fintype (J i)]
  {D : E → S × S} {W : (i : I) → J i → S × S}

def Rule.reindex (h : Rule K D W) (e : Z ≃ E) : Rule K (D ∘ e) W := by
  let f := h.entry
  have hl := h.local'
  have hi := h.eval
  refine ⟨fun i v x y u => f i v (x ∘ e.symm) (y ∘ e.symm) u, ?_, ?_⟩
  · intro i v x y u x' y' u' hx hy hu
    exact hl i v _ _ _ _ _ _ (fun j hj => hx _ (by simpa using hj))
      (fun j hj => hy _ (by simpa using hj)) hu
  · intro x y
    have he : x ∘ e.symm = y ∘ e.symm ↔ x = y :=
      (e.arrowCongr (Equiv.refl Bool)).injective.eq_iff
    simpa only [he] using hi (x ∘ e.symm) (y ∘ e.symm)

theorem reindex (h : Packet K D W) (e : Z ≃ E) : Packet K (D ∘ e) W :=
  (h.rule.reindex e).packet

/-- Keeping a wire costs one additional supply bit and no selector. -/
def Rule.keep (h : Rule K D W) (L : Z → U × U) :
    Rule K (together D L) (fun i => together (W i) L) := by
  let f := h.entry
  have hl := h.local'
  have hi := h.eval
  let g (i : I) (v : S ⊕ U) (x y : E ⊕ Z → Bool) (u : J i ⊕ Z → Bool) :=
    Sum.elim (fun s => f i s (x ∘ Sum.inl) (y ∘ Sum.inl) (u ∘ Sum.inl))
      (fun s => checkAt K (fun e => (L e).1) s (x ∘ Sum.inr) (u ∘ Sum.inr) *
        checkAt K (fun e => (L e).2) s (y ∘ Sum.inr) (u ∘ Sum.inr)) v
  refine ⟨g, ?_, ?_⟩
  · intro i v x y u x' y' u' hx hy hu
    cases v with
    | inl s =>
      exact hl i s _ _ _ _ _ _ (fun e he => hx (.inl e) (congrArg Sum.inl he))
        (fun e he => hy (.inl e) (congrArg Sum.inl he))
        (fun e he => hu (.inl e) (he.imp (congrArg Sum.inl) (congrArg Sum.inl)))
    | inr s =>
      apply congrArg₂ (· * ·)
      · exact check_congr (fun e he => hx (.inr e) (congrArg Sum.inr he))
          (fun e he => hu (.inr e) (.inl (congrArg Sum.inr he)))
      · exact check_congr (fun e he => hy (.inr e) (congrArg Sum.inr he))
          (fun e he => hu (.inr e) (.inr (congrArg Sum.inr he)))
  · intro x y
    have he : x = y ↔ x ∘ Sum.inl = y ∘ Sum.inl ∧ x ∘ Sum.inr = y ∘ Sum.inr :=
      (Equiv.sumArrowEquivProdArrow E Z Bool).injective.eq_iff.symm.trans Prod.ext_iff
    have delta : (if x = y then (1 : K) else 0) =
        (if x ∘ Sum.inl = y ∘ Sum.inl then 1 else 0) *
        (if x ∘ Sum.inr = y ∘ Sum.inr then 1 else 0) := by
      simp only [he, ite_and, ite_mul, one_mul, zero_mul]
    rw [delta, hi, Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    let : DecidableEq (J i ⊕ Z) := Classical.decEq _
    rw [← (Equiv.sumArrowEquivProdArrow (J i) Z Bool).symm.sum_comp, Fintype.sum_prod_type,
      Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro u _
    simp only [Fintype.prod_sum_type, g, Sum.elim_inl, Sum.elim_inr, Finset.prod_mul_distrib,
      check_prod]
    change _ = ∑ w : Z → Bool, (∏ s, f i s (x ∘ Sum.inl) (y ∘ Sum.inl) u) *
      ((if x ∘ Sum.inr = w then 1 else 0) * (if y ∘ Sum.inr = w then 1 else 0))
    simp only [f, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, ite_true]

theorem keep (h : Packet K D W) (L : Z → U × U) :
    Packet K (together D L) (fun i => together (W i) L) :=
  (h.rule.keep L).packet

def Rule.supplies_equiv {C : I → Type} [∀ i, Fintype (C i)]
    (h : Rule K D W) (e : ∀ i, C i ≃ J i) :
    Rule K D (fun i => W i ∘ e i) := by
  let f := h.entry
  have loc := h.local'
  have eval := h.eval
  refine ⟨fun i v x y z => f i v x y (z ∘ (e i).symm), ?_, ?_⟩
  · intro i v x y z x' y' z' hx hy hz
    exact loc i v _ _ _ _ _ _ hx hy (fun b hb => hz ((e i).symm b) (by simpa using hb))
  · intro x y
    rw [eval]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← ((e i).arrowCongr (Equiv.refl Bool)).sum_comp]
    rfl

theorem supplies_equiv {C : I → Type} [∀ i, Fintype (C i)]
    (h : Packet K D W) (e : ∀ i, C i ≃ J i) :
    Packet K D (fun i => W i ∘ e i) :=
  (h.rule.supplies_equiv e).packet

end OAI.LinearAlgebra.MatrixExponent.Spectral.Packet
end

/-! # Parallel composition and placement of wire packets -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Packet

open Classical

variable {K : Type} [Field K]

/-- Identify sites along an arbitrary map, multiplying the tables in each fiber. -/
def Rule.place {S U E I : Type} {J : I → Type}
    [Fintype S] [Fintype U] [Fintype E] [Fintype I] [∀ i, Fintype (J i)]
    {D : E → S × S} {W : (i : I) → J i → S × S}
    (h : Rule K D W) (g : S → U) :
    Rule K (fun e => (g (D e).1, g (D e).2)) (fun i e => (g (W i e).1, g (W i e).2)) := by
  obtain ⟨f, hloc, hid⟩ := h
  refine ⟨fun i v x y u => ∏ w ∈ Finset.univ.filter (fun w => g w = v), f i w x y u, ?_, ?_⟩
  · intro i v x y u x' y' u' hx hy hu
    apply Finset.prod_congr rfl
    intro w hw
    have he := (Finset.mem_filter.mp hw).2
    exact hloc i w _ _ _ _ _ _
      (fun e h => hx e ((congrArg g h).trans he))
      (fun e h => hy e ((congrArg g h).trans he))
      (fun e h => hu e (h.imp (fun h => (congrArg g h).trans he) (fun h => (congrArg g h).trans he)))
  · intro x y
    rw [hid x y]
    apply Finset.sum_congr rfl
    intro i _
    apply Finset.sum_congr rfl
    intro u _
    exact (Finset.prod_fiberwise Finset.univ g (fun v => f i v x y u)).symm

theorem place {S U E I : Type} {J : I → Type}
    [Fintype S] [Fintype U] [Fintype E] [Fintype I] [∀ i, Fintype (J i)]
    {D : E → S × S} {W : (i : I) → J i → S × S}
    (h : Packet K D W) (g : S → U) :
    Packet K (fun e => (g (D e).1, g (D e).2)) (fun i e => (g (W i e).1, g (W i e).2)) :=
  (h.rule.place g).packet

variable {A : Type} {S E I : A → Type} {J : (a : A) → I a → Type}

/-- Demand legs keep their component labels. -/
def parallelDemand (D : (a : A) → E a → S a × S a) (e : Sigma E) : Sigma S × Sigma S :=
  (⟨e.1, (D e.1 e.2).1⟩, ⟨e.1, (D e.1 e.2).2⟩)

/-- Each component activates its own supply according to its own selector. -/
def parallelSupply (W : (a : A) → (i : I a) → J a i → S a × S a)
    (i : ∀ a, I a) (e : Sigma (fun a => J a (i a))) : Sigma S × Sigma S :=
  parallelDemand (fun a => W a (i a)) e

private def parts (E : A → Type) : (Sigma E → Bool) ≃ ((a : A) → E a → Bool) where
  toFun x a e := x ⟨a, e⟩
  invFun x e := x e.1 e.2
  left_inv _ := rfl
  right_inv _ := rfl

variable [Fintype A] [DecidableEq A] [∀ a, Fintype (S a)] [∀ a, Fintype (E a)]
  [∀ a, Fintype (I a)] [∀ a i, Fintype (J a i)]

/-- The selector set is a Cartesian product. Assignments to different
components remain independent even when their endpoints coincide. -/
def Rule.parallel {D : (a : A) → E a → S a × S a}
    {W : (a : A) → (i : I a) → J a i → S a × S a}
    (h : ∀ a, Rule K (D a) (W a)) : Rule K (parallelDemand D) (parallelSupply W) := by
  let f a := (h a).entry
  have hloc a := (h a).local'
  have hid a := (h a).eval
  refine ⟨fun i v x y u =>
    f v.1 (i v.1) v.2 (parts E x v.1) (parts E y v.1) (parts _ u v.1), ?_, ?_⟩
  · rintro i ⟨a, v⟩ x y u x' y' u' hx hy hu
    apply hloc
    · intro e he
      exact hx ⟨a, e⟩ (congrArg (Sigma.mk a) he)
    · intro e he
      exact hy ⟨a, e⟩ (congrArg (Sigma.mk a) he)
    · intro e he
      exact hu ⟨a, e⟩ (he.imp (congrArg (Sigma.mk a)) (congrArg (Sigma.mk a)))
  · intro x y
    have delta : (if x = y then (1 : K) else 0) =
        ∏ a, if parts E x a = parts E y a then 1 else 0 := by
      by_cases he : x = y
      · simp [he]
      · rw [ite_eq_right he]
        obtain ⟨a, ha⟩ := Function.ne_iff.mp ((parts E).injective.ne he)
        exact (Finset.prod_eq_zero (Finset.mem_univ a) (ite_eq_right ha)).symm
    rw [delta]
    simp_rw [hid]
    rw [Fintype.prod_sum]
    apply Finset.sum_congr rfl
    intro i _
    rw [Fintype.prod_sum, ← (parts (fun a => J a (i a))).sum_comp]
    refine Finset.sum_congr (by ext; simp) ?_
    intro u _
    rw [Fintype.prod_sigma]

theorem parallel {D : (a : A) → E a → S a × S a}
    {W : (a : A) → (i : I a) → J a i → S a × S a}
    (h : ∀ a, Packet K (D a) (W a)) : Packet K (parallelDemand D) (parallelSupply W) :=
  (Rule.parallel (fun a => (h a).rule)).packet

end OAI.LinearAlgebra.MatrixExponent.Spectral.Packet
end

/-! # Selecting and deploying exact wire packets -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Packet
open scoped Classical

variable {F S A B I : Type} [Field F] [Fintype S] [Fintype A] [Fintype B] [Fintype I]
  {J : I → Type} [∀ i, Fintype (J i)] {D : A → S × S} {W : (i : I) → J i → S × S}

/-- Pin both ends of each unused demand to zero. -/
def Rule.select (h : Rule F D W) (e : B ↪ A) : Rule F (fun a => D (e a)) W := by
  let fill (x : B → Bool) (a : A) := if ha : ∃ b, e b = a then x ha.choose else false
  have read (x : B → Bool) (b : B) : fill x (e b) = x b := by
    have hh : ∃ c, e c = e b := ⟨b, rfl⟩
    simp only [fill, dite_eq_left hh, e.injective hh.choose_spec]
  have inj : Function.Injective fill := by
    intro x y eq
    funext b
    simpa only [read] using congrFun eq (e b)
  have same (x y : B → Bool) (a : A) (hx : ∀ b, e b = a → x b = y b) :
      fill x a = fill y a := by
    unfold fill
    split
    · rename_i ha
      exact hx _ ha.choose_spec
    · rfl
  obtain ⟨f, loc, eval⟩ := h
  refine ⟨fun i v x y => f i v (fill x) (fill y), ?_, ?_⟩
  · intro i v x y u x' y' u' hx hy hu
    exact loc i v _ _ _ _ _ _
      (fun a ha => same _ _ _ (fun b hb => hx b (by simp only [hb, ha])))
      (fun a ha => same _ _ _ (fun b hb => hy b (by simp only [hb, ha]))) hu
  · intro x y
    simpa only [inj.eq_iff] using eval (fill x) (fill y)

/-- Parallel one-term packets need no selector. -/
def Rule.parallel_one {S E J : A → Type} [∀ a, Fintype (S a)]
    [∀ a, Fintype (E a)] [∀ a, Fintype (J a)]
    {D : (a : A) → E a → S a × S a} {W : (a : A) → J a → S a × S a}
    (h : ∀ a, Rule F (D a) (fun _ : Unit => W a)) :
    Rule F (parallelDemand D) (fun _ : Unit => parallelDemand W) := by
  obtain ⟨f, loc, eval⟩ := Rule.parallel h
  refine ⟨fun _ => f default, fun _ => loc default, fun x y => ?_⟩
  simpa only [Fintype.sum_unique] using eval x y

/-- Exchange the two endpoints of every demand. -/
def Rule.reverse (h : Rule F D W) : Rule F (fun a => ((D a).2, (D a).1)) W := by
  obtain ⟨f, loc, eval⟩ := h
  exact ⟨fun i v x y => f i v y x,
    fun i v _ _ _ _ _ _ hx hy hu => loc i v _ _ _ _ _ _ hy hx hu,
    fun x y => by simpa only [eq_comm (a := y)] using eval y x⟩

/-- Join the two output legs of a pair of demands by one new supply
wire. The input legs become the endpoints of a single demand. -/
def Rule.join_outputs {a b : A × Bool → S} {W : B → S × S}
    (h : Rule F (fun e => (a e, b e)) (fun _ : Unit => W)) :
    Rule F (fun e => (a (e, false), a (e, true)))
      (fun _ : Unit => Sum.elim W (fun e => (b (e, false), b (e, true)))) := by
  obtain ⟨f, loc, eval⟩ := h
  let pair (x y : A → Bool) (q : A × Bool) := if q.2 then y q.1 else x q.1
  have eq (x y z : A → Bool) : pair x y = z ∘ Prod.fst ↔ x = z ∧ y = z := by
    refine ⟨fun he => ⟨funext fun e => congrFun he (e, false), funext fun e => congrFun he (e, true)⟩, ?_⟩
    rintro ⟨rfl, rfl⟩
    funext ⟨e, t⟩
    cases t <;> rfl
  refine ⟨fun _ v x y z => f () v (pair x y) (fun e => z (.inr e.1)) (z ∘ Sum.inl), ?_, ?_⟩
  · intro _ v x y z x' y' z' hx hy hz
    apply loc
    · rintro ⟨e, _|_⟩ he
      · exact hx _ he
      · exact hy _ he
    · rintro ⟨e, _|_⟩ he
      · exact hz (.inr e) (.inl he)
      · exact hz (.inr e) (.inr he)
    · exact fun e he => hz (.inl e) he
  · intro x y
    simp only [Fintype.sum_unique]
    trans ∑ z : B ⊕ A → Bool, ∏ v, f () v (pair x y) (fun e => z (.inr e.1)) (z ∘ Sum.inl)
    swap
    · exact Finset.sum_congr (by ext; simp) (fun _ _ => rfl)
    rw [← (Equiv.sumArrowEquivProdArrow B A Bool).symm.sum_comp,
      Fintype.sum_prod_type, Finset.sum_comm]
    change _ = ∑ z : A → Bool, ∑ u : B → Bool, ∏ v, f () v (pair x y) (z ∘ Prod.fst) u
    simp only [Fintype.sum_unique] at eval
    simp_rw [← eval, eq, ite_and]
    simp [eq_comm]

/-- Reindex the supply of a one-term packet. -/
def Rule.supply_equiv {C : Type} [Fintype C] {W : B → S × S}
    (h : Rule F D (fun _ : Unit => W)) (e : C ≃ B) :
    Rule F D (fun _ : Unit => W ∘ e) :=
  h.supplies_equiv (fun _ => e)

/-- Replace each single-bit wire by a bundle of independent bits. -/
def Rule.bundle {W : B → S × S} (h : Rule F D (fun _ : Unit => W)) (b : ℕ) :
    Rule F (fun a : A × Fin b => D a.1) (fun _ : Unit => fun z : B × Fin b => W z.1) := by
  let read (C : Type) (x : C × Fin b → Bool) (i : Fin b) (j : C) := x (j, i)
  refine ⟨fun _ v x y u => ∏ i : Fin b, h.entry () v (read _ x i) (read _ y i) (read _ u i),
    ?_, ?_⟩
  · intro _ v x y u x' y' u' hx hy hu
    apply Finset.prod_congr rfl
    exact fun i _ => h.local' _ _ _ _ _ _ _ _
      (fun t ht => hx (t, i) ht) (fun t ht => hy (t, i) ht) (fun t ht => hu (t, i) ht)
  · intro x y
    let e : (B × Fin b → Bool) ≃ (Fin b → B → Bool) :=
      ((Equiv.prodComm _ _).arrowCongr (.refl _)).trans (Equiv.curry _ _ _)
    have delta : (if x = y then (1 : F) else 0) =
        ∏ i, if read _ x i = read _ y i then (1 : F) else 0 := by
      by_cases he : x = y
      · simp [he]
      · rw [ite_eq_right he]
        obtain ⟨⟨t, i⟩, hi⟩ := Function.ne_iff.mp he
        symm
        exact Finset.prod_eq_zero (Finset.mem_univ i) (ite_eq_right (fun he => hi (congrFun he t)))
    simp only [Fintype.sum_unique]
    rw [delta]
    simp_rw [h.eval, Fintype.sum_unique]
    rw [Fintype.prod_sum, ← e.sum_comp]
    refine Finset.sum_congr (by ext; simp) (fun z _ => ?_)
    rw [Finset.prod_comm]
    rfl

theorem select (h : Packet F D W) (e : B ↪ A) : Packet F (fun a => D (e a)) W :=
  (Rule.select h.rule e).packet

theorem parallel_one {S E J : A → Type} [∀ a, Fintype (S a)]
    [∀ a, Fintype (E a)] [∀ a, Fintype (J a)]
    {D : (a : A) → E a → S a × S a} {W : (a : A) → J a → S a × S a}
    (h : ∀ a, Packet F (D a) (fun _ : Unit => W a)) :
    Packet F (parallelDemand D) (fun _ : Unit => parallelDemand W) :=
  (Rule.parallel_one (fun i => (h i).rule)).packet

theorem reverse (h : Packet F D W) : Packet F (fun a => ((D a).2, (D a).1)) W :=
  (Rule.reverse h.rule).packet

theorem join_outputs {a b : A × Bool → S} {W : B → S × S}
    (h : Packet F (fun e => (a e, b e)) (fun _ : Unit => W)) :
    Packet F (fun e => (a (e, false), a (e, true)))
      (fun _ : Unit => Sum.elim W (fun e => (b (e, false), b (e, true)))) :=
  (Rule.join_outputs h.rule).packet

theorem supply_equiv {C : Type} [Fintype C] {W : B → S × S}
    (h : Packet F D (fun _ : Unit => W)) (e : C ≃ B) :
    Packet F D (fun _ : Unit => W ∘ e) :=
  (Rule.supply_equiv h.rule e).packet

theorem bundle {W : B → S × S} (h : Packet F D (fun _ : Unit => W)) (b : ℕ) :
    Packet F (fun a : A × Fin b => D a.1) (fun _ : Unit => fun z : B × Fin b => W z.1) :=
  (Rule.bundle h.rule b).packet

end OAI.LinearAlgebra.MatrixExponent.Spectral.Packet
end

/-! # A wire packet from a partition of its demands -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Packet
open Classical Finset

variable {K S E X Y : Type} [Field K] [Fintype S] [Fintype E] [Fintype X] [Fintype Y]

/-- Independent supply bits serve the selected demands and their complement. -/
def Rule.partition (G : E → Prop) [DecidablePred G]
    (D : E → S × S) {W : X → S × S} {U : Y → S × S}
    (hf : Rule K (fun e : {i // G i} => D e.1) (fun _ : Unit => W))
    (hg : Rule K (fun e : {i // ¬ G i} => D e.1) (fun _ : Unit => U)) :
    Rule K D (fun _ : Unit => Sum.elim W U) := by
  obtain ⟨f, lf, sf⟩ := hf
  obtain ⟨g, lg, sg⟩ := hg
  let lo (x : E → Bool) (i : {i // G i}) := x i
  let hi (x : E → Bool) (i : {i // ¬G i}) := x i
  refine ⟨fun _ v x y u => f () v (lo x) (lo y) (u ∘ Sum.inl) *
    g () v (hi x) (hi y) (u ∘ Sum.inr), ?_, ?_⟩
  · intro _ v x y u x' y' u' hx hy hu
    refine congrArg₂ (· * ·) ?_ ?_
    · exact lf _ _ _ _ _ _ _ _ (fun e h => hx e.1 h) (fun e h => hy e.1 h) (fun e h => hu (.inl e) h)
    · exact lg _ _ _ _ _ _ _ _ (fun e h => hx e.1 h) (fun e h => hy e.1 h) (fun e h => hu (.inr e) h)
  · intro x y
    have eq : x = y ↔ lo x = lo y ∧ hi x = hi y := by
      refine ⟨fun h => ⟨congrArg lo h, congrArg hi h⟩, ?_⟩
      rintro ⟨hl, hr⟩
      funext e
      by_cases he : G e
      · exact congrFun hl ⟨e, he⟩
      · exact congrFun hr ⟨e, he⟩
    have delta : (if x = y then (1 : K) else 0) =
        (if lo x = lo y then (1 : K) else 0) * (if hi x = hi y then (1 : K) else 0) := by
      simp only [eq, ite_and, ite_mul, one_mul, zero_mul]
    simp only [Fintype.sum_unique] at sf sg ⊢
    rw [delta, sf, sg, sum_mul_sum]
    let H (z : X ⊕ Y → Bool) := ∏ v, f () v (lo x) (lo y) (z ∘ Sum.inl) *
      g () v (hi x) (hi y) (z ∘ Sum.inr)
    trans ∑ z, H z
    swap
    · exact sum_congr (by ext; simp) (fun _ _ => rfl)
    rw [← (Equiv.sumArrowEquivProdArrow X Y Bool).symm.sum_comp, Fintype.sum_prod_type]
    apply sum_congr rfl
    intro u _
    apply sum_congr rfl
    intro w _
    rw [← prod_mul_distrib]
    rfl

theorem partition (G : E → Prop) [DecidablePred G]
    (D : E → S × S) {W : X → S × S} {U : Y → S × S}
    (hf : Packet K (fun e : {i // G i} => D e.1) (fun _ : Unit => W))
    (hg : Packet K (fun e : {i // ¬ G i} => D e.1) (fun _ : Unit => U)) :
    Packet K D (fun _ : Unit => Sum.elim W U) :=
  (Rule.partition G D hf.rule hg.rule).packet

end OAI.LinearAlgebra.MatrixExponent.Spectral.Packet
end

/-! # Orientation of individual wire demands -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Spectral.Packet
open scoped Classical

variable {F S E I : Type} [Field F] [Fintype S] [Fintype E] [Fintype I]
  {J : I → Type} [∀ i, Fintype (J i)] {D : E → S × S} {W : (i : I) → J i → S × S}

/-- A demand is an equality test, so its two legs can be exchanged. -/
theorem orient (h : Packet F D W) (t : E → Bool) :
    Packet F (fun e => if t e then (D e).swap else D e) W := by
  obtain ⟨f, loc, eval⟩ := h
  let p (x y : E → Bool) (e : E) := if t e then y e else x e
  have eq (x y : E → Bool) : p x y = p y x ↔ x = y := by
    refine ⟨fun he => funext fun e => ?_, fun he => by rw [he]⟩
    have := congrFun he e
    cases ht : t e
    · simpa only [p, ht, Bool.false_eq_true, ite_false] using this
    · simpa only [p, ht, ite_true] using this.symm
  refine ⟨fun i v x y => f i v (p x y) (p y x), ?_, fun x y => ?_⟩
  · intro i v x y u x' y' u' hx hy hu
    refine loc i v _ _ _ _ _ _ ?_ ?_ hu
    · intro e he
      cases ht : t e
      · simpa [p, ht] using hx e (by simp [ht, he])
      · simpa [p, ht] using hy e (by simp [ht, he])
    · intro e he
      cases ht : t e
      · simpa [p, ht] using hy e (by simp [ht, he])
      · simpa [p, ht] using hx e (by simp [ht, he])
  · simpa only [eq] using eval (p x y) (p y x)

end OAI.LinearAlgebra.MatrixExponent.Spectral.Packet
end
