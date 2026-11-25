import OAI.LinearAlgebra.MatrixExponent.Protocol.Alignment
import OAI.LinearAlgebra.MatrixExponent.Protocol.Focus
import OAI.LinearAlgebra.MatrixExponent.Protocol.Replay

/-! # Commuting local reindexings of inventories -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol.Board

variable {K S T : Type} {s : S} {t : T} {D D' D'' : Board K S} {V V' V'' : Board K T}

def Square (a : Rename D D') (b : Rename V V')
    (e : D.localPort s ≃ V.localPort t) (f : D'.localPort s ≃ V'.localPort t) : Prop :=
  ∀ u, f (a.local s u) = b.local t (e u)

namespace Square

variable {a : Rename D D'} {b : Rename V V'}
  {e : D.localPort s ≃ V.localPort t} {f : D'.localPort s ≃ V'.localPort t}

theorem refl (e : D.localPort s ≃ V.localPort t) : Square (.refl D) (.refl V) e e :=
  fun _ => rfl

theorem trans {a' : Rename D' D''} {b' : Rename V' V''} {g : D''.localPort s ≃ V''.localPort t}
    (h : Square a b e f) (k : Square a' b' f g) : Square (a.trans a') (b.trans b') e g :=
  fun i => (k (a.local s i)).trans (congrArg (b'.local t) (h i))

theorem symm (h : Square a b e f) : Square a.symm b.symm f e := by
  intro i
  have he : a.local s (a.symm.local s i) = i := Subtype.ext (a.eqv.apply_symm_apply _)
  have hh := h (a.symm.local s i)
  rw [he] at hh
  exact Subtype.ext (b.eqv.eq_symm_apply.mpr (congrArg Subtype.val hh.symm))

variable [Field K]

theorem join {A A' : Board K S} {B B' : Board K T}
    {c : Rename A A'} {d : Rename B B'}
    {g : A.localPort s ≃ B.localPort t} {l : A'.localPort s ≃ B'.localPort t}
    (h : Square a b e f) (k : Square c d g l) :
    Square (a.join c) (b.join d) (joinPorts e g) (joinPorts f l) := by
  rintro ⟨i | i, hi⟩
  · exact congrArg (V'.joinLeft B' t) (h ⟨i, hi⟩)
  · exact congrArg (V'.joinRight B' t) (k ⟨i, hi⟩)

theorem swap (e : D.localPort s ≃ V.localPort t) (f : D'.localPort s ≃ V'.localPort t) :
    Square (D.swap D') (V.swap V') (joinPorts e f) (joinPorts f e) := by
  rintro ⟨i | i, hi⟩ <;> rfl

theorem rotate (e : D.localPort s ≃ V.localPort t) (f : D'.localPort s ≃ V'.localPort t)
    (g : D''.localPort s ≃ V''.localPort t) :
    Square (D.rotate D' D'') (V.rotate V' V'') (joinPorts (joinPorts e f) g)
      (joinPorts (joinPorts g e) f) := by
  rintro ⟨(i|i)|i, hi⟩ <;> rfl

variable {I J : Type} [Fintype I] [Fintype J] {U : I → Board K S} {W : J → Board K T}
  {z y : I → ℕ} {z' y' : J → ℕ} (p : Pin U s ≃ Pin W t)

theorem orders_eq (h : z = y) (k : z' = y') (hz : Pin.Same p z z') (hy : Pin.Same p y y') :
    Square (Board.orders_eq U h) (Board.orders_eq W k) (Pin.lift p hz) (Pin.lift p hy) := by
  subst y
  subst y'
  rintro i
  obtain ⟨j, a, rfl⟩ := Pin.exists_atCopy i
  rfl

private theorem add_left (i : Pin U s) (v : Fin (z i.1)) :
    (Board.orders_add U z y).symm.local s ((orders U z).joinLeft (orders U y) s (i.atCopy v)) =
      i.atCopy (z := z + y) (Fin.castAdd (y i.1) v) := by
  apply Subtype.ext
  exact orders_add_left U z y _ _ _

private theorem add_right (i : Pin U s) (v : Fin (y i.1)) :
    (Board.orders_add U z y).symm.local s ((orders U z).joinRight (orders U y) s (i.atCopy v)) =
      i.atCopy (z := z + y) (Fin.natAdd (z i.1) v) := by
  apply Subtype.ext
  exact orders_add_right U z y _ _ _

theorem orders_add (hz : Pin.Same p z z') (hy : Pin.Same p y y') :
    Square (Board.orders_add U z y).symm (Board.orders_add W z' y').symm
      (joinPorts (Pin.lift p hz) (Pin.lift p hy))
      (Pin.lift p (fun i => congrArg₂ (· + ·) (hz i) (hy i))) := by
  intro u
  have cases' : (∃ v, (orders U z).joinLeft (orders U y) s v = u) ∨
      (∃ v, (orders U z).joinRight (orders U y) s v = u) := by
    obtain ⟨i | i, hi⟩ := u
    · exact .inl ⟨⟨i, hi⟩, rfl⟩
    · exact .inr ⟨⟨i, hi⟩, rfl⟩
  rcases cases' with ⟨v, rfl⟩ | ⟨v, rfl⟩ <;> obtain ⟨j, a, rfl⟩ := Pin.exists_atCopy v
  · rw [joinPorts_left, Pin.lift_atCopy, add_left, add_left]
    rfl
  · rw [joinPorts_right, Pin.lift_atCopy, add_right, add_right]
    change Pin.atCopy (z := z' + y') (p j) (Fin.cast (congrArg₂ (· + ·) (hz j) (hy j)) (Fin.natAdd (z j.1) a)) = _
    apply congrArg (Pin.atCopy (z := z' + y') (p j))
    exact Fin.ext (congrArg (· + a.val) (hz j))

end Square
end OAI.LinearAlgebra.MatrixExponent.Protocol.Board
end

/-! # Corresponding branches of two inventory schedules at one site -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Routing

variable {K S S' I I' E E' : Type} [Field K]
  [Fintype S] [Fintype S'] [Fintype I] [Fintype I'] [Fintype E] [Fintype E']
  {T : I → Board K S} {T' : I' → Board K S'} {V : E → Board K S} {V' : E' → Board K S'}
  {s : S} {s' : S'}

structure MoveRel (e : Pin T s ≃ Pin T' s') (f : Pin V s ≃ Pin V' s')
    {q : Intervention I E} {q' : Intervention I' E'}
    (r : Executes T V q) (r' : Executes T' V' q') (j : q.choice) (j' : q'.choice) : Prop where
  take : Pin.Same e q.take q'.take
  put : Pin.Same e (q.put j) (q'.put j')
  core : Pin.Same f (q.core j) (q'.core j')
  rel : Frame.Rel (Pin.lift e take) (Board.joinPorts (Pin.lift e put) (Pin.lift f core))
    (r.kernel j s) (r'.kernel j' s')

variable [DecidableEq I] [DecidableEq I']
  {Q : (I → ℕ) → Intervention I E} {Q' : (I' → ℕ) → Intervention I' E'}
  {Y : I → E → ℕ} {Y' : I' → E' → ℕ}

def RunRel (e : Pin T s ≃ Pin T' s') (f : Pin V s ≃ Pin V' s')
    (close : Settlement T V Y) (close' : Settlement T' V' Y')
    (run : ∀ z, Executes T V (Q z)) (run' : ∀ z, Executes T' V' (Q' z))
    {L : Finset I} {L' : Finset I'} :
    (k : ℕ) → {z : I → ℕ} → {z' : I' → ℕ} → Branch L Q k z → Branch L' Q' k z' → Prop
  | 0, z, z', p, p' =>
    ∃ hw : Pin.Same f (edges L Q Y 0 z p) (edges L' Q' Y' 0 z' p'),
      ∀ hz : Pin.Same e z z', Frame.Rel (Pin.lift e hz) (Pin.lift f hw)
        ((close z).kernel () s) ((close' z').kernel () s')
  | k + 1, z, z', p, p' =>
    MoveRel e f (run z) (run' z') p.1 p'.1 ∧
      RunRel e f close close' run run' (L := L) (L' := L') k p.2 p'.2

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-!
# Transporting an execution between corresponding local coordinates

The unchanged inventory and the newly installed links are reindexed
separately. Every local ordinal is preserved, even when the global
sets of labels, sites and possible branches differ.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Routing Board

variable {K S S' I I' E E' : Type} [Field K]
  [Fintype S] [Fintype S'] [Fintype I] [Fintype I'] [Fintype E] [Fintype E']
  {T : I → Board K S} {T' : I' → Board K S'} {V : E → Board K S} {V' : E' → Board K S'}
  {s : S} {s' : S'} {e : Pin T s ≃ Pin T' s'} {f : Pin V s ≃ Pin V' s'}
  {q : Intervention I E} {q' : Intervention I' E'}
  {r : Executes T V q} {r' : Executes T' V' q'} {j : q.choice} {j' : q'.choice}
  {z : I → ℕ} {z' : I' → ℕ}

omit [Field K] [Fintype S] [Fintype S'] [Fintype I] [Fintype I'] in
theorem Pin.Same.add {u : I → ℕ} {u' : I' → ℕ}
    (h : Pin.Same e z z') (k : Pin.Same e u u') : Pin.Same e (z + u) (z' + u') :=
  fun i => congrArg₂ (· + ·) (h i) (k i)

theorem MoveRel.next (h : MoveRel e f r r' j j') (hz : Pin.Same e z z') :
    Pin.Same e (q.next z j) (q'.next z' j') :=
  fun i => congrArg₂ (· + ·) (congrArg₂ (· - ·) (hz i) (h.take i)) (h.put i)

theorem MoveRel.takeStep (h : MoveRel e f r r' j j') (hz : Pin.Same e z z')
    (ht : q.take ≤ z) (ht' : q'.take ≤ z') :
    Frame.Rel (Pin.lift e hz) (joinPorts (Pin.lift e (h.next hz)) (Pin.lift f h.core))
      ((r.takeStep z ht).kernel j s) ((r'.takeStep z' ht').kernel j' s') := by
  let w := z - q.take
  let w' := z' - q'.take
  have hw : Pin.Same e w w' := fun i => congrArg₂ (· - ·) (hz i) (h.take i)
  have h₁ : q.take + w = z := funext fun i => Nat.add_sub_of_le (ht i)
  have h₂ : q'.take + w' = z' := funext fun i => Nat.add_sub_of_le (ht' i)
  have inp := (Square.orders_add e h.take hw).trans (Square.orders_eq e h₁ h₂ (h.take.add hw) hz)
  have out := (Square.rotate (Pin.lift e h.put) (Pin.lift f h.core) (Pin.lift e hw)).trans
    ((Square.orders_add e hw h.put).join (Square.refl (Pin.lift f h.core)))
  exact (Kernel.keep_rel h.rel (Pin.lift e hw)).pull inp out

variable [DecidableEq I] [DecidableEq I']
  {Q : (I → ℕ) → Intervention I E} {Q' : (I' → ℕ) → Intervention I' E'}
  {Y : I → E → ℕ} {Y' : I' → E' → ℕ}
  {L : Finset I} {L' : Finset I'}
  {close : Settlement T V Y} {close' : Settlement T' V' Y'}
  {run : ∀ z, Executes T V (Q z)} {run' : ∀ z, Executes T' V' (Q' z)}
  {a : I → ℝ} {a' : I' → ℝ} {w w' v v' : ℝ} {k : ℕ}

omit [Fintype I] [Fintype E] in
private theorem carry (q : Intervention I E) (ht : q.take ≤ z) (j : q.choice) (L : Finset I) (k : ℕ) :
    q.next z j + Stock.copies L 1 + Stock.copies L k = q.next (z + Stock.copies L (k + 1)) j := by
  funext i
  have hh : q.take i ≤ z i := ht i
  by_cases h : i ∈ L <;> simp [Intervention.next, Stock.copies, h]
  omega

theorem execute_rel (h : Runs L a Q w k z v) (h' : Runs L' a' Q' w' k z' v')
    (hL : ∀ n, Pin.Same e (Stock.copies L n) (Stock.copies L' n)) (hz : Pin.Same e z z')
    {p : Branch L Q k z} {p' : Branch L' Q' k z'}
    (hr : RunRel e f close close' run run' k p p') :
    ∃ hw : Pin.Same f (edges L Q Y k z p) (edges L' Q' Y' k z' p'),
      Frame.Rel (Pin.lift e (hz.add (hL k))) (Pin.lift f hw)
        ((execute T V L Q Y close run k z v h).kernel p s)
        ((execute T' V' L' Q' Y' close' run' k z' v' h').kernel p' s') := by
  induction k generalizing z z' v v' with
  | zero =>
    obtain ⟨hw, hk⟩ := hr
    have ha : z = z + Stock.copies L 0 := by ext; simp [Stock.copies]
    have hb : z' = z' + Stock.copies L' 0 := by ext; simp [Stock.copies]
    refine ⟨hw, ?_⟩
    rw [execute, execute]
    exact (hk hz).pull (Square.orders_eq e ha hb hz (hz.add (hL 0))) (Square.refl (Pin.lift f hw))
  | succ k ih =>
    obtain ⟨hs, hrest⟩ := hr
    have hn := (hs.next hz).add (hL 1)
    obtain ⟨hw, hk⟩ := ih (h.2 p.1) (h'.2 p'.1) hn hrest
    have first := hs.takeStep (hz.add (hL (k + 1)))
      (fun i => (h.1 i).trans (Nat.le_add_right ..))
      (fun i => (h'.1 i).trans (Nat.le_add_right ..))
    have hkeep := Kernel.keep_rel hk (Pin.lift f hs.core)
    have inp := (Square.orders_eq e (carry _ h.1 p.1 L k) (carry _ h'.1 p'.1 L' k)
      (hn.add (hL k)) (hs.next (hz.add (hL (k + 1))))).join (Square.refl (Pin.lift f hs.core))
    have out := (Square.swap (Pin.lift f hw) (Pin.lift f hs.core)).trans
      (Square.orders_add f hs.core hw)
    refine ⟨hs.core.add hw, ?_⟩
    classical
    rw [execute, execute]
    exact first.compose (hkeep.pull inp out)

theorem execute_start_rel (h : Runs L a Q w k 0 0) (h' : Runs L' a' Q' w' k 0 0)
    (hL : ∀ n, Pin.Same e (Stock.copies L n) (Stock.copies L' n))
    {p : Branch L Q k 0} {p' : Branch L' Q' k 0}
    (hr : RunRel e f close close' run run' k p p') :
    ∃ hw : Pin.Same f (edges L Q Y k 0 p) (edges L' Q' Y' k 0 p'),
      Frame.Rel (Pin.lift e (hL k)) (Pin.lift f hw)
        ((execute_start T V L Q Y close run h).kernel p s)
        ((execute_start T' V' L' Q' Y' close' run' h').kernel p' s') := by
  have hz : Pin.Same e 0 0 := fun _ => rfl
  obtain ⟨hw, hk⟩ := execute_rel h h' hL hz hr
  exact ⟨hw, hk.pull (Square.orders_eq e (zero_add _) (zero_add _) (hz.add (hL k)) (hL k))
    (Square.refl (Pin.lift f hw))⟩

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-!
# Locality of simultaneous inventory moves

Only the participants incident at the chosen site need to correspond.
Inactive participants add no stock and contribute the scalar one.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol

open Routing Board Finset

variable {K S S' I I' E E' J J' : Type} [Field K]
  [Fintype I] [Fintype I'] [Fintype E] [Fintype E'] [Fintype J] [Fintype J']
  {s : S} {s' : S'} {u : Finset J} {u' : Finset J'}

@[to_additive]
theorem prod_match {M : Type} [CommMonoid M] {v : J → M} {w : J' → M}
    (g : ↥u ≃ ↥u') (he : ∀ j : ↥u, v j = w (g j))
    (hv : ∀ j ∉ u, v j = 1) (hw : ∀ j ∉ u', w j = 1) : ∏ j, v j = ∏ j, w j := by
  rw [← prod_subset (subset_univ u) (fun j _ hj => hv j hj),
    ← prod_subset (subset_univ u') (fun j _ hj => hw j hj),
    ← prod_coe_sort u v, ← prod_coe_sort u' w, ← g.prod_comp]
  exact prod_congr rfl fun j _ => he j

private def outputSlot (T : I → Board K S) (V : E → Board K S)
    {p : J → I → ℕ} {c : J → E → ℕ} (a : Pin.Assignment p) (b : Pin.Assignment c)
    (j : J) (s : S) :
    ((orders T (p j)).join (orders V (c j))).localPort s →
      ((orders T (fun i => ∑ j, p j i)).join (orders V (fun i => ∑ j, c j i))).localPort s :=
  ((union_join _ _).trans ((orders_sum T p a).symm.join (orders_sum V c b).symm)).local s ∘
    component (fun i => (orders T (p i)).join (orders V (c i))) s j

variable {T : I → Board K S} {T' : I' → Board K S'} {V : E → Board K S} {V' : E' → Board K S'}
  {e : Pin T s ≃ Pin T' s'} {f : Pin V s ≃ Pin V' s'}

private theorem output_match {g : ↥u ≃ ↥u'} {p : J → I → ℕ} {c : J → E → ℕ}
    {p' : J' → I' → ℕ} {c' : J' → E' → ℕ}
    {a : Pin.Assignment p} {b : Pin.Assignment c} {a' : Pin.Assignment p'} {b' : Pin.Assignment c'}
    (ha : Pin.Align e g a a') (hb : Pin.Align f g b b')
    (hp : Pin.Same e (fun i => ∑ j, p j i) (fun i => ∑ j, p' j i))
    (hc : Pin.Same f (fun i => ∑ j, c j i) (fun i => ∑ j, c' j i))
    (j : ↥u) (hpj : Pin.Same e (p j) (p' (g j))) (hcj : Pin.Same f (c j) (c' (g j)))
    (x : ((orders T (p j)).join (orders V (c j))).localPort s) :
    joinPorts (Pin.lift e hp) (Pin.lift f hc) (outputSlot T V a b j s x) =
      outputSlot T' V' a' b' (g j) s' (joinPorts (Pin.lift e hpj) (Pin.lift f hcj) x) := by
  rcases x with ⟨x|x, hx⟩
  · exact congrArg (joinLeft _ (orders V' (fun i => ∑ j, c' j i)) s') (ha.assign hp j hpj ⟨x, hx⟩)
  · exact congrArg (joinRight (orders T' (fun i => ∑ j, p' j i)) _ s') (hb.assign hc j hcj ⟨x, hx⟩)

variable [Fintype S] [Fintype S'] [DecidableEq J] [DecidableEq J']
  {q : J → Intervention I E} {q' : J' → Intervention I' E'}
  {r : ∀ j, Executes T V (q j)} {r' : ∀ j, Executes T' V' (q' j)}
  {t : ∀ j, (q j).choice} {t' : ∀ j, (q' j).choice}

theorem MoveRel.parallel (a : Allocation q) (b : Allocation q') (g : ↥u ≃ ↥u')
    (hr : ∀ j : ↥u, MoveRel e f (r j) (r' (g j)) (t j) (t' (g j)))
    (hs : ∀ j ∉ u, Silent s (r j) (t j)) (hs' : ∀ j ∉ u', Silent s' (r' j) (t' j))
    (h₁ : Pin.Align e g a.take b.take) (h₂ : Pin.Align e g (a.put t) (b.put t'))
    (h₃ : Pin.Align f g (a.core t) (b.core t')) :
    MoveRel e f (Executes.parallel a r) (Executes.parallel b r') t t' := by
  have ht : Pin.Same e (Intervention.parallel q).take (Intervention.parallel q').take :=
    fun i => sum_match g (fun j => (hr j).take i)
      (fun j h => (hs j h).take i) (fun j h => (hs' j h).take (e i))
  have hp : Pin.Same e ((Intervention.parallel q).put t) ((Intervention.parallel q').put t') :=
    fun i => sum_match g (fun j => (hr j).put i)
      (fun j h => (hs j h).put i) (fun j h => (hs' j h).put (e i))
  have hc : Pin.Same f ((Intervention.parallel q).core t) ((Intervention.parallel q').core t') :=
    fun i => sum_match g (fun j => (hr j).core i)
      (fun j h => (hs j h).core i) (fun j h => (hs' j h).core (f i))
  refine ⟨ht, hp, hc, fun h x y => ?_⟩
  apply prod_match g
  · intro j
    exact ((hr j).rel.pull (h₁.assign ht j (hr j).take)
      (output_match h₂ h₃ hp hc j (hr j).put (hr j).core)) h x y
  · exact fun j hj => (hs j hj).one _ _ _
  · exact fun j hj => (hs' j hj).one _ _ _

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Naming the visible pins of a chart -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Routing Spectral

variable {K S I J : Type}

theorem Pin.eq_iff {T : J → Board K I} {v : I} (p q : Pin T v) :
    p = q ↔ p.1 = q.1 ∧ HEq p.2.val q.2.val := by
  constructor
  · rintro rfl; exact ⟨rfl, HEq.rfl⟩
  · obtain ⟨i, x⟩ := p
    obtain ⟨j, y⟩ := q
    rintro ⟨rfl, h⟩
    exact congrArg (Sigma.mk _) (Subtype.ext (eq_of_heq h))

variable [Field K] [Fintype S] [Nonempty S] {N : ℕ} {b : Market I N} {s : I}
  (A : Finset (Tensor K S))

theorem Near.eq_of_fst_eq {i j : Near b s} (h : i.1 = j.1) : i = j := by
  obtain ⟨i, u⟩ := i
  obtain ⟨j, v⟩ := j
  change i = j at h
  subst j
  exact congrArg (Sigma.mk i) (Subtype.ext ((b.name i).injective (u.property.trans v.property.symm)))

theorem placeReq_slot (j : Near b s) (l : Pin (localRequest (b.code j.1) A) j.2.1) :
    HEq (placeReq A j l).2.val l.2.val := by
  obtain ⟨k, x⟩ := l
  cases k <;> exact HEq.rfl

theorem placeReq_eq_iff (i j : Near b s)
    (l : Pin (localRequest (b.code i.1) A) i.2.1)
    (r : Pin (localRequest (b.code j.1) A) j.2.1) :
    placeReq A i l = placeReq A j r ↔
      b.request A i.1 l.1 = b.request A j.1 r.1 ∧ HEq l.2.val r.2.val := by
  rw [Pin.eq_iff]
  exact and_congr Iff.rfl ⟨fun h => (placeReq_slot A i l).symm.trans (h.trans (placeReq_slot A j r)),
    fun h => (placeReq_slot A i l).trans (h.trans (placeReq_slot A j r).symm)⟩

theorem placeEdge_injective :
    Function.Injective (fun p : Σ j : Near b s, Pin (localEdge K (b.code j.1)) j.2.1 =>
      placeEdge K p.1 p.2) := by
  rintro ⟨i, x⟩ ⟨j, y⟩ h
  have he : i = j := Near.eq_of_fst_eq (congrArg (fun p => p.1.1) h)
  subst j
  have hg := congrArg (fun p => p.1) h
  have hl : x.1 = y.1 := eq_of_heq (Sigma.mk.inj hg).2
  have hv : (x.2.val : Bool) = (y.2.val : Bool) :=
    congrArg (fun p : Pin (edge K b) s => (p.2.val : Bool)) h
  exact congrArg (Sigma.mk i) ((Pin.eq_iff _ _).mpr ⟨hl, heq_of_eq hv⟩)

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Moving a count from a local chart to an incident global pin -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Routing Spectral Classical

variable {K S I I' : Type} [Field K] [Fintype S] [Nonempty S] [DecidableEq S]
  [DecidableEq I] [DecidableEq I'] {N : ℕ} (A : Finset (Tensor K S))
  {b : Market I N} {c : Market I' N} {s : I} {v : I'}

abbrev Inputs (u : Spot N) := Pin (localRequest u.1 A) u.2
abbrev LinksAt (K : Type) [Field K] (u : Spot N) := Pin (localEdge K u.1) u.2

local instance : DecidableEq (b.Good A) := @instDecidableEqSum (b.Request A) b.Edge inferInstance inferInstance

def counts (b : Market I N) (i : I) (z : (b.shape i).Goods A → ℕ) : b.Request A ⊕ b.Edge → ℕ :=
  @Stock.collect _ _ _ (@instDecidableEqSum (b.Request A) b.Edge inferInstance inferInstance)
    (b.assign A i) z

theorem counts_req (j : Near b s) (z : (b.shape j.1).Goods A → ℕ) (p : Inputs A (spot j)) :
    counts A b j.1 z (.inl (placeReq A j p).1) = z (.inl p.1) :=
  Stock.collect_inj (b.assign_injective A j.1) z (.inl p.1)

omit [Nonempty S] in
theorem counts_edge (j : Near b s) (z : (b.shape j.1).Goods A → ℕ) (p : LinksAt K (spot j)) :
    counts A b j.1 z (.inr (placeEdge K j p).1) = z (.inr p.1) :=
  Stock.collect_inj (b.assign_injective A j.1) z (.inr p.1)

theorem req_source (i : I) {z : (b.shape i).Goods A → ℕ} (p : Pin (request b A) s)
    (h : counts A b i z (.inl p.1) ≠ 0) :
    ∃ (u : {u // b.name i u = s}) (l : Inputs A (spot (⟨i, u⟩ : Near b s))),
      placeReq A ⟨i, u⟩ l = p := by
  obtain ⟨k, hk, _⟩ := Stock.collect_nonzero h
  rcases k with k | k
  · obtain ⟨u, x, hx⟩ := placeReq_surj p i k (Sum.inl.inj hk)
    exact ⟨u, ⟨k, x⟩, hx⟩
  · contradiction

omit [Nonempty S] in
theorem edge_source (i : I) {z : (b.shape i).Goods A → ℕ} (p : Pin (edge K b) s)
    (h : counts A b i z (.inr p.1) ≠ 0) :
    ∃ (u : {u // b.name i u = s}) (l : LinksAt K (spot (⟨i, u⟩ : Near b s))),
      placeEdge K ⟨i, u⟩ l = p := by
  obtain ⟨k, hk, _⟩ := Stock.collect_nonzero h
  rcases k with k | k
  · contradiction
  · obtain ⟨u, x, hx⟩ := placeEdge_surj p i k (Sum.inr.inj hk)
    exact ⟨u, ⟨k, x⟩, hx⟩

private theorem values {P : Type*} {Z Y : P → Type} {a b : P} (h : a = b)
    (f : ∀ u, Z u → Y u → ℕ) {z : Z a} {z' : Z b} (hz : HEq z z')
    {x : Y a} {y : Y b} (hx : HEq x y) : f a z x = f b z' y := by
  subst b
  rw [eq_of_heq hz, eq_of_heq hx]

variable {A} (r : Match A b c s v) (j : Near b s)
  {z : (b.shape j.1).Goods A → ℕ} {y : (c.shape (r.near j).1).Goods A → ℕ}

private theorem along {X Y U V : Type} (e : X ≃ Y) (f : U ≃ V)
    (a : U → X) (b : V → Y) (x : X → ℕ) (y : Y → ℕ)
    (h : ∀ i, e (a i) = b (f i)) (he : ∀ i, x (a i) = y (b (f i)))
    (hx : ∀ i, x i ≠ 0 → ∃ j, a j = i) (hy : ∀ i, y i ≠ 0 → ∃ j, b j = i) :
    ∀ i, x i = y (e i) := by
  intro i
  by_cases hi : ∃ j, a j = i
  · obtain ⟨j, rfl⟩ := hi
    rw [he, h]
  have zero : x i = 0 := Classical.byContradiction (fun h => hi (hx _ h))
  rw [zero]
  by_contra! hn
  obtain ⟨u, hu⟩ := hy _ hn.symm
  exact hi ⟨f.symm u, e.injective (by rw [h, f.apply_symm_apply, hu])⟩

theorem Match.same_req (hz : HEq z y) :
    Pin.Same r.req (counts A b j.1 z ∘ Sum.inl) (counts A c (r.near j).1 y ∘ Sum.inl) := by
  let g := Equiv.cast (congrArg (Inputs A) (r.spot_eq j))
  refine along r.req g (placeReq A j) (placeReq A (r.near j)) (fun p => counts A b j.1 z (.inl p.1))
    (fun p => counts A c (r.near j).1 y (.inl p.1)) ?_ ?_ ?_ ?_
  · exact fun i => r.req_eq j i (g i) (cast_heq _ _).symm
  · intro i
    rw [counts_req, counts_req]
    exact values (r.spot_eq j)
      (fun u (z : u.1.2.Goods A → ℕ) (i : Inputs A u) => z (.inl i.1)) hz (cast_heq _ _).symm
  · intro i hi
    obtain ⟨u, l, hl⟩ := req_source A _ i hi
    have he : u = j.2 := Subtype.ext ((b.name _).injective (u.property.trans j.2.property.symm))
    subst u
    exact ⟨l, hl⟩
  · intro i hi
    obtain ⟨u, l, hl⟩ := req_source A _ i hi
    have he : u = (r.near j).2 :=
      Subtype.ext ((c.name _).injective (u.property.trans (r.near j).2.property.symm))
    subst u
    exact ⟨l, hl⟩

theorem Match.same_core (hz : HEq z y) :
    Pin.Same r.core (counts A b j.1 z ∘ Sum.inr) (counts A c (r.near j).1 y ∘ Sum.inr) := by
  let g := Equiv.cast (congrArg (LinksAt K) (r.spot_eq j))
  refine along r.core g (placeEdge K j) (placeEdge K (r.near j)) (fun p => counts A b j.1 z (.inr p.1))
    (fun p => counts A c (r.near j).1 y (.inr p.1)) ?_ ?_ ?_ ?_
  · exact fun i => r.core_eq j i (g i) (cast_heq _ _).symm
  · intro i
    rw [counts_edge, counts_edge]
    exact values (r.spot_eq j)
      (fun u (z : u.1.2.Goods A → ℕ) (i : LinksAt K u) => z (.inr i.1)) hz (cast_heq _ _).symm
  · intro i hi
    obtain ⟨u, l, hl⟩ := edge_source A _ i hi
    have he : u = j.2 := Subtype.ext ((b.name _).injective (u.property.trans j.2.property.symm))
    subst u
    exact ⟨l, hl⟩
  · intro i hi
    obtain ⟨u, l, hl⟩ := edge_source A _ i hi
    have he : u = (r.near j).2 :=
      Subtype.ext ((c.name _).injective (u.property.trans (r.near j).2.property.symm))
    subst u
    exact ⟨l, hl⟩

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # The local factor of a market move in canonical coordinates -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol

open Spectral Routing Classical Board

variable {K S I G : Type} [Field K] {n : ℕ}

def feed [Fintype G] {T : G → Board K I} {s : I} {z : G → ℕ}
    (x : Lines n (Pin T s × ℕ)) (p : (orders T z).localPort s) : Fin (2 ^ n) → Bool :=
  x (⟨p.1.1.1, ⟨p.1.2, p.2⟩⟩, p.1.1.2.val)

def both {D V : Board K I} {s : I} (x : Lines n (D.localPort s)) (y : Lines n (V.localPort s)) :
    Lines n ((D.join V).localPort s)
  | ⟨.inl i, h⟩ => x ⟨i, h⟩
  | ⟨.inr i, h⟩ => y ⟨i, h⟩

private theorem placed_value [Fintype G] [Fintype S] [Fintype I]
    {D : Board K S} {V : G → Board K S} {D' : Board K I} {V' : G → Board K I}
    (v : Expansion D V) (f : S ↪ I) (e : Rename (D.move f) D')
    (g : ∀ i, Rename ((V i).move f) (V' i)) {s : I} (j : {u // f u = s}) (t : G)
    (x : Lines n (D'.localPort s)) (y : Lines n ((V' t).localPort s)) :
    ((v.place f).rename e g).kernel t s n x y = v.kernel t j.val n
      ((x ∘ e.local s) ∘ D.movePort f j) ((y ∘ (g t).local s) ∘ (V t).movePort f j) := by
  unfold Expansion.rename
  dsimp only
  rw [v.placed f j t]
  rfl

variable [Fintype S] [Nonempty S] [DecidableEq S] {N h : ℕ} {A : Finset (Tensor K S)}

abbrev Ticket (A : Finset (Tensor K S)) (N h : ℕ) :=
  Σ p : Spot N, Σ q : p.1.Move A, ↥(histograms q.move.letter (2 ^ h + Fintype.card q.move.letter))

def gather (p : Spot N) (x : Lines n (Inputs A p × ℕ)) (y : Lines n (LinksAt K p × ℕ)) :
    Lines n (Pin (goods p.1 A) p.2 × ℕ)
  | (⟨.inl i, j⟩, k) => x (⟨i, j⟩, k)
  | (⟨.inr i, j⟩, k) => y (⟨i, j⟩, k)

def Ticket.run (p : Ticket A N h) (ha : 0 ∉ A)
    (x y : Lines n (Inputs A p.1 × ℕ)) (z : Lines n (LinksAt K p.1 × ℕ)) : K :=
  if hb : Fintype.card p.2.1.move.letter ≤ 2 ^ h then
    (localAction p.1.1 A p.2.1 h ha hb).kernel p.2.2 p.1.2 n
      (feed (gather p.1 x (fun _ _ => false))) (feed (gather p.1 y z))
  else 0

variable [Fintype I] [DecidableEq I] {b : Market I N} {s : I} (j : Near b s)
  (q : (b.code j.1).Move A) (ha : 0 ∉ A) (hb : Fintype.card q.move.letter ≤ 2 ^ h)
  (hd : ∀ u ∈ q.demand, ∃ i, b.assign A j.1 u = .inl i)
  (u : ↥(histograms q.move.letter (2 ^ h + Fintype.card q.move.letter)))

def ticket : Ticket A N h := ⟨spot j, q, u⟩

private theorem post_read (d : (b.shape j.1).Goods A → ℕ)
    (y : Lines n (Pin (request b A) s × ℕ)) (z : Lines n (Pin (edge K b) s × ℕ)) :
    (both (feed y) (feed z) ∘ (post A b j.1 d).local s) ∘
        movePort (orders (goods (b.code j.1) A) d) (b.name j.1) j.2 =
      feed (gather (spot j) (fun p => y (placeReq A j p.1, p.2)) (fun p => z (placeEdge K j p.1, p.2))) := by
  funext ⟨⟨⟨i, k⟩, l⟩, hl⟩
  cases i <;> rfl

omit [Fintype I] [DecidableEq I] in
private theorem drop_feed {E : Type} [Fintype E] (D : Board K I) (V : E → Board K I)
    (z : E → ℕ) (hz : ∀ e, z e = 0) (x : Lines n (D.localPort s)) :
    x ∘ (dropEmpty D V z hz).local s = both x (feed (fun _ _ => false)) := by
  funext o
  rcases o with ⟨i|⟨⟨i, k⟩, l⟩, hl⟩
  · rfl
  · exact Fin.elim0 (Fin.cast (hz i) k)

theorem applyMove_value (x y : Lines n (Pin (request b A) s × ℕ))
    (z : Lines n (Pin (edge K b) s × ℕ)) :
    (applyMove A b j.1 q h ha hb hd).kernel u s n (feed x) (both (feed y) (feed z)) =
      (ticket j q u).run ha (fun p => x (placeReq A j p.1, p.2))
        (fun p => y (placeReq A j p.1, p.2)) (fun p => z (placeEdge K j p.1, p.2)) := by
  let v := localAction (b.code j.1) A q h ha hb
  unfold Ticket.run ticket
  dsimp only
  rw [dite_eq_left hb]
  let d := Stock.copies q.demand (q.move.block * 2 ^ h)
  let e := (post A b j.1 d).trans (dropEmpty _ _ _ (q.take_core (b.assign A j.1) (2 ^ h) hd))
  let g := fun t : ↥(histograms q.move.letter (2 ^ h + Fintype.card q.move.letter)) =>
    post A b j.1 (q.output ((b.shape j.1).links A) (2 ^ h + Fintype.card q.move.letter) t.val)
  refine (placed_value v (b.name j.1) e g j.2 u (feed x) (both (feed y) (feed z))).trans ?_
  refine congrArg₂ (v.kernel u j.2.val n) ?_ (post_read j _ y z)
  refine Eq.trans ?_ (post_read j d x (fun _ _ => false))
  have hx := drop_feed (orders (request b A) (counts A b j.1 d ∘ Sum.inl))
    (edge K b) (counts A b j.1 d ∘ Sum.inr) (q.take_core (b.assign A j.1) (2 ^ h) hd) (feed x)
  exact congrArg (fun f => (f ∘ (post A b j.1 d).local s) ∘
    movePort (orders (goods (b.code j.1) A) d) (b.name j.1) j.2) hx

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Interventions outside the marked site's neighborhood -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Routing Spectral Classical Board

variable {K S I : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S] [Fintype I]
  [DecidableEq I] {N M : ℕ} {ρ : ℝ} {A : Finset (Tensor K S)} (b : Market I N)
  (a : Atlas N A M ρ) (h : ℕ) (ha : 0 ∉ A) (hh : a.Room (2 ^ h)) (p : b.Request A → ℝ)

abbrev worker (i : b.active a p) : Executes (request b A) (edge K b) (b.localMove a p (2 ^ h) i) :=
  applyMove A b i (b.moveAt a p i) h ha (hh _ _ (b.moving a p i).1).1 (b.demand_slot a p i)

theorem silent_move (u : (b.policy a p (2 ^ h)).choice) (j : b.active a p)
    {s : I} (hoff : ∀ l, b.name j l ≠ s) : Silent s (worker b a h ha hh p j) (u j) := by
  let q := b.moveAt a p j
  let d := Stock.copies q.demand (q.move.block * 2 ^ h)
  let r := q.output ((b.shape j).links A) (2 ^ h + Fintype.card q.move.letter) (u j).val
  have req (z : (b.shape j).Goods A → ℕ) (x : Pin (request b A) s) :
      counts A b j z (.inl x.1) = 0 := by
    by_contra he
    obtain ⟨t, _⟩ := req_source A _ x he
    exact hoff _ t.property
  have core (x : Pin (edge K b) s) : counts A b j r (.inr x.1) = 0 := by
    by_contra he
    obtain ⟨t, _⟩ := edge_source A _ x he
    exact hoff _ t.property
  refine ⟨req d, req r, core, fun t x y => ?_⟩
  let v := localAction (b.code j) A q h ha (hh _ _ (b.moving a p j).1).1
  unfold worker applyMove Expansion.rename
  dsimp only
  rw [v.absent (b.name j) hoff (u j)]
  rfl

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-! # Matched moves have identical local maps -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Spectral Routing Classical Board

variable {K S I I' : Type} [Field K] [Fintype S] [Nonempty S] [DecidableEq S]
  {N M h : ℕ} {ρ : ℝ} {A : Finset (Tensor K S)}

private theorem Ticket.run_congr {a b : Ticket A N h} (hab : a = b) (ha : 0 ∉ A) {n : ℕ}
    {x y : Lines n (Inputs A a.1 × ℕ)} {z : Lines n (LinksAt K a.1 × ℕ)}
    {x' y' : Lines n (Inputs A b.1 × ℕ)} {z' : Lines n (LinksAt K b.1 × ℕ)}
    (hx : ∀ i j k, HEq i j → x (i, k) = x' (j, k))
    (hy : ∀ i j k, HEq i j → y (i, k) = y' (j, k))
    (hz : ∀ i j k, HEq i j → z (i, k) = z' (j, k)) :
    a.run ha x y z = b.run ha x' y' z' := by
  subst b
  have he : x = x' := funext fun i => hx i.1 i.1 i.2 .rfl
  have hf : y = y' := funext fun i => hy i.1 i.1 i.2 .rfl
  have hg : z = z' := funext fun i => hz i.1 i.1 i.2 .rfl
  rw [he, hf, hg]

private def Ticket.amount (q : Ticket A N h) (put : Bool) : q.1.1.2.Goods A → ℕ :=
  if put then q.2.1.output (q.1.1.2.links A) (2 ^ h + Fintype.card q.2.1.move.letter) q.2.2.val
  else Stock.copies q.2.1.demand (q.2.1.move.block * 2 ^ h)

omit [Nonempty S] in
private theorem Ticket.amount_congr {a b : Ticket A N h} (hab : a = b) (put : Bool) :
    HEq (a.amount put) (b.amount put) := by subst b; rfl

omit [Nonempty S] in
private theorem recorded {a : Atlas N A M ρ} {s t : Spot N} (he : s = t)
    (q : a.menu s.1) (r : a.menu t.1) (u : a.Branch s.1 (2 ^ h) q) (v : a.Branch t.1 (2 ^ h) r)
    (hu : HEq (some ⟨q, u⟩ : a.Record s.1 (2 ^ h)) (some ⟨r, v⟩ : a.Record t.1 (2 ^ h))) :
    (⟨s, q.val, u⟩ : Ticket A N h) = ⟨t, r.val, v⟩ := by
  subst t
  have he := Option.some.inj (eq_of_heq hu)
  obtain ⟨rfl, hv⟩ := Sigma.mk.inj he
  rw [eq_of_heq hv]

variable [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
  {b : Market I N} {c : Market I' N} {s : I} {v : I'}
  (r : Match A b c s v) (a : Atlas N A M ρ) (h : ℕ) (ha : 0 ∉ A) (hh : a.Room (2 ^ h))
  (p : b.Request A → ℝ) (p' : c.Request A → ℝ)
  (u : (b.policy a p (2 ^ h)).choice) (u' : (c.policy a p' (2 ^ h)).choice)
  (j : Near b s) (hj : j.1 ∈ b.active a p) (hj' : (r.near j).1 ∈ c.active a p')

private theorem packed (n : ℕ) :
    let i : b.active a p := ⟨j.1, hj⟩
    let q := b.localMove a p (2 ^ h) i
    let Y := orders (request b A) (q.put (u i))
    let Z := orders (edge K b) (q.core (u i))
    ∀ x y, (worker b a h ha hh p i).kernel (u i) s n x y =
      (ticket j (b.moveAt a p i) (u i)).run ha
        (fun t => Pin.read x (placeReq A j t.1) t.2)
        (fun t => Pin.read (y ∘ Y.joinLeft Z s) (placeReq A j t.1) t.2)
        (fun t => Pin.read (y ∘ Y.joinRight Z s) (placeEdge K j t.1) t.2) := by
  intro i q Y Z x y
  let X := fun t : Pin (request b A) s × ℕ => Pin.read x t.1 t.2
  let U := fun t : Pin (request b A) s × ℕ => Pin.read (y ∘ Y.joinLeft Z s) t.1 t.2
  let V := fun t : Pin (edge K b) s × ℕ => Pin.read (y ∘ Y.joinRight Z s) t.1 t.2
  refine Eq.trans ?_ (applyMove_value j _ ha (hh _ _ (b.moving a p i).1).1 (b.demand_slot a p i) (u i) X U V)
  apply congrArg₂ ((worker b a h ha hh p i).kernel (u i) s n)
  · funext l
    obtain ⟨l, k, rfl⟩ := Pin.exists_atCopy l
    exact (Pin.read_copy x l k).symm
  · funext l
    rcases l with ⟨l|l, hl⟩
    · exact (Pin.read_copy (y ∘ Y.joinLeft Z s) ⟨l.1.1, ⟨l.2, hl⟩⟩ l.1.2).symm
    · exact (Pin.read_copy (y ∘ Y.joinRight Z s) ⟨l.1.1, ⟨l.2, hl⟩⟩ l.1.2).symm

theorem Match.local_rel
    (hrec : HEq (b.record a p (2 ^ h) u j.1) (c.record a p' (2 ^ h) u' (r.near j).1)) :
    MoveRel r.req r.core (worker b a h ha hh p ⟨j.1, hj⟩)
      (worker c a h ha hh p' ⟨(r.near j).1, hj'⟩) (u ⟨j.1, hj⟩) (u' ⟨(r.near j).1, hj'⟩) := by
  let i : b.active a p := ⟨j.1, hj⟩
  let i' : c.active a p' := ⟨(r.near j).1, hj'⟩
  have ht : ticket j (b.moveAt a p i) (u i) = ticket (r.near j) (c.moveAt a p' i') (u' i') := by
    change HEq (b.record a p (2 ^ h) u i) (c.record a p' (2 ^ h) u' i') at hrec
    rw [b.record_active, c.record_active] at hrec
    exact recorded (r.spot_eq j) (b.live a p i) (c.live a p' i') _ _ hrec
  let q := b.localMove a p (2 ^ h) i
  let q' := c.localMove a p' (2 ^ h) i'
  have htake : Pin.Same r.req q.take q'.take := r.same_req j (Ticket.amount_congr ht false)
  have hput : Pin.Same r.req (q.put (u i)) (q'.put (u' i')) :=
    r.same_req j (Ticket.amount_congr ht true)
  have hcore : Pin.Same r.core (q.core (u i)) (q'.core (u' i')) :=
    r.same_core j (Ticket.amount_congr ht true)
  refine ⟨htake, hput, hcore, fun n x y => ?_⟩
  rw [packed a h ha hh p u j hj n, packed a h ha hh p' u' (r.near j) hj' n]
  let Y := orders (request c A) (q'.put (u' i'))
  let Z := orders (edge K c) (q'.core (u' i'))
  apply Ticket.run_congr ht
  · intro l l' k he
    rw [Pin.read_lift, r.req_eq j l l' he]
  · intro l l' k he
    change Pin.read ((y ∘ Y.joinLeft Z v) ∘ Pin.lift r.req hput) (placeReq A j l) k = _
    rw [Pin.read_lift, r.req_eq j l l' he]
  · intro l l' k he
    change Pin.read ((y ∘ Y.joinRight Z v) ∘ Pin.lift r.core hcore) (placeEdge K j l) k = _
    rw [Pin.read_lift, r.core_eq j l l' he]

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-!
# Assembling corresponding interventions at a site

Match only the active centers meeting this site. All other centers
are silent there. Local ordering keys give equal offsets to matching
copies, independently of the order of the other centers.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol
open Routing Spectral Finset
open scoped Classical

variable {K S I I' : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
  {N M t t' : ℕ} {ρ : ℝ} {A : Finset (Tensor K S)} {b : Market I N} {c : Market I' N}
  {s : I} {v : I'}

private def onSite (b : Market I N) (s : I) (U : Finset I) : Finset U :=
  univ.filter (fun i : U => ∃ j, b.name i.val j = s)

private def incident (b : Market I N) (s : I) (U : Finset I) :
    ↥(onSite b s U) ≃ {j : Near b s // j.1 ∈ U} where
  toFun i :=
    let h := (mem_filter.mp i.property).2
    ⟨⟨i.val.val, ⟨h.choose, h.choose_spec⟩⟩, i.val.property⟩
  invFun j := ⟨⟨j.val.1, j.property⟩,
    mem_filter.mpr ⟨mem_univ _, ⟨j.val.2.val, j.val.2.property⟩⟩⟩
  left_inv _ := rfl
  right_inv _ := Subtype.ext (Near.eq_of_fst_eq rfl)

omit [Fintype I] in
private theorem offSite {U : Finset I} {j : U} (hj : j ∉ onSite b s U) :
    ∀ l, b.name j l ≠ s := fun l hl => hj (mem_filter.mpr ⟨mem_univ _, l, hl⟩)

omit [Nonempty S] in
private theorem record_live (b : Market I N) (a : Atlas N A M ρ) (p : b.Request A → ℝ)
    (n : ℕ) (u : (b.policy a p n).choice) (i : I) :
    (b.record a p n u i).isSome = true ↔ i ∈ b.active a p := by
  unfold Market.record
  split <;> simp_all

private theorem Match.live_iff (r : Match A b c s v) (a : Atlas N A M ρ)
    (p : b.Request A → ℝ) (p' : c.Request A → ℝ) (n : ℕ)
    (u : (b.policy a p n).choice) (u' : (c.policy a p' n).choice)
    (j : Near b s) (hr : HEq (b.record a p n u j.1) (c.record a p' n u' (r.near j).1)) :
    j.1 ∈ b.active a p ↔ (r.near j).1 ∈ c.active a p' := by
  have h : (⟨_, b.record a p n u j.1⟩ : Σ i, a.Record i n) =
      ⟨_, c.record a p' n u' (r.near j).1⟩ := Sigma.ext (r.same j) hr
  have he := congrArg (fun x : Σ i, a.Record i n => x.2.isSome) h
  rw [← record_live b a p n u, ← record_live c a p' n u', he]

private theorem pack_agree {J J' : Type} [Fintype J] [Fintype J'] {U : Finset J} {U' : Finset J'}
    (e : ↥U ≃ ↥U') {z key : J → ℕ} {z' key' : J' → ℕ}
    (hkey : ∀ j : ↥U, key j = key' (e j)) (heq : ∀ j : ↥U, z j = z' (e j))
    (h₀ : ∀ j ∉ U, z j = 0) (h₀' : ∀ j ∉ U', z' j = 0)
    (i : ↥U) (k : Fin (z i)) (l : Fin (z' (e i))) (h : k.val = l.val) :
    offset z key i + k.val = offset z' key' (e i) + l.val := by
  rw [h]
  unfold offset
  simp only [sum_filter]
  apply congrArg (· + l.val)
  apply sum_match e
  · intro j
    rw [hkey i, hkey j, heq]
  · intro j hj; rw [h₀ j hj, ite_self]
  · intro j hj; rw [h₀' j hj, ite_self]

theorem Match.perform_rel (r : Match A b c s v) (a : Atlas N A M ρ)
    (g : b.Ports t) (g' : c.Ports t') (hkeys : r.keys g g')
    (h : ℕ) (ha : 0 ∉ A) (hh : a.Room (2 ^ h))
    (p : b.Request A → ℝ) (p' : c.Request A → ℝ)
    (u : (b.policy a p (2 ^ h)).choice) (u' : (c.policy a p' (2 ^ h)).choice)
    (hrec : ∀ j : Near b s, HEq (b.record a p (2 ^ h) u j.1) (c.record a p' (2 ^ h) u' (r.near j).1)) :
    MoveRel r.req r.core (perform b a g h ha hh p) (perform c a g' h ha hh p') u u' := by
  let U := onSite b s (b.active a p)
  let U' := onSite c v (c.active a p')
  let l := incident b s (b.active a p)
  let l' := incident c v (c.active a p')
  have eq (j) := r.live_iff a p p' (2 ^ h) u u' j (hrec j)
  let e : ↥U ≃ ↥U' := l.trans ((r.near.subtypeEquiv eq).trans l'.symm)
  have yes (i : ↥U) : MoveRel r.req r.core (worker b a h ha hh p i.val)
      (worker c a h ha hh p' (e i).val) (u i.val) (u' (e i).val) :=
    r.local_rel a h ha hh p p' u u' (l i).val (l i).property ((eq _).mp (l i).property) (hrec _)
  have no (i) (hi : i ∉ U) := silent_move b a h ha hh p u i (offSite hi)
  have no' (i) (hi : i ∉ U') := silent_move c a h ha hh p' u' i (offSite hi)
  have key (x : Pin (request b A) s) (i : ↥U) :
      b.position a p g x.1 i.val = c.position a p' g' (r.req x).1 (e i).val := hkeys (l i).val x
  refine MoveRel.parallel (b.allocation a p (2 ^ h) g) (c.allocation a p' (2 ^ h) g') e yes no no' ?_ ?_ ?_
  · intro j i k k' he
    exact pack_agree e (key i) (fun w => (yes w).take i) (fun w hw => (no w hw).take i)
      (fun w hw => (no' w hw).take (r.req i)) j k k' he
  · intro j i k k' he
    exact pack_agree e (key i) (fun w => (yes w).put i) (fun w hw => (no w hw).put i)
      (fun w hw => (no' w hw).put (r.req i)) j k k' he
  · intro j i k k' he
    exact pack_agree e (key := fun _ => 0) (key' := fun _ => 0) (fun _ => rfl) (fun w => (yes w).core i) (fun w hw => (no w hw).core i)
      (fun w hw => (no' w hw).core (r.core i)) j k k' he

end OAI.LinearAlgebra.MatrixExponent.Protocol
end

/-!
# A matched replay identifies the local operator at every scale
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Protocol.Match

open Spectral Routing
open scoped Classical

variable {K S I I' : Type} [Field K] [Fintype S] [DecidableEq S] [Nonempty S]
  [Fintype I] [DecidableEq I] [Fintype I'] [DecidableEq I']
  {N M t t' : ℕ} {ρ : ℝ} {A : Finset (Tensor K S)} {b : Market I N} {c : Market I' N}
  {s : I} {v : I'} (f : Match A b c s v) (a : Atlas N A M ρ)
  (g : b.Ports t) (g' : c.Ports t') (h : ℕ) (ha : 0 ∉ A) (hh : a.Room (2 ^ h)) (μ d : ℕ)

theorem replay_rel (hs : f.keys g g')
    (hd : f.depots g g') (hr : b.ready A d) (hr' : c.ready A d) (hc : UniformCap N A M)
    {k : ℕ} {z : b.Request A → ℕ} {y : c.Request A → ℕ}
    {u : b.Path a μ d (2 ^ h) k z} {w : c.Path a μ d (2 ^ h) k y}
    (he : f.Replay a μ d (2 ^ h) k z y u w) :
    RunRel f.req f.core (fun z => terminal A d M b g z hr hc)
      (fun z => terminal A d M c g' z hr' hc)
      (Q := b.decision a μ d (2 ^ h)) (Q' := c.decision a μ d (2 ^ h))
      (fun z => perform b a g h ha hh (b.stockPrice (M := M) μ d z))
      (fun z => perform c a g' h ha hh (c.stockPrice (M := M) μ d z))
      (L := b.payload A) (L' := c.payload A) k u w := by
  induction k generalizing z y with
  | zero => exact f.terminal_rel hd he d M hr hr' hc
  | succ k ih => exact ⟨f.perform_rel a g g' hs h ha hh _ _ u.1 w.1 he.2.1, ih he.2.2⟩

end OAI.LinearAlgebra.MatrixExponent.Protocol.Match
end
