import OAI.Hierarchy.TaggedShorterPair
import Mathlib.SetTheory.Cardinal.Finite

namespace OAI
/-! # Fixed wiring from compacted endpoint records to two tagged calls -/

namespace Hierarchy.TaggedShorterPair
noncomputable section
open ThreeFlat Routing CallPool Tagged
open scoped BigOperators Classical

abbrev Input (n d w : ℕ) := (Bool × Row n × Option (Fin d)) ⊕ (Bool × Row n × Fin w)
abbrev Pin (n d w : ℕ) := Input n d w ⊕ Hole n w

def inputs {n d w : ℕ} (active : Bool → Row n → Bool) (id : Bool → Rows n d)
    (data : Bool → Rows n w) : Input n d w → Bool
  | .inl (s,i,none) => active s i
  | .inl (s,i,some j) => id s i j
  | .inr (s,i,j) => data s i j

private abbrev Bus := CallTagVerifier.Bus
private abbrev Gate (n w : ℕ) := (Bool ⊕ Bool) ⊕ Hole n w

private def arity (n d w : ℕ) : Gate n w → Type
  | .inl g => CallTagVerifier.stagePin n d (some g)
  | .inr _ => Bool

private instance (n d w : ℕ) (g : Gate n w) : Fintype (arity n d w g) := by
  cases g <;> dsimp [arity] <;> infer_instance

private def getData {n d w : ℕ} (kind side : Bool) (i : Row n) (j : Fin w) :
    Option (Pin n d w ⊕ Bus n d) :=
  if kind then some (.inl (.inl (.inr (side,i,j))))
  else if h : j.val < 1+d+n then some (.inr (.inr (side,i,⟨j.val,h⟩))) else none

private def getPin {n d w : ℕ} (p : Hole n w) : Option (Pin n d w ⊕ Bus n d) :=
  match (Tagged.portIndex n w).symm p.2 with
  | .inl (i,j) => getData p.1 true i j
  | .inr (.inl (i,j)) => some (.inl (.inr (false,Tagged.portIndex n w (.inr (.inl (i,j))))))
  | .inr (.inr (i,j)) => getData p.1 false i j

private def wires (n d w : ℕ) : (g : Gate n w) → arity n d w g → Pin n d w ⊕ Bus n d
  | .inl g, p => match CallTagVerifier.wire n d (some g) p with
    | .inl (.inl t) => .inl (.inr (false,Tagged.portIndex n w (.inr (.inl t))))
    | .inl (.inr a) => .inl (.inl (.inl a))
    | .inr a => .inr a
  | .inr p, b => Bool.rec (motive:=fun _ => Pin n d w ⊕ Bus n d)
      (.inl (.inr p)) ((getPin p).getD (.inl (.inr p))) (b : Bool)

private def stages (F : Type*) [Zero F] [One F] (n d w : ℕ) :
    (g : Gate n w) → BitNetwork F (Fintype.card (arity n d w g))
  | .inl g => CallTagVerifier.stage F n d (some g)
  | .inr p => TypedWiring.localTable (P := Bool) fun a =>
    if a false = (if (getPin (d := d) p).isSome then a true else false) then 1 else 0

/-- Open pins include one full numbered copy of each tagged table. Shared
hidden wires carry the ripple counts and their formatted words. -/
def cut (F : Type*) [Zero F] [One F] (n d w : ℕ) : BitNetwork F (Fintype.card (Pin n d w)) :=
  TypedWiring.glue (stages F n d w) (wires n d w)

private def rank {n d : ℕ} (h : Bus n d → Bool) (s : Bool) (i : Row n) (j : Fin n) :=
  h (.inl (s,i,j))
private def word {n d : ℕ} (h : Bus n d → Bool) (s : Bool) (i : Row n) (j : Fin (1+d+n)) :=
  h (.inr (s,i,j))

private theorem copy_read {n d w : ℕ} (active : Bool → Row n → Bool) (id : Bool → Rows n d)
    (data : Bool → Rows n w) (z : Hole n w → Bool) (h : Bus n d → Bool) (p : Hole n w) :
    ((getPin (d := d) p).map (Sum.elim (Sum.elim (inputs active id data) z) h)).getD false =
      pairPins (holeTags z) (fun s i => widenRecord w (word h s i)) data p := by
  obtain ⟨b,k⟩ := p
  obtain ⟨port,rfl⟩ := (Tagged.portIndex n w).surjective k
  cases b <;> rcases port with ⟨i,j⟩ | (⟨i,j⟩ | ⟨i,j⟩) <;>
    simp [getPin,getData,pairPins,callInput,inputs,holeTags,widenRecord,word,Function.uncurry] <;>
    split_ifs <;> rfl

private theorem copy_eval (F : Type*) [CommSemiring F] {n d w : ℕ}
    (active : Bool → Row n → Bool) (id : Bool → Rows n d) (data : Bool → Rows n w)
    (z : Hole n w → Bool) (h : Bus n d → Bool) (p : Hole n w) :
    TypedWiring.value (stages F n d w (.inr p))
      (fun k => Sum.elim (Sum.elim (inputs active id data) z) h (wires n d w (.inr p) k)) =
      if z p = pairPins (holeTags z) (fun s i => widenRecord w (word h s i)) data p then 1 else 0 := by
  let phi (a : Bool → Bool) : F :=
    if a false = (if (getPin (d:=d) p).isSome then a true else false) then 1 else 0
  let x (b : Bool) := Sum.elim (Sum.elim (inputs active id data) z) h (wires n d w (.inr p) b)
  change TypedWiring.value (P:=Bool) (TypedWiring.localTable (P:=Bool) phi) x = _
  refine (TypedWiring.localTable_value phi x).trans ?_
  rw [←copy_read active id data z h p]
  cases e : getPin (d := d) p <;> simp [phi,x,wires,e] <;> rfl

private theorem prefix_eval (F : Type*) [CommSemiring F] {n d w : ℕ}
    (active : Bool → Row n → Bool) (id : Bool → Rows n d) (data : Bool → Rows n w)
    (z : Hole n w → Bool) (h : Bus n d → Bool) (b : Bool) :
    TypedWiring.value (stages F n d w (.inl (.inl b)))
      (fun k => Sum.elim (Sum.elim (inputs active id data) z) h (wires n d w (.inl (.inl b)) k)) =
      if rank h b = CallTagPrefix.words n (fun i => !(active b i)) then 1 else 0 := by
  let pin : CallTagPrefix.Pin (2^n) n → Bool :=
    CallTagPrefix.pins (active b) (rank h b)
  let x : CallTagPrefix.Pin (2^n) n → Bool :=
    fun k => Sum.elim (Sum.elim (inputs active id data) z) h (wires n d w (.inl (.inl b)) k)
  have hx : x = pin := by
    funext k
    cases k <;> rfl
  change TypedWiring.value (TypedWiring.flipPins (CallTagPrefix.network F (2^n) n) _) x = _
  rw [hx,TypedWiring.value_flipPins]
  have eqn : (fun p => (pin p).xor (CallTagVerifier.mask p)) =
      CallTagPrefix.pins (fun i => !(active b i)) (rank h b) := by
    funext p
    cases p <;> simp [pin,CallTagPrefix.pins,CallTagVerifier.mask]
  rw [eqn,CallTagPrefix.network_eval]

private theorem word_eval (F : Type*) [CommSemiring F] {n d w : ℕ}
    (active : Bool → Row n → Bool) (id : Bool → Rows n d) (data : Bool → Rows n w)
    (z : Hole n w → Bool) (h : Bus n d → Bool) (b : Bool) :
    TypedWiring.value (stages F n d w (.inl (.inr b)))
      (fun k => Sum.elim (Sum.elim (inputs active id data) z) h (wires n d w (.inl (.inr b)) k)) =
      if word h b = fun i => CallTagWord.word (active b i) (id b i) (rank h b i) then 1 else 0 := by
  let x : CallTagWord.Pin (2^n) d n → Bool :=
    fun k => Sum.elim (Sum.elim (inputs active id data) z) h (wires n d w (.inl (.inr b)) k)
  change TypedWiring.value (CallTagWord.network F (2^n) d n) x = _
  have eqn : x = CallTagWord.pins (active b) (id b) (rank h b) (word h b) := by
    funext k
    rcases k with i | (⟨i,j⟩ | (⟨i,j⟩ | ⟨i,j⟩)) <;> rfl
  rw [eqn,CallTagWord.network_eval]

theorem cut_eval (F : Type*) [CommSemiring F] {n d w : ℕ}
    (active : Bool → Row n → Bool) (id : Bool → Rows n d) (data : Bool → Rows n w)
    (z : Hole n w → Bool) :
    TypedWiring.value (cut F n d w) (Sum.elim (inputs active id data) z) =
      if z = pairPins (holeTags z) (records w active id) data then 1 else 0 := by
  let ranks s := CallTagPrefix.words n (fun i => !(active s i))
  let star : Bus n d → Bool := Sum.elim (fun p => ranks p.1 p.2.1 p.2.2)
    (fun p => CallTagVerifier.records active id p.1 p.2.1 p.2.2)
  have good (h : Bus n d → Bool) :
      (∀ b, rank h b = ranks b) ∧
      (∀ b, word h b = fun i => CallTagWord.word (active b i) (id b i) (rank h b i)) ↔ h = star := by
    constructor
    · rintro ⟨hr,hw⟩
      funext p
      rcases p with ⟨s,i,j⟩ | ⟨s,i,j⟩
      · exact congrFun (congrFun (hr s) i) j
      · have h' := hw s
        rw [hr s] at h'
        exact congrFun (congrFun h' i) j
    · rintro rfl
      exact ⟨fun _ => rfl,fun _ => rfl⟩
  have eval (h : Bus n d → Bool) :
      (∏ g, TypedWiring.value (stages F n d w g)
        (fun k => Sum.elim (Sum.elim (inputs active id data) z) h (wires n d w g k))) =
          if h = star then (if z = pairPins (holeTags z) (records w active id) data then 1 else 0) else 0 := by
    rw [Fintype.prod_sum_type,Fintype.prod_sum_type]
    simp only [prefix_eval,word_eval,copy_eval,Fintype.prod_boole]
    by_cases hh : h = star
    · subst h
      rw [ite_eq_left rfl]
      obtain ⟨hr,hw⟩ := (good star).mpr rfl
      dsimp only [ranks] at hr
      rw [ite_eq_left hr,ite_eq_left hw,one_mul,one_mul]
      change (if ∀ p, z p = pairPins (holeTags z) (records w active id) data p then _ else _) = _
      simp only [← funext_iff]
    · rw [ite_eq_right hh]
      by_cases hr : ∀ b, rank h b = ranks b
      · have hw : ¬∀ b, word h b = fun i => CallTagWord.word (active b i) (id b i) (rank h b i) :=
          fun hw => hh ((good h).mp ⟨hr,hw⟩)
        rw [ite_eq_right hw,mul_zero,zero_mul]
      · dsimp only [ranks] at hr
        rw [ite_eq_right hr,zero_mul,zero_mul]
  rw [cut,TypedWiring.glue_value]
  simp only [eval,Finset.sum_ite_eq',Finset.mem_univ,ite_true]

private theorem copy_cells (F : Type*) [Zero F] [One F] (n d w : ℕ) (p : Hole n w) :
    (stages F n d w (.inr p)).cells = 16 := by
  simp [stages,TypedWiring.localTable,TableCompiler.localTableNetwork_cells]

private theorem copy_internal (F : Type*) [Zero F] [One F] (n d w : ℕ) (p : Hole n w) :
    (stages F n d w (.inr p)).internal = 12 := by
  simp [stages,TypedWiring.localTable,TableCompiler.localTableNetwork_internal]

private theorem prefix_cells (F : Type*) [Zero F] [One F] (n d w : ℕ) (b : Bool) :
    (stages F n d w (.inl (.inl b))).cells=(CallTagPrefix.network F (2^n) n).cells := rfl
private theorem prefix_internal (F : Type*) [Zero F] [One F] (n d w : ℕ) (b : Bool) :
    (stages F n d w (.inl (.inl b))).internal=(CallTagPrefix.network F (2^n) n).internal := rfl
private theorem word_cells (F : Type*) [Zero F] [One F] (n d w : ℕ) (b : Bool) :
    (stages F n d w (.inl (.inr b))).cells=(CallTagWord.network F (2^n) d n).cells := rfl
private theorem word_internal (F : Type*) [Zero F] [One F] (n d w : ℕ) (b : Bool) :
    (stages F n d w (.inl (.inr b))).internal=(CallTagWord.network F (2^n) d n).internal := rfl

/-- The cost includes the hidden rank and word buses, all copy gates, and
their internal variables. The shorter tagged factors are exposed as cut pins. -/
theorem cut_cost (F : Type*) [Zero F] [One F] (n d w : ℕ) :
    (cut F n d w).cells + (cut F n d w).internal ≤
      1000*(2^n)*(1+n+d+w) := by
  have cb : Nat.card Bool=2 := Nat.card_eq_fintype_card.trans Fintype.card_bool
  have pc := CallTagPrefix.network_cells F (2^n) n
  have pi := CallTagPrefix.network_internal F (2^n) n
  have wc := CallTagWord.network_cells F (2^n) d n
  have wi := (CallTagWord.network_internal F (2^n) d n).trans wc
  let count (p q c : ℕ) : Gate n w → ℕ :=
    Sum.elim (Sum.elim (fun _ => p) (fun _ => q)) (fun _ => c)
  let pre := CallTagPrefix.network F (2^n) n
  let fmt := CallTagWord.network F (2^n) d n
  have sc : (∑ g, (stages F n d w g).cells) = ∑ g, count pre.cells fmt.cells 16 g := by
    apply Finset.sum_congr rfl
    intro g _
    rcases g with (b | b) | p
    · exact prefix_cells F n d w b
    · exact word_cells F n d w b
    · exact copy_cells F n d w p
  have si : (∑ g, (stages F n d w g).internal) = ∑ g, count pre.internal fmt.internal 12 g := by
    apply Finset.sum_congr rfl
    intro g _
    rcases g with (b | b) | p
    · exact prefix_internal F n d w b
    · exact word_internal F n d w b
    · exact copy_internal F n d w p
  simp only [cut,TypedWiring.glue_cells,TypedWiring.glue_internal]
  rw [sc,si]
  simp only [count,Fintype.sum_sum_type,Sum.elim_inl,Sum.elim_inr,
    Finset.sum_const,Finset.card_univ,nsmul_eq_mul,Nat.cast_id]
  dsimp only [pre,fmt]
  have cardBus : Fintype.card (Bus n d)=2*(2^n*n)+2*(2^n*(1+d+n)) := by
    simp only [←Nat.card_eq_fintype_card,Bus,CallTagVerifier.Bus,Nat.card_sum,Nat.card_prod,Nat.card_fin,cb]
  have cardHole : Fintype.card (Hole n w)=2*Tagged.pins n w := by
    simp only [←Nat.card_eq_fintype_card,Hole,Nat.card_prod,Nat.card_fin,cb]
  have cardBool [I : Fintype Bool] : @Fintype.card Bool I=2 := by
    rw [←Nat.card_eq_fintype_card]
    exact cb
  simp only [cardBus,cardHole,cardBool,Tagged.pins]
  nlinarith only [pc,pi,wc,wi,Nat.zero_le (2^n),Nat.zero_le (2^n*n),
    Nat.zero_le (2^n*d),Nat.zero_le (2^n*w)]

theorem cut_contract (F : Type*) [CommSemiring F] {n d w : ℕ} (fits : 1+d+n ≤ w)
    {A : Type*} [Fintype A] (ids : A ↪ Bits d) (pos : Bool → A ↪ Row n)
    (id : Bool → Rows n d) (live : ∀ side a, id side (pos side a) = ids a)
    (data : Bool → Rows n w) (blank : ∀ s i, i ∉ Set.range (pos s) → data s i = fun _ => false) :
    (∑ z : Hole n w → Bool, TypedWiring.value (cut F n d w)
       (Sum.elim (inputs (fun s i => decide (i ∈ Set.range (pos s))) id data) z) *
       (Tagged.coeff F n w (fun j => z (false,j)) * Tagged.coeff F n w (fun j => z (true,j)))) =
      if ∀ a, data true (pos true a) = data false (pos false a) then 1 else 0 := by
  simp only [cut_eval]
  exact contract F fits ids pos id live data blank

end
end Hierarchy.TaggedShorterPair

end OAI
