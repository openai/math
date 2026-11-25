import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Physical
import OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.OrderSpec

/-! # Unique encoding and decoding of processor histories -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Spec

open scoped Classical

variable {X : Type} {k H V : ℕ} (S : Spec X k H)
variable (x : X → Bool) (g j : Level k)

@[simp] theorem badge_input (p : Fin (S.P g)) (f : S.Fields g j → Bool) :
    S.badge (S.input x g j p f) = (true, S.identifier g p.castSucc, S.data x g p) :=
  (Private.format _ _).code.symm_apply_apply _

@[simp] theorem badge_vacant : S.badge (S.vacant g j) =
    (false, S.identifier g (Fin.last (S.P g)), (S.supply g).code.symm (fun _ => false)) :=
  (Private.format _ _).code.symm_apply_apply _

private theorem blank (t : S.Input g j) (ht : S.mask g j t = true) : S.vacant g j t = false := by
  rcases t with ((u | (u | u)) | u)
  · rfl
  · contradiction
  · exact congrFun ((S.supply g).code.apply_symm_apply (fun _ => false)) u
  · rfl

variable {S x g j} {a : S.History} {b : S.Tape V}

private theorem label {y : Plan S.P V k}
    (h₀ : ∀ g i, y g i = Fin.last (S.P g) → b g i = S.vacant g i.1)
    (h₁ : ∀ g i p, y g i = p.castSucc → ∃ f, a g p = ⟨i.1, f⟩ ∧ b g i = S.input x g i.1 p f)
    (g) (i) : (S.badge (b g i)).2.1.val = (y g i).val := by
  by_cases he : y g i = Fin.last (S.P g)
  · rw [h₀ g i he, badge_vacant, he]; rfl
  obtain ⟨p, hp⟩ := Fin.exists_castSucc_eq.mpr he
  obtain ⟨f, _, hf⟩ := h₁ g i p hp.symm
  rw [hf, badge_input, ← hp]; rfl

theorem Places.proper (h : S.Places x a b) : S.Proper x b := by
  obtain ⟨y, hy, h₀, h₁⟩ := h.spec
  have he := label h₀ h₁
  have hon (g) (i) : (S.badge (b g i)).1 = decide ((y g i).val < S.P g) := by
    by_cases hv : y g i = Fin.last (S.P g)
    · simp [h₀ g i hv, hv]
    obtain ⟨p, hp⟩ := Fin.exists_castSucc_eq.mpr hv
    obtain ⟨f, _, hf⟩ := h₁ g i p hp.symm
    simp [hf, ← hp]
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro g
    constructor
    · intro p
      obtain ⟨i, hi, hu⟩ := hy.occurs g p
      refine ⟨i, ?_, fun j hj => hu j (Fin.ext ((he g j).symm.trans hj.2))⟩
      simp [he, hon, hi]
    · intro i hi
      have hv : y g i ≠ Fin.last (S.P g) := by
        intro hv
        simp [h₀ g i hv] at hi
      obtain ⟨p, hp⟩ := Fin.exists_castSucc_eq.mpr hv
      obtain ⟨f, _, hf⟩ := h₁ g i p hp.symm
      exact ⟨p, (he g i).trans (congrArg Fin.val hp.symm), by simp [hf]⟩
  · intro g i
    rw [he, hon]
    exact ⟨Nat.le_of_lt_succ (y g i).isLt, rfl⟩
  · intro g j i t hit
    change (S.badge (b g ⟨j, i⟩)).2.1.val ≤ (S.badge (b g ⟨j, t⟩)).2.1.val
    rw [he, he]
    exact hy.order g j hit
  · intro g i hi t ht
    have hv : y g i = Fin.last (S.P g) := by
      rw [hon, decide_eq_false_iff_not] at hi
      exact Fin.ext (le_antisymm (Nat.le_of_lt_succ (y g i).isLt) (le_of_not_gt hi))
    rw [h₀ g i hv]
    exact blank S g _ t ht

private theorem Places.recover (h : S.Places x a b) (g) (i) (p : Fin (S.P g))
    (hp : (S.badge (b g i)).2.1.val = p.val) : a g p = ⟨i.1, b g i ∘ Sum.inr⟩ := by
  obtain ⟨y, _, h₀, h₁⟩ := h.spec
  obtain ⟨f, ha, hb⟩ := h₁ g i p (Fin.ext ((label h₀ h₁ g i).symm.trans hp))
  rw [ha, hb]
  rfl

/-- Private matching uniquely identifies the slot holding each processor's record. -/
theorem Proper.decode (h : S.Proper x b) : ∃! a, S.Places x a b := by
  let y : Plan S.P V k :=
    fun g i => ⟨(S.badge (b g i)).2.1.val, Nat.lt_succ_of_le (h.ids g i).1⟩
  have hon (g) (i) : (S.badge (b g i)).1 = decide ((y g i).val < S.P g) := (h.ids g i).2
  have occurs (g) (p : Fin (S.P g)) : ∃! i, y g i = p.castSucc := by
    obtain ⟨i, hi, hu⟩ := (h.privateMatch g).1 p
    refine ⟨i, Fin.ext hi.2, fun j hj => hu j ⟨?_, congrArg Fin.val hj⟩⟩
    simp [hon, hj]
  let loc (g) (p : Fin (S.P g)) := (occurs g p).choose
  let a : S.History := fun g p => ⟨(loc g p).1, b g (loc g p) ∘ Sum.inr⟩
  have level (g) (i) (p : Fin (S.P g)) (hi : y g i = p.castSucc) :
      a g p = ⟨i.1, b g i ∘ Sum.inr⟩ := by
    rw [show i = loc g p from (occurs g p).choose_spec.2 _ hi]
  have hy : Assigned (fun g p => (a g p).1) y :=
    ⟨fun g j _ _ hi => h.sorted g j hi,
      fun g i p hi => congrArg Sigma.fst (level g i p hi), occurs⟩
  have id_eq (g) (i) : (S.badge (b g i)).2.1 = S.identifier g (y g i) := Fin.ext rfl
  have he (g) (i) : (Private.format _ _).code (S.badge (b g i)) = b g i ∘ Sum.inl :=
    Equiv.apply_symm_apply _ _
  refine ⟨a, ⟨y, hy, ?_, ?_⟩, ?_⟩
  · intro g i hi
    have hv : (S.badge (b g i)).1 = false := by simp [hon, hi]
    funext t
    by_cases ht : S.mask g i.1 t = true
    · exact (h.vacant g i hv t ht).trans (blank S g i.1 t ht).symm
    rcases t with ((u | (u | u)) | u) <;> try contradiction
    have eq := congrFun (he g i) (.inr (.inl u))
    change (Coloring.Format.addr H).code (S.badge (b g i)).2.1 u = _ at eq
    rw [id_eq, hi] at eq
    exact eq.symm
  · intro g i p hi
    refine ⟨_, level g i p hi, ?_⟩
    have hv : (S.badge (b g i)).1 = true := by simp [hon, hi]
    obtain ⟨q, hq, hdata⟩ := (h.privateMatch g).2 i hv
    have ep : q = p := Fin.ext (hq.symm.trans (congrArg Fin.val hi))
    subst q
    have eq : S.badge (b g i) = (true, S.identifier g p.castSucc, S.data x g p) :=
      Prod.ext hv (Prod.ext ((id_eq g i).trans (congrArg (S.identifier g) hi)) hdata)
    funext t
    cases t with
    | inl u =>
      have hc := he g i
      rw [eq] at hc
      exact (congrFun hc u).symm
    | inr u => rfl
  · intro z hz
    funext g p
    exact hz.recover g (loc g p) p (congrArg Fin.val (occurs g p).choose_spec.1)

/-- The budget gives a unique allocation, and the allocation fixes every bit. -/
theorem encode (S : Spec X k H) (x : X → Bool) (a : S.History)
    (hs : ∀ g, ∑ p, 2 ^ (a g p).1.val ≤ 2 * V) : ∃! b : S.Tape V, S.Places x a b := by
  obtain ⟨y, hy, hu⟩ := unique_plan (fun g p => (a g p).1) hs
  have row (g) (i : Slot (S.P g) V k) : ∃ z : S.Input g i.1 → Bool,
      (y g i = Fin.last (S.P g) → z = S.vacant g i.1) ∧
      (∀ p, y g i = p.castSucc → ∃ f, a g p = ⟨i.1, f⟩ ∧ z = S.input x g i.1 p f) := by
    by_cases hv : y g i = Fin.last (S.P g)
    · exact ⟨_, fun _ => rfl, fun p hp => (Fin.castSucc_ne_last p (hp.symm.trans hv)).elim⟩
    obtain ⟨p, hp⟩ := Fin.exists_castSucc_eq.mpr hv
    have hf : ∃ f, a g p = ⟨i.1, f⟩ := by
      rw [← hy.level g i p hp.symm]
      exact ⟨(a g p).2, rfl⟩
    obtain ⟨f, hf⟩ := hf
    refine ⟨S.input x g i.1 p f, fun he => (hv he).elim, ?_⟩
    intro q hq
    have he : p = q := Fin.castSucc_inj.mp (hp.trans hq)
    subst q
    exact ⟨f, hf, rfl⟩
  let b : S.Tape V := fun g i => (row g i).choose
  have h₀ := fun g i => (row g i).choose_spec.1
  have h₁ := fun g i => (row g i).choose_spec.2
  refine ⟨b, ⟨y, hy, h₀, h₁⟩, ?_⟩
  intro z hz
  obtain ⟨u, hu', hz₀, hz₁⟩ := hz.spec
  have he := hu u hu'
  subst u
  funext g i
  by_cases hv : y g i = Fin.last (S.P g)
  · exact (hz₀ g i hv).trans (h₀ g i hv).symm
  obtain ⟨p, hp⟩ := Fin.exists_castSucc_eq.mpr hv
  obtain ⟨f, hf, hb⟩ := h₁ g i p hp.symm
  obtain ⟨t, ht, hz⟩ := hz₁ g i p hp.symm
  have eq : t = f := eq_of_heq (Sigma.mk.inj_iff.mp (ht.symm.trans hf)).2
  subst t
  exact hz.trans hb.symm

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Spec
end

/-!
# Preserving the sum of the transcript weights

The public input fixes the static supply. Each nonzero physical term
then names a unique accepted history. Conversely the charge bound
places every accepted history in a unique ordered set of slots.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
open Coloring Finset
open scoped Classical
variable {X K : Type} [Field K] {k H V U : ℕ}
    {S : Spec X k H} {x : X → Bool} {a : S.History} {b : S.Tape V}
    (D : System S U) (W : List Bool → K)

private theorem badge_on {g j : Level k} (v : S.Input g j → Bool) :
    v (S.on g j) = (S.badge v).1 := rfl

theorem Spec.Places.actors (h : S.Places x a b) :
    (∏ g, ∏ i : Slot (S.P g) V k, D.actor W g i.1 (b g i)) =
      ∏ g, ∏ p, D.value W x g p (a g p) := by
  obtain ⟨y, hy, h₀, h₁⟩ := h.spec
  apply hy.prod
  · intro g i hv
    have hz : (S.badge (b g i)).1 = false := by rw [h₀ g i hv, S.badge_vacant]
    unfold System.actor activeValue
    rw [badge_on (b g i), hz, ite_eq_right Bool.false_ne_true, ite_eq_left (h.proper.vacant g i hz)]
  · intro g i p hv
    obtain ⟨f, he, hh⟩ := h₁ g i p hv
    rw [he, hh]
    rfl

theorem Spec.Places.valid (h : S.Places x a b) (ok : D.accepts x a) :
    D.physical W x b = ∏ g, ∏ p, D.value W x g p (a g p) := by
  have t := h.proper
  have hp : S.Public x b := ⟨t.privateMatch, t.ids, t.sorted, h.messages.mpr ok.1⟩
  rw [System.physical, ite_eq_left hp, h.actors D W]

theorem System.support (h : D.physical W x b ≠ 0) :
    ∃! a, D.accepts x a ∧ S.Places x a b := by
  have ht : S.Public x b := by
    by_contra hn
    exact h (by rw [System.physical, ite_eq_right hn])
  rw [System.physical, ite_eq_left ht] at h
  have proper : S.Proper x b := by
    refine ⟨ht.privateMatch, ht.ids, ht.sorted, ?_⟩
    intro g i hi
    have hv := prod_ne_zero_iff.mp (prod_ne_zero_iff.mp h _ (mem_univ g)) _ (mem_univ i)
    unfold actor activeValue at hv
    rw [badge_on (b g i), hi, ite_eq_right Bool.false_ne_true] at hv
    by_contra hn
    exact hv (ite_eq_right hn)
  obtain ⟨a, ha, hu⟩ := proper.decode
  rw [ha.actors D W] at h
  refine ⟨a, ⟨⟨ha.messages.mp ht.messages, ?_⟩, ha⟩, fun _ he => hu _ he.2⟩
  intro g i
  have hv := prod_ne_zero_iff.mp (prod_ne_zero_iff.mp h _ (mem_univ g)) _ (mem_univ i)
  by_contra hn
  exact hv (ite_eq_right hn)

theorem System.realization [Fintype X] {h c B : ℕ} (ok : D.Bounded V h c B) :
    (fun x => ∑ b : S.Tape V, D.physical W x b) = D.tensor W := by
  funext x
  have each (b : S.Tape V) : D.physical W x b =
      ∑ a : S.History, if D.accepts x a ∧ S.Places x a b then D.physical W x b else 0 := by
    by_cases hz : D.physical W x b = 0
    · simp only [hz, ite_self, sum_const_zero]
    obtain ⟨a, ha, hu⟩ := D.support W hz
    have unique (a') : (D.accepts x a' ∧ S.Places x a' b) ↔ a' = a := ⟨hu _, fun e => e ▸ ha⟩
    simp only [unique, sum_ite_eq', mem_univ, ite_true]
  rw [show (∑ b : S.Tape V, D.physical W x b) = _ from sum_congr rfl fun b _ => each b, sum_comm]
  apply sum_congr rfl
  intro a _
  by_cases h : D.accepts x a
  · have cap (g) : (∑ p, 2 ^ (a g p).1.val) ≤ 2 * V :=
      (single_le_sum (f := fun g => ∑ p, 2 ^ (a g p).1.val) (fun _ _ => Nat.zero_le _) (mem_univ g)).trans
        (ok.charge x a h)
    obtain ⟨b, hb, hu⟩ := S.encode x a cap
    have unique (b') : S.Places x a b' ↔ b' = b := ⟨hu _, fun e => e ▸ hb⟩
    simp only [h, true_and, unique, sum_ite_eq', mem_univ, ite_true]
    exact hb.valid D W h
  · simp only [h, false_and, ite_false, sum_const_zero]

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end

/-! # Size of one slot of a bounded protocol -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.System

open Coloring Finset

variable {X : Type} {k H U : ℕ} {S : Spec X k H} (D : System S U) (g j : Level k)

theorem input_le_slotCost : Fintype.card (S.Input g j) ≤ D.slotCost g j := by
  unfold slotCost
  apply le_trans _ (Nat.le_mul_of_pos_right _ (pow_pos (by omega) _))
  have := Nat.two_pow_pos j.val
  omega

variable [Fintype X] {V h c B : ℕ} (hD : D.Bounded V h c B) (hh : 100 ≤ h)
  (hb : 100 + k + Nat.clog 2 (h + 1) + c ≤ B)

include hD hh in
/-- Charge the headers by the message count and the payloads by the dyadic capacity. -/
private theorem port_bound (l : Level k) :
    Fintype.card (S.Port j l × (S.Msg l).pins) ≤ h ^ (c + 10) + 8 * 2 ^ j.val := by
  let n := seats S.messages (2 ^ j.val) l.val
  have hn : n ≤ h ^ c := (min_le_left _ _).trans hD.count
  have hc : n * 2 ^ l.val ≤ 2 * 2 ^ j.val :=
    (Nat.mul_le_mul_right _ (min_le_right _ _)).trans (Nat.div_mul_le_self _ _)
  have hw : 2 + S.key.width ≤ h ^ 10 := by
    have hp : 2 ≤ h ^ 2 := (show 2 ≤ 100 ^ 2 by decide).trans (Nat.pow_le_pow_left hh _)
    calc
      _ ≤ 2 * h ^ 2 := by have := hD.key; omega
      _ ≤ h * h ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = h ^ 3 := (pow_succ' h 2).symm
      _ ≤ _ := Nat.pow_le_pow_right (by omega) (by decide)
  have hmsg : (S.Msg l).width = 2 + S.key.width + (S.body l).width := by
    simp only [Spec.Msg, Match.format, Format.width_pair]
    rw [Format.width_bit]
    omega
  rw [Fintype.card_prod, Fintype.card_fin]
  change n * (S.Msg l).width ≤ _
  rw [hmsg, mul_add, pow_add]
  apply Nat.add_le_add (Nat.mul_le_mul hn hw)
  calc
    _ ≤ n * (4 * 2 ^ l.val) := Nat.mul_le_mul_left _ (hD.payload l)
    _ = 4 * (n * 2 ^ l.val) := by ac_rfl
    _ ≤ 4 * (2 * 2 ^ j.val) := Nat.mul_le_mul_left _ hc
    _ = _ := by omega

include hD hh in
private theorem input_bound :
    Fintype.card (S.Input g j) ≤
      1 + h ^ (c + 10) + (S.supply g).width + B * 2 ^ j.val + B * (h ^ (c + 10) + 8 * 2 ^ j.val) := by
  have hp : (Private.format (S.supply g) H).width = 1 + H + (S.supply g).width := by
    simp only [Private.format, Format.width_pair, Format.width_addr, add_assoc]
    rw [Format.width_bit]
  have hn : H ≤ h ^ (c + 10) :=
    hD.names.trans (Nat.pow_le_pow_right (by omega) (by omega))
  have hs : ∑ l : Level k, Fintype.card (S.Port j l × (S.Msg l).pins) ≤
      B * (h ^ (c + 10) + 8 * 2 ^ j.val) := calc
    _ ≤ ∑ _ : Level k, (h ^ (c + 10) + 8 * 2 ^ j.val) := sum_le_sum fun l _ => port_bound D j hD hh l
    _ = (k + 1) * (h ^ (c + 10) + 8 * 2 ^ j.val) := by simp
    _ ≤ _ := Nat.mul_le_mul_right _ hD.height
  rw [Fintype.card_sum]
  change (Private.format (S.supply g) H).width + Fintype.card (S.Fields g j) ≤ _
  rw [hp, Fintype.card_sum, Fintype.card_fin, Fintype.card_sigma]
  have := hD.guesses g j
  omega

private theorem sizes (A T G I O Q B : ℕ) (hB : 100 ≤ B) (ht : 0 < T) (hq : Q ≤ B)
    (hi : I ≤ 1 + G + A + B * T + B * (G + 8 * T)) (ho : O ≤ 1 + 8 * Q * T) :
    1 + I + T + Q * T ≤ B ^ 2 * (A + T + G) ∧ O + 1 ≤ B ^ 2 * (A + T + G) := by
  let L := A + T + G
  have ha : A + T + G ≤ B * L := Nat.le_mul_of_pos_left L (by omega)
  have h₁ : B * (G + 8 * T) ≤ 8 * (B * L) := by
    rw [mul_left_comm 8]
    exact Nat.mul_le_mul_left _ (by unfold L; omega)
  have hg : B * T ≤ B * L := Nat.mul_le_mul_left _ (by unfold L; omega)
  have h₂ : Q * T ≤ B * L := Nat.mul_le_mul hq (by unfold L; omega)
  have h₃ : 100 * (B * L) ≤ B ^ 2 * (A + T + G) := by
    rw [pow_two, mul_assoc]
    exact Nat.mul_le_mul_right _ hB
  rw [mul_assoc] at ho
  omega

include hD hh hb in
private theorem log_bound :
    Nat.clog 2 (B ^ 2 * ((S.supply g).width + 2 ^ j.val + h ^ (c + 10))) ≤ 3 * B ^ 2 := by
  have hB : 100 ≤ B := by omega
  have hsq : B ≤ B ^ 2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right B (by omega)
  let N := 2 ^ (B ^ 2)
  have hg : (S.supply g).width ≤ N :=
    (hD.level g).trans (Nat.pow_le_pow_right (by decide) (by have := g.isLt; omega))
  have hj : 2 ^ j.val ≤ N := Nat.pow_le_pow_right (by decide) (by have := j.isLt; omega)
  have hp : h ≤ 2 ^ B := (Nat.le_succ h).trans ((Nat.le_pow_clog (by decide) (h + 1)).trans
    (Nat.pow_le_pow_right (by decide) (by omega)))
  have he : h ^ (c + 10) ≤ N := calc
    _ ≤ h ^ B := Nat.pow_le_pow_right (by omega) (by omega)
    _ ≤ (2 ^ B) ^ B := Nat.pow_le_pow_left hp _
    _ = _ := by unfold N; rw [pow_two, pow_mul]
  have hN : B ^ 2 ≤ N := Nat.lt_two_pow_self.le
  apply Nat.clog_le_of_le_pow
  calc
    _ ≤ N * (3 * N) := Nat.mul_le_mul hN (by omega)
    _ ≤ N * (N * N) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right _ (by omega))
    _ = _ := by unfold N; rw [← pow_add, ← pow_add]; congr 1; omega

private theorem scale_cost {b n m : ℕ} (a : ℕ) (hb : 0 < b) (hn : n ≤ m) :
    b ^ n * a ≤ b ^ m * a := Nat.mul_le_mul_right _ (Nat.pow_le_pow_right hb hn)

include hD hh hb in
theorem slotCost_le :
    D.slotCost g j ≤ B ^ 5000 * ((S.supply g).width + 2 ^ j.val + h ^ (c + 10)) := by
  let L := (S.supply g).width + 2 ^ j.val + h ^ (c + 10)
  let I := Fintype.card (S.Input g j)
  let O := Fintype.card (Output (2 ^ j.val) U)
  let Q := RAM.ceiling U + 1
  have hB : 100 ≤ B := by omega
  have hq : Q ≤ B := by
    have he := Nat.clog_mono_right 2 (Nat.add_le_add_right hD.dictionary 1)
    unfold Q RAM.ceiling
    omega
  have ht := Nat.two_pow_pos j.val
  obtain ⟨hs, ho⟩ := sizes (S.supply g).width (2 ^ j.val) (h ^ (c + 10)) I O Q B hB ht hq
    (input_bound D g j hD hh) (card_output _ _)
  have hl : Nat.clog 2 (B ^ 2 * L) ≤ 3 * B ^ 2 := log_bound D g j hD hh hb
  have hi : I + 1 ≤ B ^ 2 * L := by unfold L; omega
  have hb₁ := (Nat.clog_mono_right 2 hi).trans hl
  have hb₂ := (Nat.clog_mono_right 2 ho).trans hl
  have hc : 100 + j.val + D.width + (D.verify g j).size + Nat.clog 2 (I + 1) + Nat.clog 2 (O + 1) ≤ B ^ 3 := by
    have hsq : B ≤ B ^ 2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right B (by omega)
    have := j.isLt
    have := hD.addresses
    have := hD.control g j
    calc
      _ ≤ 10 * B ^ 2 := by omega
      _ ≤ B * B ^ 2 := Nat.mul_le_mul_right _ (by omega)
      _ = _ := (pow_succ' B 2).symm
  calc
    _ ≤ (B ^ 2 * L) * (B ^ 3) ^ 212 := Nat.mul_le_mul hs (Nat.pow_le_pow_left hc _)
    _ = B ^ 638 * L := by rw [mul_right_comm, ← pow_mul, ← pow_add]
    _ ≤ _ := scale_cost L (by omega) (by decide)

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.System
end

/-! # Total cost of checking a bounded protocol -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.System.Bounded

open Finset
variable {X : Type} [Fintype X] {k H U V h c B W : ℕ} {S : Spec X k H} {D : System S U}

/-- Charge private data to its static budget and dyadic capacity to the volume.
The extra entry accounts for routing, even in an empty group. -/
private theorem group_bound (hd : D.Bounded V h c B) (hb : 100 ≤ B) (a : ℕ) (g : Level k) :
    (S.pool V g + 1) * ((S.supply g).width + a) + (∑ i : Slot (S.P g) V k, capacity i)
      ≤ B ^ 2 * (V + S.size * a) := by
  have hp : S.P g ≤ S.size := single_le_sum (fun _ _ => Nat.zero_le _) (mem_univ _)
  have hw : (S.supply g).width ≤ 2 * V :=
    (hd.level g).trans ((Nat.pow_le_pow_right (by decide) (by omega : g.val ≤ k)).trans hd.longest)
  have hpair : S.P g * (S.supply g).width ≤ 2 * V :=
    (single_le_sum (f := fun g => S.P g * (S.supply g).width) (fun _ _ => Nat.zero_le _)
      (mem_univ g)).trans hd.static
  have hp' : S.P g + 1 ≤ 2 * S.size := by have := hd.processors; omega
  have hm : (S.P g + 1) * ((S.supply g).width + a) ≤ 4 * (V + S.size * a) := by
    have ha := Nat.mul_le_mul_right a hp'
    nlinarith only [ha, hw, hpair, Nat.zero_le (S.size * a)]
  have hc := (card_slots (S.P g) V k).trans (Nat.mul_le_mul_right _ hd.height)
  have hpool : S.pool V g + 1 ≤ (B + 1) * (S.P g + 1) := by
    unfold Spec.pool
    nlinarith only [hc, Nat.zero_le B]
  have hcap := (sum_capacity (S.P g) V k).trans (Nat.mul_le_mul_right _ hd.height)
  calc
    _ ≤ ((B + 1) * (S.P g + 1)) * ((S.supply g).width + a) + B * (2 * V) :=
      Nat.add_le_add (Nat.mul_le_mul_right _ hpool) hcap
    _ ≤ (B + 1) * (4 * (V + S.size * a)) + B * (2 * (V + S.size * a)) := by
      rw [mul_assoc]; exact Nat.add_le_add (Nat.mul_le_mul_left _ hm)
        (Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (Nat.le_add_right _ _)))
    _ = (6 * B + 4) * (V + S.size * a) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ (by nlinarith only [hb])

private theorem groups (hd : D.Bounded V h c B) (hb : 100 ≤ B) (a : ℕ) :
    (∑ g, (S.pool V g + 1) * ((S.supply g).width + a)) ≤ B ^ 3 * (V + S.size * a) ∧
    (∑ i : S.Site V, ((S.supply i.1).width + 2 ^ i.2.1.val + a)) ≤ B ^ 3 * (V + S.size * a) := by
  have hs : (∑ _ : Level k, B ^ 2 * (V + S.size * a)) ≤ B ^ 3 * (V + S.size * a) := by
    simp only [sum_const, card_univ, Fintype.card_fin, Nat.nsmul_eq_mul]
    rw [pow_succ' B 2, mul_assoc]
    exact Nat.mul_le_mul_right _ hd.height
  constructor
  · exact (sum_le_sum fun g _ => (Nat.le_add_right _ _).trans (group_bound hd hb a g)).trans hs
  rw [Fintype.sum_sigma]
  refine (sum_le_sum fun g _ => ?_).trans hs
  refine le_trans ?_ (group_bound hd hb a g)
  calc
    _ = Fintype.card (Slot (S.P g) V k) * ((S.supply g).width + a) +
        (∑ i : Slot (S.P g) V k, capacity i) := by
      simp only [sum_add_distrib, sum_const, card_univ, Nat.nsmul_eq_mul, capacity]; ring
    _ ≤ _ := Nat.add_le_add_right (Nat.mul_le_mul_right _ (by unfold Spec.pool; omega)) _

/-- Sum the costs of checking all processors, private inputs and message batches. -/
theorem estimate (hd : D.Bounded V h c B) (hh : 100 ≤ h)
    (hb : 100 + k + Nat.clog 2 (h + 1) + c ≤ B) (hw : 1 ≤ W) (C : ℕ) :
    D.cost V h C W ≤ W * B ^ 10000 * (V + S.size * h ^ (C + c + 40)) := by
  let a := h ^ (C + c + 40)
  let t := V + S.size * a
  let u := W * B ^ 6000 * t
  have hB : 100 ≤ B := by omega
  have h₁ : 1 ≤ h := by omega
  have b₁ : 1 ≤ B := by omega
  have ha : 1 ≤ a := one_le_pow₀ h₁
  have ht : 1 ≤ t := by
    have hp := hd.processors
    unfold t; exact (Nat.mul_pos hp ha).trans_le (Nat.le_add_left _ _)
  have hu : t ≤ u := Nat.le_mul_of_pos_left _ (by positivity)
  have hb₃ : B ^ 3 ≤ B ^ 6000 := pow_le_pow_right₀ b₁ (by omega)
  have hb₅ : B ^ 5000 * B ^ 3 ≤ W * B ^ 6000 := calc
    _ = B ^ (5000 + 3) := (pow_add ..).symm
    _ ≤ B ^ 6000 := pow_le_pow_right₀ b₁ (by omega)
    _ ≤ _ := Nat.le_mul_of_pos_left _ hw
  obtain ⟨hp, hs⟩ := groups hd hB a
  have hslots : (∑ i : S.Site V, D.slotCost i.1 i.2.1) ≤ u := calc
    _ ≤ ∑ i : S.Site V, B ^ 5000 * ((S.supply i.1).width + 2 ^ i.2.1.val + a) := by
      apply sum_le_sum
      intro i _
      refine (D.slotCost_le _ _ hd hh hb).trans (Nat.mul_le_mul_left _ (Nat.add_le_add_left ?_ _))
      exact pow_le_pow_right₀ h₁ (by omega : c + 10 ≤ C + c + 40)
    _ ≤ B ^ 5000 * (B ^ 3 * t) := by rw [← mul_sum]; exact Nat.mul_le_mul_left _ hs
    _ ≤ _ := by rw [← mul_assoc]; exact Nat.mul_le_mul_right _ hb₅
  have hhidden : Fintype.card (S.Hidden V) ≤ u := by
    rw [Fintype.card_sigma]
    exact (sum_le_sum fun i _ => D.input_le_slotCost _ _).trans hslots
  have hpools : (∑ g, W * (S.pool V g + 1) * ((S.supply g).width + h ^ C)) ≤ u := calc
    _ ≤ ∑ g, W * ((S.pool V g + 1) * ((S.supply g).width + a)) := by
      apply sum_le_sum
      intro g _
      rw [mul_assoc]
      have : h ^ C ≤ a := pow_le_pow_right₀ h₁ (by omega : C ≤ C + c + 40)
      gcongr
    _ ≤ W * (B ^ 3 * t) := by rw [← mul_sum]; exact Nat.mul_le_mul_left _ hp
    _ ≤ _ := by rw [← mul_assoc]; exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left _ hb₃)
  have hhead : (100 + H) ^ 10 ≤ a := calc
    _ ≤ (h ^ 3) ^ 10 := by
      apply Nat.pow_le_pow_left
      have hx := hd.names
      have hz : h ≤ h ^ 2 := by nlinarith only [hh]
      calc
        _ ≤ 2 * h ^ 2 := by omega
        _ ≤ h ^ 3 := by rw [pow_succ' h 2]; gcongr; omega
    _ = h ^ 30 := (pow_mul h 3 10).symm
    _ ≤ _ := pow_le_pow_right₀ h₁ (by omega : 30 ≤ C + c + 40)
  have hnames : (k + 1) * S.size * (100 + H) ^ 10 ≤ u := calc
    _ ≤ B * (S.size * a) := by rw [mul_assoc]; exact Nat.mul_le_mul hd.height (Nat.mul_le_mul_left _ hhead)
    _ ≤ _ := by
      have hbase : B ≤ B ^ 3 := by simpa using (pow_le_pow_right₀ b₁ (by decide : 1 ≤ 3))
      exact Nat.mul_le_mul (hbase.trans (hb₃.trans (Nat.le_mul_of_pos_left _ hw))) (Nat.le_add_left _ _)
  have hx : Fintype.card X ≤ u := hd.exterior.trans ((Nat.le_add_right _ _).trans hu)
  have hch : Channels.cost S.key S.body (S.Reserved V) h C W ≤ u := hd.estimate_channels hh hb hw C
  have hscale : 70000 ≤ B ^ 4000 := calc
    _ ≤ 100 ^ 3 := by decide
    _ ≤ B ^ 3 := Nat.pow_le_pow_left hB _
    _ ≤ _ := pow_le_pow_right₀ b₁ (by omega)
  calc
    D.cost V h C W ≤ 70000 * u := by unfold cost; omega
    _ ≤ B ^ 4000 * u := Nat.mul_le_mul_right _ hscale
    _ = W * (B ^ 4000 * B ^ 6000) * t := by unfold u; ac_rfl
    _ = _ := by rw [← pow_add]

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.System.Bounded
end

/-! # Canonical allocation of charged strings to fixed seats -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings

open RAM
variable {n M T k : ℕ}

private theorem enough (x : Fin n → List Bool) (hm : n ≤ M) (ht : ∑ j, callCharge (x j) ≤ T)
    (l : Level k) : (bucket (fun j => callCharge (x j)) l.val).card ≤ seats M T l.val :=
  (bucket_capacity (fun _ => le_max_left 1 _) ht l.val).trans (min_le_min_right _ hm)

def place (x : Fin n → List Bool) (hm : n ≤ M) (ht : ∑ j, callCharge (x j) ≤ T)
    (hk : ∀ j, (x j).length ≤ 2 ^ k) : Placement M T k x := by
  have h (l : Level k) := unique_seats _ (enough x hm ht l)
  let ord (s : Slot M T k) := (h s.1).choose s.2
  have ordered (l : Level k) : OrderedSeats (bucket (fun j => callCharge (x j)) l.val)
      (fun s => ord ⟨l, s⟩) := (h l).choose_spec.1
  have index (s : Slot M T k) (j : Fin n) (hs : ord s = j.castSucc) :
      s.1.val = Nat.clog 2 (callCharge (x j)) :=
    (Finset.mem_filter.mp (((ordered s.1).2.1 j).mp ⟨s.2, hs⟩)).2.symm
  have covered (j : Fin n) : ∃! s, ord s = j.castSucc := by
    have hb : Nat.clog 2 (callCharge (x j)) ≤ k :=
      (Nat.clog_le_iff_le_pow (by decide)).mpr (max_le (Nat.two_pow_pos k) (hk j))
    let l : Level k := ⟨_, Nat.lt_succ_of_le hb⟩
    obtain ⟨s, hs⟩ := ((ordered l).2.1 j).mpr (by simp [bucket, l])
    refine ⟨⟨l, s⟩, hs, ?_⟩
    rintro ⟨d, z⟩ hz
    have hd : d = l := Fin.ext (index ⟨d, z⟩ j hz)
    subst d
    have he : z = s := (ordered l).2.2 _ _ (hz.trans hs.symm) (hz.trans_ne (Fin.castSucc_ne_last j))
    rw [he]
  let f (j : Fin n) := (covered j).choose
  have hf (j) : ord (f j) = j.castSucc := (covered j).choose_spec.1
  have inj : Function.Injective f := fun i j hij =>
    Fin.castSucc_inj.mp ((hf i).symm.trans ((congrArg ord hij).trans (hf j)))
  exact ⟨⟨f, inj⟩, ord, ordered, hf, fun s j hs => ((covered j).choose_spec.2 s hs).symm,
    fun j => index _ j (hf j)⟩

theorem place_unique (x : Fin n → List Bool) (hm : n ≤ M) (ht : ∑ j, callCharge (x j) ≤ T)
    (hk : ∀ j, (x j).length ≤ 2 ^ k) (q : Placement M T k x) : q = place x hm ht hk := by
  let p := place x hm ht hk
  change q = p
  clear_value p
  have ho : q.ordinal = p.ordinal := by
    funext ⟨l, s⟩
    exact congrFun ((unique_seats _ (enough x hm ht l)).unique (q.ordered l) (p.ordered l)) s
  have hf : q.toSlot = p.toSlot := by
    apply DFunLike.ext _ _
    intro j
    exact q.fromSlot _ j (by rw [ho, p.atSlot])
  cases q
  cases p
  cases ho
  cases hf
  rfl

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings
end

/-!
# Packing arbitrary bit strings into length classes

Both the empty string and a one-bit string occupy class zero.
The token records the exact length, so they cannot match.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings

open RAM Coloring
open scoped Classical

variable {I : Type} {A : Format} {n T : I → ℕ} {M k : ℕ}

/-- Equal tokens agree under every dictionary, including a singleton indicator. -/
theorem encode_inj {b : ℕ} {x y : List Bool} (hx : x.length ≤ 2 ^ b) (hy : y.length ≤ 2 ^ b)
    (he : encodeToken b x = encodeToken b y) : x = y := by
  let W (z : List Bool) : ℚ := if x = z then 1 else 0
  have h := congrArg (tokenValue (2 ^ b) W b) he
  rw [tokenValue_encode W b x hx hx, tokenValue_encode W b y hy hy] at h
  by_contra hn
  simp [W, hn] at h

abbrev Payload (k : ℕ) := Σ l : Level k, (token l.val).obj

private theorem payload_eq {a b : Level k} {x y : List Bool}
    (ha : a.val = Nat.clog 2 (callCharge x)) (hb : b.val = Nat.clog 2 (callCharge y)) :
    (⟨a, encodeToken a.val x⟩ : Payload k) = ⟨b, encodeToken b.val y⟩ ↔ x = y := by
  constructor
  · intro h
    have e : a = b := congrArg Sigma.fst h
    subst b
    have bound (z : List Bool) (hz : a.val = Nat.clog 2 (callCharge z)) : z.length ≤ 2 ^ a.val := by
      rw [hz]
      exact (le_max_right _ _).trans (Nat.le_pow_clog (by decide) _)
    exact encode_inj (bound x ha) (bound y hb) (eq_of_heq (Sigma.mk.inj h).2)
  · rintro rfl
    rw [show a = b from Fin.ext (ha.trans hb.symm)]

variable (row : Rows A n) (p : Layout row M k T)

theorem atSlot (i : I) (j : Fin (n i)) :
    let s := (p i).toSlot j
    code row p s.1 ⟨i, s.2⟩ =
      (true, (row i j).1, (row i j).2.1, encodeToken s.1.val (row i j).2.2) := by
  simp [code, (p i).atSlot j]

theorem unused (i : I) (s : Slot M (T i) k) (hs : s ∉ Set.range (p i).toSlot) :
    code row p s.1 ⟨i, s.2⟩ =
      (false, false, A.code.symm (fun _ => false), emptyToken s.1.val) := by
  have he : (p i).ordinal s = Fin.last (n i) := by
    by_contra h
    obtain ⟨j, hj⟩ := Fin.exists_castSucc_eq.mpr h
    exact hs ⟨j, (p i).fromSlot s j hj.symm⟩
  simp [code, he]

private abbrev Source (n : I → ℕ) := Σ i, Fin (n i)

private def target (a : Source n) : Σ l : Level k, Seats M T l :=
  let s := (p a.1).toSlot a.2
  ⟨s.1, a.1, s.2⟩

private theorem injective : Function.Injective (target row p) := by
  rintro ⟨i, a⟩ ⟨j, b⟩ h
  have hi : i = j := congrArg (fun v => v.2.1) h
  subst j
  let swap (v : Σ l : Level k, Seats M T l) : Σ i, Slot M (T i) k := ⟨v.2.1, v.1, v.2.2⟩
  have hs := congrArg swap h
  have he : a = b := (p i).toSlot.injective (eq_of_heq (Sigma.mk.inj hs).2)
  rw [he]

private theorem covered (v : Σ l : Level k, Seats M T l)
    (hv : (Channels.packet (code row p) v).1 = true) : v ∈ Set.range (target row p) := by
  rcases v with ⟨l, i, t⟩
  have hr : (⟨l, t⟩ : Slot M (T i) k) ∈ Set.range (p i).toSlot := by
    by_contra h
    have he := unused row p i ⟨l, t⟩ h
    exact Bool.false_ne_true ((congrArg Prod.fst he).symm.trans hv)
  obtain ⟨j, hj⟩ := hr
  exact ⟨⟨i, j⟩, congrArg (fun s : Slot M (T i) k => (⟨s.1, i, s.2⟩ : Σ l : Level k, Seats M T l)) hj⟩

private def data (a : Source n) : Payload k :=
  let l := ((p a.1).toSlot a.2).1
  ⟨l, encodeToken l.val (row a.1 a.2).2.2⟩

private theorem packet_target (a : Source n) :
    Channels.packet (code row p) (target row p a) =
      (true, (row a.1 a.2).1, (row a.1 a.2).2.1, data row p a) := by
  simp only [Channels.packet, target, atSlot, data]

private theorem peer (a b : Source n) :
    Channels.packet (code row p) (target row p b) =
      (true, !(Channels.packet (code row p) (target row p a)).2.1,
        (Channels.packet (code row p) (target row p a)).2.2) ↔
    (true, row b.1 b.2) = (true, !(row a.1 a.2).1, (row a.1 a.2).2) := by
  have he : data row p b = data row p a ↔ (row b.1 b.2).2.2 = (row a.1 a.2).2.2 :=
    payload_eq ((p b.1).level b.2) ((p a.1).level a.2)
  simp only [packet_target, Prod.ext_iff, he]

/-- The global key is unaffected by bucketing, and a pair agrees on
the tagged token exactly when it agrees on the original bit string. -/
theorem good_iff : Channels.good (code row p) ↔
    Match.good (fun v : Σ i, Fin (n i) => (true, row v.1 v.2)) := by
  have active (a) : (Channels.packet (code row p) (target row p a)).1 = true := by
    rw [packet_target]
  constructor
  · rintro ⟨hu, hp⟩
    constructor
    · intro a b _ _ hd hk
      apply injective row p
      apply hu _ _ (active a) (active b)
      · simpa only [packet_target] using hd
      · simpa only [packet_target] using hk
    · intro a _
      obtain ⟨v, hv⟩ := hp _ (active a)
      obtain ⟨b, rfl⟩ := covered row p v (congrArg Prod.fst hv)
      exact ⟨b, (peer row p a b).mp hv⟩
  · rintro ⟨hu, hp⟩
    constructor
    · intro v w hv hw hd hk
      obtain ⟨a, rfl⟩ := covered row p v hv
      obtain ⟨b, rfl⟩ := covered row p w hw
      simp only [packet_target] at hd hk
      exact congrArg (target row p) (hu a b rfl rfl hd hk)
    · intro v hv
      obtain ⟨a, rfl⟩ := covered row p v hv
      obtain ⟨b, hb⟩ := hp a rfl
      exact ⟨target row p b, (peer row p a b).mpr hb⟩

theorem unique_layout (hm : ∀ i, n i ≤ M) (ht : ∀ i, ∑ j, callCharge (row i j).2.2 ≤ T i)
    (hk : ∀ i j, (row i j).2.2.length ≤ 2 ^ k) :
    ∃! p : Layout row M k T, Channels.good (code row p) ↔
      Match.good (fun v : Σ i, Fin (n i) => (true, row v.1 v.2)) := by
  let q : Layout row M k T := fun i => place _ (hm i) (ht i) (hk i)
  exact ⟨q, good_iff row q, fun z _ => funext fun i => place_unique _ (hm i) (ht i) (hk i) (z i)⟩

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings
end

/-! # Matching literal messages in the logical transcript -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Spec

variable {X : Type} {k H : ℕ} (S : Spec X k H)
    {n : S.Who → ℕ} (j : S.Who → Level k) (row : Strings.Rows S.key n)
    (f : (i : S.Who) → Fin (S.guesses i.1 (j i)) → Bool)

/-- Each tape occupies its least length class. Within a class the
original list order determines the occupied prefix. -/
theorem literal_messages (hm : ∀ i, n i ≤ S.messages)
    (ht : ∀ i, ∑ t, RAM.callCharge (row i t).2.2 ≤ 2 ^ (j i).val) :
    ∃! p : Strings.Layout row S.messages k (fun i => 2 ^ (j i).val),
      Channels.good (S.withStrings.declared (S.literal j row p f)) ↔
        Match.good (fun i : Σ s, Fin (n s) => (true, row i.1 i.2)) := by
  have bound (i : S.Who) (t : Fin (n i)) : (row i t).2.2.length ≤ 2 ^ k :=
    (le_max_right _ _).trans ((Finset.single_le_sum (f := fun t => RAM.callCharge (row i t).2.2)
      (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)).trans ((ht i).trans
        (Nat.pow_le_pow_right (by decide) (Nat.le_of_lt_succ (j i).isLt))))
  have he (p : Strings.Layout row S.messages k (fun i => 2 ^ (j i).val)) :
      S.withStrings.declared (S.literal j row p f) = Strings.code row p := by
    funext l i
    rcases i with ⟨⟨g, v⟩, t⟩
    dsimp only [declared, literal, message, Sum.elim_inr]
    exact (S.withStrings.Msg l).code.symm_apply_apply (Strings.code row p l ⟨⟨g, v⟩, t⟩)
  simp_rw [he]
  exact Strings.unique_layout row hm ht bound

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Spec
end

section
/-! # Decoding the ordered logical messages from slots and local ordinal bits -/

namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings

open RAM Coloring
open scoped Classical

variable {I : Type} {A : Format} {n T : I → ℕ} {M k : ℕ}

theorem unpack_encode (b : ℕ) (x : List Bool) (hx : x.length ≤ 2 ^ b) :
    unpack b (encodeToken b x) = x := by
  have hn : x.length < 2 ^ (b + 1) := lt_of_le_of_lt hx (by rw [pow_succ]; have := Nat.two_pow_pos b; omega)
  simp only [unpack, encodeToken, dite_eq_left hn]
  apply List.ext_getElem
  · simp [hx]
  · intro i h₁ h₂
    simp [h₂]

variable (row : Rows A n) (q : Layout row M k T) (hm : ∀ i, n i ≤ M)

theorem order_val (i : I) (s : Slot M (T i) k) :
    (order row q hm i s).val = ((q i).ordinal s).val := rfl

/-- Recovery includes the end of the original list. The decoder is not
given its length, and the sentinel on vacant seats never counts as a message. -/
theorem restore_code (i : I) (j : ℕ) :
    restore (code row q) (order row q hm) i j =
      if hj : j < n i then some (row i ⟨j, hj⟩) else none := by
  let P (s : Slot M (T i) k) := (code row q s.1 ⟨i, s.2⟩).1 = true ∧ (order row q hm i s).val = j
  by_cases hj : j < n i
  · let a : Fin (n i) := ⟨j, hj⟩
    let s := (q i).toSlot a
    have hs : P s := by
      refine ⟨congrArg Prod.fst (atSlot row q i a), ?_⟩
      rw [order_val, (q i).atSlot]
      rfl
    have he : ∃! t, P t := by
      refine ⟨s, hs, fun t ht => ?_⟩
      exact ((q i).fromSlot t a (Fin.ext ht.2)).symm
    have hc : he.choose = s := (he.choose_spec.2 s hs).symm
    have hb : (row i a).2.2.length ≤ 2 ^ s.1.val := by
      rw [(q i).level]
      exact (le_max_right _ _).trans (Nat.le_pow_clog (by decide) _)
    unfold restore
    rw [dite_eq_left hj, dite_eq_left he, hc]
    change some ((code row q s.1 ⟨i, s.2⟩).2.1, (code row q s.1 ⟨i, s.2⟩).2.2.1,
      unpack s.1.val (code row q s.1 ⟨i, s.2⟩).2.2.2) = some (row i a)
    rw [atSlot row q i a, unpack_encode _ _ hb]
  · have he : ¬∃! s, P s := by
      rintro ⟨s, ⟨hs, hj'⟩, _⟩
      have hn : s ∈ Set.range (q i).toSlot := by
        by_contra h
        rw [unused row q i s h] at hs
        exact Bool.false_ne_true hs
      obtain ⟨a, rfl⟩ := hn
      rw [order_val, (q i).atSlot] at hj'
      exact hj (hj' ▸ a.isLt)
    unfold restore
    rw [dite_eq_right hj, dite_eq_right he]

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol.Strings
end

/-! # Local factors for the sum over a physical tape -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
open Coloring
open scoped Classical

variable {X K : Type} [Field K] {k H U V : ℕ} (S : Spec X k H)

abbrev Spec.Factor (V : ℕ) := Level k ⊕ S.Site V ⊕ Level k ⊕ Unit ⊕ S.Site V

abbrev Spec.pins : S.Factor V → Type
  | .inl g => Private.Pins (Slot (S.P g) V k) (S.P g) H (S.supply g)
  | .inr (.inl _) => Unit ⊕ (Format.addr H).pins
  | .inr (.inr (.inl g)) => Slot (S.P g) V k × (Format.addr H).pins
  | .inr (.inr (.inr (.inl _))) => Channels.Pins S.key S.body (S.Reserved V)
  | .inr (.inr (.inr (.inr i))) => S.Input i.1 i.2.1

instance (i : S.Factor V) : Fintype (S.pins i) := by
  rcases i with g|i|g|u|i <;> unfold Spec.pins <;> infer_instance

variable {S} (D : System S U) (W : List Bool → K)

def System.check : (i : S.Factor V) → (S.pins i → Bool) → K
  | .inl g, x =>
    if Private.good (fun p => (S.supply g).code.symm (fun t => x (.inl (p, t))))
      (fun i => (Private.format (S.supply g) H).code.symm (fun t => x (.inr (i, t)))) then 1 else 0
  | .inr (.inl i), x =>
    if ((Format.addr H).code.symm (x ∘ Sum.inr)).val ≤ S.P i.1 ∧
      x (.inl ()) = decide (((Format.addr H).code.symm (x ∘ Sum.inr)).val < S.P i.1) then 1 else 0
  | .inr (.inr (.inl g)), x =>
    if ∀ j : Level k, Monotone (fun i : Fin (seats (S.P g) V j.val) =>
      (Format.addr H).code.symm (fun t => x (⟨j, i⟩, t))) then 1 else 0
  | .inr (.inr (.inr (.inl _))), x =>
    if Channels.good (Channels.decode S.key S.body (S.Reserved V) x) then 1 else 0
  | .inr (.inr (.inr (.inr i))), x => D.actor W i.1 i.2.1 x

end OAI.LinearAlgebra.MatrixExponent.Transcript.Protocol
end
