import OAI.Geometry.Hirsch.RawBits

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Coins

open Table

variable {Bit I Z : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I]
  {coin : Coins Bit} (raw : coin.Raw I) (place : I → Z) (site : Z)

theorem Raw.extra (s : Finset I) (f : Table Bit → Finset I) (N : ℕ) (hs : site ∉ s.image place)
    (hf : ∀ x, (f x).card ≤ N ∧ ∀ i ∈ f x, place i = site) :
    coin.two.prob (fun x => s ⊆ raw.pins.success x.1 ∧
      ∃ i ∈ f (raw.after place site x), i ∈ raw.pins.success x.1) ≤ N * raw.rate * raw.pins.weight s := by
  let A := raw.inSite place site
  let E := fun x : Table Bit × Table Bit => s ⊆ raw.pins.success x.1 ∧ ∃ i ∈ f x.1, i ∈ raw.pins.success x.2
  have hh : ∀ x : Table Bit × Table Bit, (s ⊆ raw.pins.success x.1 ∧
      ∃ i ∈ f (raw.after place site x), i ∈ raw.pins.success x.1) → E (swap A x) := by
    rintro x ⟨hp,i,hi,hm⟩
    have he : place i = site := (hf _).2 _ hi
    refine ⟨fun j hj => (raw.fixed place site x (fun h => hs (Finset.mem_image.mpr ⟨j,hj,h⟩))).mp (hp hj),
      i,hi,?_⟩
    rw [raw.mem] at hm ⊢
    intro b hb
    have ha : b ∈ A := ⟨i,he,hb⟩
    simpa [swap,Table.replace,ha] using hm b hb
  apply ((coin.two.mono hh).trans_eq (coin.preserve A E)).trans
  rw [Law.tensor_prob]
  have hb : ∀ x, coin.law.prob (fun y => E (x,y)) ≤ N * raw.rate * Law.ind (s ⊆ raw.pins.success x) := by
    intro x
    by_cases h : s ⊆ raw.pins.success x
    · have ht := raw.pins.extra ∅ (f x) (by simp)
      simp only [Pins.weight,Finset.card_empty,pow_zero,mul_one,Finset.empty_subset,true_and] at ht
      simp only [E,h,true_and,Law.ind,↓reduceIte,mul_one]
      exact ht.trans (mul_le_mul_of_nonneg_right (Nat.cast_le.mpr (hf x).1) raw.pos.le)
    · simp [E,h,Law.ind,Law.prob]
  apply (coin.law.mean_mono hb).trans_eq
  rw [Law.mean_scale,Law.mean_ind,raw.pins.prob]; rfl

structure Rules (raw : coin.Raw I) where
  barriers : I → Finset Bit
  separate : ∀ i j, Disjoint (barriers i) (raw.bits j)
  ok : I → Table Bit → Prop

namespace Rules

variable {raw place} (rule : Rules raw)

def pass (x : Table Bit) :=
  raw.pins.success x |>.filter (fun g => All (rule.barriers g) x ∧ rule.ok g x)

@[simp] theorem mem (x : Table Bit) (g : I) : g ∈ rule.pass x ↔
    g ∈ raw.pins.success x ∧ All (rule.barriers g) x ∧ rule.ok g x := Finset.mem_filter

def Compatible (place : I → Z) (s : Finset I) (g : I) :=
  (∀ j ∈ s, place j = place g) ∨ ∃ x, s ⊆ raw.pins.success x ∧ rule.ok g x

theorem Compatible.sub {rule : Rules raw} {s t : Finset I} {g : I}
    (h : rule.Compatible place s g) (ht : t ⊆ s) : rule.Compatible place t g := by
  rcases h with h | ⟨x,hx,hh⟩
  · exact .inl (fun j hj => h j (ht hj))
  · exact .inr ⟨x,ht.trans hx,hh⟩

structure Reliable (place : I → Z) (K : ℕ) (margin loss : ℝ) : Prop where
  pos : 0 < margin
  small : margin ≤ 1
  nonneg : 0 ≤ loss
  barriers : ∀ i, margin ≤ coin.weight (rule.barriers i)
  screen : ∀ g s, s.card ≤ K → rule.Compatible place s g → raw.pins.given (fun x => ¬rule.ok g x) s ≤ loss

omit [Fintype Bit] [DecidableEq Bit] [Fintype I] in
theorem barriers_keep (site : Z) (x : Table Bit × Table Bit) (g : I) :
    All (rule.barriers g) x.1 → All (rule.barriers g) (raw.after place site x) := by
  intro hh b hb
  have hn : b ∉ raw.inSite place site := by
    rintro ⟨j,_,hj⟩
    exact Finset.disjoint_left.mp (rule.separate g j) hb hj
  simpa [Raw.after,Table.replace,hn] using hh _ hb

variable {rule} {K : ℕ} {margin loss : ℝ} (hr : rule.Reliable place K margin loss)

include hr in
theorem Reliable.start {s : Finset I} (hk : s.card ≤ K) :
    margin^K * raw.pins.weight s ≤
      coin.law.prob (fun x => s ⊆ raw.pins.success x ∧ ∀ g ∈ s, All (rule.barriers g) x) := by
  let bars := s.biUnion rule.barriers
  have he : ∀ x, (s ⊆ raw.pins.success x ∧ ∀ g ∈ s, All (rule.barriers g) x) ↔
      All (bars ∪ raw.bitsOf s) x := by
    intro x
    change (s ⊆ raw.successes x ∧ _) ↔ _
    rw [raw.all]
    simp only [All,bars,Finset.mem_union,Finset.mem_biUnion]
    aesop
  rw [coin.law.eq_prob he,coin.all_prob]
  apply le_trans _ (coin.weight_union ..)
  rw [raw.cost]
  apply mul_le_mul_of_nonneg_right _ (raw.pins.positive s).le
  apply le_trans _ (coin.weight_many s rule.barriers)
  apply (pow_le_pow_of_le_one hr.pos.le hr.small hk).trans
  rw [← Finset.prod_const]
  exact Finset.prod_le_prod₀ (fun _ _ => hr.pos.le) (fun i _ => hr.barriers i)

end Rules
end OAI.Geometry.Hirsch.Layer.Coins
