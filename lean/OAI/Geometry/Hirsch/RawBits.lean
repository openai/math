import OAI.Geometry.Hirsch.Resampling

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Coins

open Table

variable {Bit I Z : Type} [DecidableEq Bit] (coin : Coins Bit)

omit [DecidableEq Bit] in
theorem weight_pos (s : Finset Bit) : 0 < coin.weight s := Finset.prod_pos (fun b _ => coin.pos b)

omit [DecidableEq Bit] in
theorem weight_le (s : Finset Bit) : coin.weight s ≤ 1 :=
  Finset.prod_le_one₀ (fun b _ => (coin.pos b).le) (fun b _ => coin.le_one b)

theorem weight_union (s t : Finset Bit) : coin.weight s * coin.weight t ≤ coin.weight (s ∪ t) := by
  have he : coin.weight (s ∪ t) * coin.weight (s ∩ t) = coin.weight s * coin.weight t :=
    Finset.prod_union_inter
  rw [← he]
  exact mul_le_of_le_one_right (coin.weight_pos _).le (coin.weight_le _)

theorem weight_many (s : Finset I) (f : I → Finset Bit) :
    ∏ i ∈ s, coin.weight (f i) ≤ coin.weight (s.biUnion f) := by
  induction s using Finset.induction_on with
  | empty => simp [weight]
  | insert i s hi ih =>
    rw [Finset.prod_insert hi,Finset.biUnion_insert]
    exact (mul_le_mul_of_nonneg_left ih (coin.weight_pos _).le).trans (coin.weight_union ..)

structure Raw (I : Type) where
  bits : I → Finset Bit
  rate : ℝ
  pos : 0 < rate
  weight : ∀ i, coin.weight (bits i) = rate
  unique : ∀ i j, i ≠ j → Disjoint (bits i) (bits j)

namespace Raw

variable {coin} (raw : coin.Raw I)

def bitsOf (s : Finset I) := s.biUnion raw.bits

theorem cost (s : Finset I) : coin.weight (raw.bitsOf s) = raw.rate^s.card := by
  unfold Coins.weight bitsOf
  rw [Finset.prod_biUnion (fun i _ j _ hn => raw.unique i j hn)]
  change (∏ i ∈ s, coin.weight (raw.bits i)) = _
  simp [raw.weight]

def inSite (place : I → Z) (site : Z) : Set Bit := {b | ∃ i, place i = site ∧ b ∈ raw.bits i}

omit [DecidableEq Bit] in
theorem belongs {place : I → Z} {site : Z} {i : I} {b : Bit} (hb : b ∈ raw.bits i) :
    b ∈ raw.inSite place site ↔ place i = site := by
  refine ⟨?_,fun h => ⟨i,h,hb⟩⟩
  rintro ⟨j,hj,hm⟩
  by_contra hn
  exact Finset.disjoint_left.mp (raw.unique i j (fun he => hn (he ▸ hj))) hb hm

variable [Fintype Bit] [Fintype I]

def successes (x : Table Bit) := Finset.univ.filter (fun i => All (raw.bits i) x)

omit [Fintype Bit] in
theorem all (s : Finset I) (x : Table Bit) : s ⊆ raw.successes x ↔ All (raw.bitsOf s) x := by
  simp only [successes,Finset.subset_iff,Finset.mem_filter,Finset.mem_univ,true_and]
  simp only [All,bitsOf,Finset.mem_biUnion]
  aesop

def pins : Pins coin.law I where
  rate := raw.rate
  pos := raw.pos
  success := raw.successes
  prob s := by rw [coin.law.eq_prob (raw.all s),coin.all_prob,raw.cost]

@[simp] theorem mem (i : I) (x : Table Bit) : i ∈ raw.pins.success x ↔ All (raw.bits i) x := by
  simp [pins,successes]

theorem reads (s : Finset I) : Reads (↑(raw.bitsOf s)) (fun x => s ⊆ raw.pins.success x) := by
  intro x y he
  exact (propext (raw.all s x)).trans ((reads_all _ _ _ he).trans (propext (raw.all s y)).symm)

theorem reads_site {place : I → Z} {site : Z} {s : Finset I} (hs : ∀ i ∈ s, place i = site) :
    Reads (raw.inSite place site) (fun x => s ⊆ raw.pins.success x) := by
  apply (raw.reads s).mono
  intro b hb
  obtain ⟨i,hi,hm⟩ := Finset.mem_biUnion.mp hb
  exact ⟨i,hs i hi,hm⟩

theorem reads_away {place : I → Z} {site : Z} {s : Finset I} (hs : ∀ i ∈ s, place i ≠ site) :
    Reads (raw.inSite place site)ᶜ (fun x => s ⊆ raw.pins.success x) := by
  apply (raw.reads s).mono
  intro b hb
  obtain ⟨i,hi,hm⟩ := Finset.mem_biUnion.mp hb
  exact fun hh => hs _ hi ((raw.belongs hm).mp hh)

variable (place : I → Z) (site : Z)

def after (x : Table Bit × Table Bit) := Table.replace (raw.inSite place site) x.1 x.2

theorem fixed (x : Table Bit × Table Bit) {g : I} (hg : place g ≠ site) :
    g ∈ raw.pins.success x.1 ↔ g ∈ raw.pins.success (raw.after place site x) := by
  have hh := (raw.reads_away (s := {g}) (place := place) (site := site) (by simp [hg])).keep x.1 x.2
  simpa only [Finset.singleton_subset_iff,after] using iff_of_eq hh.symm

theorem joint_after (s : Finset I) (event : Table Bit → Prop) :
    coin.two.prob (fun x => event (raw.after place site x) ∧ s ⊆ raw.pins.success x.1) =
      raw.pins.given event (s.filter (fun g => place g ≠ site)) * raw.pins.weight s := by
  let inside := s.filter fun g => place g = site
  let outside := s.filter fun g => place g ≠ site
  have he : outside ∪ inside = s := by ext; simp [inside,outside]; tauto
  have hd : Disjoint outside inside := Finset.disjoint_left.mpr fun _ h₁ h₂ =>
    (Finset.mem_filter.mp h₁).2 (Finset.mem_filter.mp h₂).2
  let E := fun x => event x ∧ outside ⊆ raw.pins.success x
  have eqn : ∀ x, (event (raw.after place site x) ∧ s ⊆ raw.pins.success x.1) ↔
      (E (raw.after place site x) ∧ inside ⊆ raw.pins.success x.1) := by
    intro x
    have ho := (raw.reads_away (s := outside) (fun _ hg => (Finset.mem_filter.mp hg).2)).keep x.1 x.2
    unfold E after
    rw [ho,← he,Finset.union_subset_iff,and_assoc]
  have hin := raw.reads_site (s := inside) (place := place) (site := site)
    (fun _ hg => (Finset.mem_filter.mp hg).2)
  rw [coin.two.eq_prob eqn]
  change coin.two.prob (fun x => E (Table.replace _ x.1 x.2) ∧ _) = _
  rw [coin.resample_both _ hin,raw.pins.prob]
  change raw.pins.joint event outside * raw.pins.weight inside =
    raw.pins.given event outside * raw.pins.weight s
  rw [← he,raw.pins.weight_union hd,Pins.given,← mul_assoc,div_mul_cancel₀ _ (raw.pins.positive _).ne']

end Raw
end OAI.Geometry.Hirsch.Layer.Coins
