import OAI.Geometry.Hirsch.JointGates

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Coins

open Table

variable {Bit I Z : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I]
  {coin : Coins Bit} {raw : coin.Raw I} {place : I → Z}
  {K : ℕ} {margin loss : ℝ}

namespace Rules

def initial (raw : coin.Raw I) : Rules raw where
  barriers _ := ∅
  separate _ _ := Finset.disjoint_empty_left _
  ok _ _ := True

theorem initial_reliable (raw : coin.Raw I) (place : I → Z) (K : ℕ) :
    (initial raw).Reliable place K 1 0 := by
  refine ⟨one_pos,le_rfl,le_rfl,fun _ => by simp [initial,weight],?_⟩
  intro g s _ _
  simp [initial,Pins.given,Pins.joint,Law.prob]

variable (rule : Rules raw) (thr : Thresholds K) (bad : I → Table Bit → Prop)

def screen : Rules raw :=
  { rule with ok := fun g x => rule.ok g x ∧ raw.pins.Screen thr (bad g) x }

theorem screen_pass (x : Table Bit) : (rule.screen thr bad).pass x ⊆ rule.pass x := by
  intro g hg
  obtain ⟨hp,hb,hs,_⟩ := (mem ..).mp hg
  exact (mem ..).mpr ⟨hp,hb,hs⟩

theorem reliable_screen (hr : rule.Reliable place K margin loss)
    (ignore : ∀ g s, s.card ≤ K → (∀ i ∈ s, place i = place g) → raw.pins.given (bad g) s ≤ thr.value 0) :
    (rule.screen thr bad).Reliable place K margin (loss + (1+4^K)*thr.value K) := by
  refine ⟨hr.pos,hr.small,?_,hr.barriers,fun g s hk hc => ?_⟩
  · have := thr.positive K
    exact add_nonneg hr.nonneg (by positivity)
  · have old : rule.Compatible place s g := hc.imp_right (fun ⟨x,hx,h,_⟩ => ⟨x,hx,h⟩)
    have compatible : raw.pins.Compatible thr (bad g) s := by
      rcases hc with hh | ⟨x,hx,_,hs⟩
      · exact fun t ht hk => (ignore g t hk (fun i hi => hh i (ht hi))).trans (thr.mono (by omega))
      · exact raw.pins.passes thr _ hs hx
    have h₁ := hr.screen g s hk old
    have h₂ := raw.pins.screen_cost thr (bad g) hk compatible
    rw [← Pins.cond_prob] at h₁ h₂ ⊢
    exact ((raw.pins.cond s).mono (fun _ h => not_and_or.mp h)).trans
      (((raw.pins.cond s).either _ _).trans (add_le_add h₁ h₂))

end Rules

namespace Raw

variable (raw fresh : coin.Raw I)

def Separate := ∀ i j, Disjoint (raw.bits i) (fresh.bits j)

def join (hd : raw.Separate fresh) : coin.Raw I where
  bits i := raw.bits i ∪ fresh.bits i
  rate := raw.rate * fresh.rate
  pos := mul_pos raw.pos fresh.pos
  weight i := by unfold Coins.weight; rw [Finset.prod_union (hd i i)]; exact congrArg₂ (· * ·) (raw.weight i) (fresh.weight i)
  unique i j h := by
    rw [Finset.disjoint_union_left,Finset.disjoint_union_right,Finset.disjoint_union_right]
    exact ⟨⟨raw.unique i j h,hd i j⟩,⟨(hd j i).symm,fresh.unique i j h⟩⟩

theorem join_success (hd : raw.Separate fresh) (x : Table Bit) :
    (raw.join fresh hd).pins.success x = raw.pins.success x ∩ fresh.pins.success x := by
  ext i
  simp only [Finset.mem_inter,mem,join,All,Finset.mem_union]
  aesop

theorem join_given (hd : raw.Separate fresh) (e : Table Bit → Prop)
    (he : Reads (↑(fresh.bitsOf Finset.univ))ᶜ e) (s : Finset I) :
    (raw.join fresh hd).pins.given e s = raw.pins.given e s := by
  let A : Set Bit := ↑(fresh.bitsOf Finset.univ)
  have hp : Reads Aᶜ (fun x => s ⊆ raw.pins.success x) := by
    apply (raw.reads s).mono
    intro b hb hh
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hb
    obtain ⟨j,_,hj⟩ := Finset.mem_biUnion.mp hh
    exact Finset.disjoint_left.mp (hd i j) hi hj
  have hq : Reads A (fun x => s ⊆ fresh.pins.success x) := by
    apply (fresh.reads s).mono
    intro b hb
    obtain ⟨i,_,hi⟩ := Finset.mem_biUnion.mp hb
    exact Finset.mem_biUnion.mpr ⟨i,Finset.mem_univ _,hi⟩
  have hi := coin.independent (e := fun x => e x ∧ s ⊆ raw.pins.success x)
    (fun x y h => congrArg₂ And (he x y h) (hp x y h)) hq
  unfold Pins.given Pins.joint
  simp only [join_success,Finset.subset_inter_iff,← and_assoc]
  rw [hi,fresh.pins.prob]
  change _ * fresh.rate^s.card / (raw.rate * fresh.rate)^s.card = _
  rw [mul_pow,mul_div_mul_right _ _ (pow_ne_zero _ fresh.pos.ne')]; rfl

end Raw

namespace Rules

variable {fresh : coin.Raw I} (rule : Rules raw) (hd : raw.Separate fresh)
  (bars : I → Finset Bit) (sep : ∀ i j, Disjoint (rule.barriers i ∪ bars i) ((raw.join fresh hd).bits j))

def next : Rules (raw.join fresh hd) where
  barriers i := rule.barriers i ∪ bars i
  separate := sep
  ok := rule.ok

theorem next_pass (x : Table Bit) (g : I) :
    g ∈ (rule.next hd bars sep).pass x ↔
      g ∈ rule.pass x ∧ g ∈ fresh.pins.success x ∧ All (bars g) x := by
  rw [mem,Raw.join_success,mem,Finset.mem_inter]
  simp only [next,All,Finset.mem_union]
  aesop

theorem reliable_next (hr : rule.Reliable place K margin loss)
    (hdep : ∀ g, Reads (↑(fresh.bitsOf Finset.univ))ᶜ (rule.ok g))
    {v : ℝ} (hv : 0 < v) (hv' : v ≤ 1) (hb : ∀ g, v ≤ coin.weight (bars g)) :
    (rule.next hd bars sep).Reliable place K (margin*v) loss := by
  refine ⟨mul_pos hr.pos hv,(mul_le_of_le_one_left hv.le hr.small).trans hv',hr.nonneg,fun i => ?_,fun g s hk hc => ?_⟩
  · exact (mul_le_mul (hr.barriers i) (hb i) hv.le (coin.weight_pos _).le).trans (coin.weight_union ..)
  · have old : rule.Compatible place s g := by
      rcases hc with hc | ⟨x,hx,hh⟩
      · exact .inl hc
      · rw [Raw.join_success] at hx
        exact .inr ⟨x,hx.trans Finset.inter_subset_left,hh⟩
    change (raw.join fresh hd).pins.given (fun x => ¬rule.ok g x) s ≤ loss
    rw [raw.join_given fresh hd _ (fun x y h => congrArg Not (hdep g x y h))]
    exact hr.screen g s hk old

end Rules
end OAI.Geometry.Hirsch.Layer.Coins
