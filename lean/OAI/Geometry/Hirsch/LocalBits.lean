import OAI.Geometry.Hirsch.Screening

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Coins.Raw

open Table

variable {Bit I : Type} [Fintype Bit] [DecidableEq Bit] [Fintype I]
  {coin : Coins Bit} (raw : coin.Raw I)

def force (s : Finset I) (x : Table Bit) := Table.replace (↑(raw.bitsOf s)) x (fun _ => true)

theorem forced (s : Finset I) (e : Table Bit → Prop) :
    coin.law.prob (fun x => e (raw.force s x)) = raw.pins.given e s := by
  let A : Set Bit := ↑(raw.bitsOf s)
  have fixed : ∀ x, s ⊆ raw.pins.success x → raw.force s x = x := by
    intro x hx
    have hh := (raw.all s x).mp hx
    funext b
    by_cases hb : b ∈ raw.bitsOf s
    · simp [force,Table.replace,hb,hh b hb]
    · simp [force,Table.replace,hb]
  have free : Reads Aᶜ (fun x => e (raw.force s x)) := by
    intro x y hh
    apply congrArg e
    funext b
    by_cases hb : b ∈ raw.bitsOf s
    · simp [force,Table.replace,hb]
    · simp [force,Table.replace,hb,hh (show b ∈ Aᶜ from hb)]
  have hi := coin.independent free (raw.reads s)
  apply (eq_div_iff (raw.pins.positive s).ne').mpr
  change _ * raw.pins.rate^s.card = _
  rw [← raw.pins.prob,← hi]
  apply coin.law.eq_prob
  intro x
  by_cases hh : s ⊆ raw.pins.success x
  · simp only [fixed _ hh]
  · simp [hh]

theorem given_restrict {e : Table Bit → Prop} {A : Set Bit} (he : Reads A e) (keys : Finset I)
    (hk : ∀ j ∉ keys, ∀ b ∈ raw.bits j, b ∉ A) (s : Finset I) :
    raw.pins.given e s = raw.pins.given e (s ∩ keys) := by
  rw [← forced,← forced]
  apply coin.law.eq_prob
  intro x
  apply iff_of_eq
  apply he
  intro b hb
  have same : b ∈ raw.bitsOf s ↔ b ∈ raw.bitsOf (s ∩ keys) := by
    simp only [bitsOf,Finset.mem_biUnion,Finset.mem_inter]
    exact ⟨fun ⟨j,hj,hm⟩ => ⟨j,⟨hj,by_contra (fun hn => hk j hn b hm hb)⟩,hm⟩,
      fun ⟨j,hj,hm⟩ => ⟨j,hj.1,hm⟩⟩
  simp only [force,Table.replace,Finset.mem_coe,same]

theorem screen_restrict {e : Table Bit → Prop} {A : Set Bit} (he : Reads A e) (keys : Finset I)
    (hk : ∀ j ∉ keys, ∀ b ∈ raw.bits j, b ∉ A) {K : ℕ} (thr : Thresholds K) (x : Table Bit) :
    raw.pins.Screen thr e x ↔ ¬e x ∧ raw.pins.Compatible thr e (raw.pins.success x ∩ keys) := by
  refine ⟨fun h => ⟨h.1,raw.pins.passes thr e h Finset.inter_subset_left⟩,fun ⟨hn,hc⟩ => ⟨hn,?_⟩⟩
  intro s hs hm
  have hh := Finset.card_le_card (Finset.inter_subset_left : s ∩ keys ⊆ s)
  rw [raw.given_restrict he keys hk]
  exact (hc _ (Finset.inter_subset_inter hs Finset.Subset.rfl) (hh.trans hm)).trans (thr.mono hh)

theorem reads_screen {e : Table Bit → Prop} {A : Set Bit} (he : Reads A e)
    (whole : ∀ j b, b ∈ raw.bits j → b ∈ A → ↑(raw.bits j) ⊆ A) {K : ℕ} (thr : Thresholds K) :
    Reads A (raw.pins.Screen thr e) := by
  let keys := Finset.univ.filter (fun j => ↑(raw.bits j) ⊆ A)
  have hk : ∀ j ∉ keys, ∀ b ∈ raw.bits j, b ∉ A := by
    intro j hj b hb hm
    exact hj (Finset.mem_filter.mpr ⟨Finset.mem_univ _,whole j b hb hm⟩)
  intro x y hh
  have same : raw.pins.success x ∩ keys = raw.pins.success y ∩ keys := by
    ext j
    by_cases hj : j ∈ keys
    · have hv := ((reads_all (raw.bits j)).mono (Finset.mem_filter.mp hj).2) x y hh
      simp only [Finset.mem_inter,hj,and_true,mem,hv]
    · simp [hj]
  apply propext
  rw [raw.screen_restrict he keys hk,raw.screen_restrict he keys hk,same,he x y hh]

end OAI.Geometry.Hirsch.Layer.Coins.Raw
