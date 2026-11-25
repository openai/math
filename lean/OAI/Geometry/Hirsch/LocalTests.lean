import OAI.Geometry.Hirsch.Agreement

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Network

def size (u : Dials) := u.a^u.h*3

def total (u : Dials) (b : Budget) := ∑ j ∈ Finset.range (size u), b j

theorem total_le (u : Dials) {b : Budget} {k : ℕ} (h : b ≤ flat k) : total u b ≤ size u*k := by
  apply le_trans (Finset.sum_le_sum fun j _ => h j)
  simp [flat]

theorem total_spend {u : Dials} {b c : Budget} {j : ℕ} (hj : j < size u) (h : atLayer j + b ≤ c) :
    total u b + 1 ≤ total u c := by
  have hh := Finset.sum_le_sum (s := Finset.range (size u)) (fun i _ => h i)
  simp only [Pi.add_apply,Finset.sum_add_distrib,atLayer,Finset.sum_ite_eq',Finset.mem_range,hj,↓reduceIte] at hh
  exact (Nat.add_comm ..).le.trans hh

variable {u : Dials} {X Y : Type} {Q : Network u X} {Q' : Network u Y} {e : X ≃ Y}
  {p R S : ℕ} {r : Q.w.Round} {r' : Q'.w.Round} {i j : X} {area : Set ℕ} {d : Bool}
  {b : Budget} {l : List X}

namespace Matches

variable (m : Q.Matches Q' e p R r r')
include m

theorem trip (ht : r.Trip area i j b l) (hR : R ≤ S) (h : Q.Agree Q' e p (S+total u b) i) :
    r'.Trip area (e i) (e j) b (l.map e) ∧ Q.Agree Q' e p S j ∧ ∀ g ∈ l, Q.Agree Q' e p S g := by
  induction ht with
  | nil => exact ⟨.nil,h.cut (by omega),by simp⟩
  | @go i j k d b a path hi hm ha ht ih =>
    have cost := total_spend (u := u) (Q.w.bound i) ha
    have hh := h.cut (show S+total u a+1 ≤ S+total u b by omega)
    obtain ⟨hm',hj⟩ := m.step hm hh (by omega)
    obtain ⟨ht,hk,hg⟩ := ih hj
    have mark := m.mark _ (h.cut (by omega)) d
    have key := hh.2.2.1 d hm.1
    have charge : (r.charge i d).map e = r'.charge (e i) d := by
      simp only [Round.charge,mark]; split <;> simp [key.1]
    rw [List.map_append,charge]
    refine ⟨.go (hh.place ▸ hi) hm' (hh.1 ▸ ha) ht,hk,fun g h => ?_⟩
    rcases List.mem_append.mp h with h | h
    · rw [(r.charge_mem.mp h).2]; exact key.2.cut (by omega)
    · exact hg _ h

theorem test (ht : l ∈ r.test area d b i) (hR : R ≤ S+1) (h : Q.Agree Q' e p (S+1+total u b) i) :
    l.map e ∈ r'.test area d b (e i) ∧ ∀ g ∈ l, Q.Agree Q' e p (S+1) g := by
  obtain ⟨j,he,ht⟩ := ht
  obtain ⟨ht,hj,hg⟩ := m.trip ht hR h
  exact ⟨⟨e j,by simpa only [Round.Ends,hj.place,hj.2.1,hj.shore] using he,ht⟩,hg⟩

theorem covers {s : Finset X} {t : Finset Y} (hR : R ≤ S+1)
    (h : Q.Agree Q' e p (S+1+total u b) i)
    (hp : ∀ g, Q.Agree Q' e p (S+1) g → (g ∈ s ↔ e g ∈ t)) :
    (r.test area d b i).Covers s ↔ (r'.test area d b (e i)).Covers t := by
  constructor
  · intro hc l hl
    obtain ⟨hl',hh⟩ := m.symm.test hl hR h.symm
    rw [e.symm_apply_apply] at hl'
    obtain ⟨g,hg,hs⟩ := hc _ hl'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg
    have h' := (hp _ (hh j hj).symm).mp hs
    exact ⟨j,hj,by simpa using h'⟩
  · intro hc l hl
    obtain ⟨hl',hh⟩ := m.test hl hR h
    obtain ⟨g,hg,hs⟩ := hc _ hl'
    obtain ⟨j,hj,rfl⟩ := List.mem_map.mp hg
    exact ⟨j,hj,(hp _ (hh j hj)).mpr hs⟩

theorem minimal {s : Finset X} (hR : R ≤ S+1) (h : Q.Agree Q' e p (S+1+total u b) i)
    (hm : (r.test area d b i).Minimal s) : (r'.test area d b (e i)).Minimal (s.map e.toEmbedding) := by
  intro t ht hc
  let a := t.map e.symm.toEmbedding
  have sub : a ⊂ s := by
    apply Finset.ssubset_iff_subset_ne.mpr
    refine ⟨fun j hj => ?_,?_⟩
    · have : e j ∈ t := by simpa [a] using hj
      simpa using ht.subset this
    · intro he
      have := Finset.card_lt_card ht
      have := congrArg Finset.card he
      simp only [a,Finset.card_map] at *; omega
  exact hm a sub ((m.covers hR h (fun _ _ => by simp [a])).mpr hc)

theorem support {s : Finset X} (hR : R ≤ S+1) (h : Q.Agree Q' e p (S+1+total u b) i)
    (hc : (r.test area d b i).Covers s) (hm : (r.test area d b i).Minimal s) :
    ∀ g ∈ s, Q.Agree Q' e p (S+1) g := by
  intro g hg
  obtain ⟨l,t,hh,_⟩ := hm.essential hc hg
  exact (m.test hh hR h).2 _ (by simp)

theorem on (ho : r.On area d i j) (h : Q.Agree Q' e p (R+1+size u) i) : r'.On area d (e i) (e j) := by
  obtain ⟨v,hr,hv,hm,rfl⟩ := ho
  have ray : ∀ i, Q.w.Ray area d i v → Q.Agree Q' e p (R+1+(Q.w.loc d v-Q.w.loc d i)) i →
      Q'.w.Ray area d (e i) (e v) ∧ Q.Agree Q' e p (R+1) v := by
    clear hr hv hm
    intro i ht
    induction ht with
    | self => exact fun h => ⟨.self,h.cut (by omega)⟩
    | @go i j hi hl ht ih =>
      intro h
      have := ht.forward
      have := Q.w.loc_step d hl
      have hh := h.cut (show R+1+(Q.w.loc d j-Q.w.loc d (Q.w.step i d))+1 ≤ _ by omega)
      obtain ⟨he,hj⟩ := hh.2.2.1 d hl
      obtain ⟨ht,hv⟩ := ih hj
      exact ⟨.go (hh.place ▸ hi) (hh.2.1.mp hl) (he ▸ ht),hv⟩
  have small : Q.w.loc d v ≤ size u := by
    have := Q.w.bound v
    unfold size loc; split <;> omega
  obtain ⟨ht,hh⟩ := ray _ hr (h.cut (by omega))
  exact ⟨e v,ht,hh.place ▸ hv,(m.mark _ (hh.cut (by omega)) _).mp hm,(hh.2.2.1 _ (r.middle _ _ hm).2).1.symm⟩

end Matches
end OAI.Geometry.Hirsch.Layer.Board.Network
