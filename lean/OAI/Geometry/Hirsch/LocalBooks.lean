import OAI.Geometry.Hirsch.Relabel

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Network

variable {u : Dials} {I Ω : Type} [Fintype I] [Fintype Ω] {Q Q' : Network u I} {e : Equiv.Perm I}
  {p R S : ℕ} {r : Q.w.Round} {r' : Q'.w.Round} {i : I} {area : Set ℕ} {d : Bool}
  {law : Law Ω} {pins pins' : Pins law I} {K : ℕ} {gamma alpha : ℝ}
  {g : Trial.Gates pins Q.w.place K gamma alpha} {g' : Trial.Gates pins' Q'.w.place K gamma alpha}
  {f : Equiv.Perm Ω}

def Related (Q Q' : Network u I) (e : Equiv.Perm I) (p R : ℕ) (f : Equiv.Perm Ω)
    (a a' : Ω → Finset I) := ∀ i, Q.Agree Q' e p R i → ∀ x, i ∈ a x ↔ e i ∈ a' (f x)

omit [Fintype I] [Fintype Ω] in
theorem Related.symm {a a' : Ω → Finset I} (h : Q.Related Q' e p R f a a') :
    Q'.Related Q e.symm p R f.symm a' a := fun i hi x => by simpa using (h _ hi.symm (f.symm x)).symm

omit [Fintype I] [Fintype Ω] in
theorem Related.up {a a' : Ω → Finset I} (h : Q.Related Q' e p R f a a') (hle : R ≤ S) :
    Q.Related Q' e p S f a a' := fun i hi => h i (hi.cut hle)

omit [Fintype I] in
theorem left_eq {s : Finset I} (h : ∀ g ∈ s, Q.Agree Q' e p (R+1) g) :
    Q.w.left d s = Q'.w.left d (e.finsetCongr s) := by
  unfold left
  congr 1
  ext z
  constructor
  · rintro ⟨i,hi,hs,he⟩
    exact ⟨e i,by simpa using hi,((h _ hi).shore _).mp hs,((h _ hi).num _).symm.trans he⟩
  · rintro ⟨j,hj,hs,he⟩
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hj
    exact ⟨i,hi,((h _ hi).shore _).mpr hs,((h _ hi).num _).trans he⟩

namespace Matches

variable (m : Q.Matches Q' e p R r r') (hp : Q.Related Q' e p R f g.pass g'.pass)
  {a b : Budget} {s : Finset I}

include m hp in
theorem cut_map (hab : a ≤ b) (h : Q.Agree Q' e p (R+1+total u b) i)
    (hs : s ∈ g.cuts (r.test area d a i) (r.test area d b i)) :
    e.finsetCongr s ∈ g'.cuts (r'.test area d a (e i)) (r'.test area d b (e i)) ∧
      ∀ j ∈ s, Q.Agree Q' e p (R+1) j := by
  obtain ⟨hk,hc,hm,x,hx⟩ := g.mem_cuts.mp hs
  have cost : total u a ≤ total u b := Finset.sum_le_sum fun x _ => hab x
  have h' := h.cut (show R+1+total u a ≤ _ by omega)
  have hs := m.support (Nat.le_succ _) h' (Round.test_mono _ _ _ _ hab _ hc) hm
  refine ⟨g'.mem_cuts.mpr ⟨by simpa using hk,?_,m.minimal (Nat.le_succ _) h' hm,f x,?_⟩,hs⟩
  · exact (m.covers (Nat.le_succ _) h (fun _ _ => by simp)).mp hc
  intro j hj
  obtain ⟨k,hk,rfl⟩ := Finset.mem_map.mp hj
  exact (hp _ ((hs _ hk).cut (Nat.le_succ _)) x).mp (hx hk)

include m hp in
theorem cuts (hab : a ≤ b) (h : Q.Agree Q' e p (R+1+total u b) i) :
    e.finsetCongr.finsetCongr (g.cuts (r.test area d a i) (r.test area d b i)) =
      g'.cuts (r'.test area d a (e i)) (r'.test area d b (e i)) := by
  ext t
  constructor
  · intro hh
    obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp hh
    exact (m.cut_map hp hab h hs).1
  · intro ht
    have hs := (m.symm.cut_map hp.symm hab h.symm ht).1
    rw [e.symm_apply_apply,← Equiv.finsetCongr_symm] at hs
    exact Finset.mem_map.mpr ⟨_,hs,e.finsetCongr.apply_symm_apply t⟩

variable {D : Depths K} {M A : ℝ} {old : Q.w.Round} {old' : Q'.w.Round}
  (L : Ledger g old area d D M A) (L' : Ledger g' old' area d D M A)

def span (u : Dials) (D : Depths K) := 1+size u*D.max

theorem bound (u : Dials) {b : Budget} (hb : b ≤ flat D.max) : 1+total u b ≤ span u D :=
  Nat.add_le_add_left (total_le _ hb) 1

include m hp in
theorem band (h : Q.Agree Q' e p (R+span u D) i) :
    e.finsetCongr.finsetCongr (L.band r i) = L'.band r' (e i) := by
  have hD := D.order
  have hi := h.cut (show R+1 ≤ R+span u D by unfold span; omega)
  have he : L.depth i = L'.depth (e i) := by unfold Ledger.depth ahead; rw [hi.1]
  have hl : flat D.near ≤ L.depth i :=
    (show flat D.near ≤ flat D.band from fun _ => show D.near ≤ D.band by omega).trans (L.range_depth i).1
  have hh := bound u ((L.range_depth i).2.trans (show flat (D.band+1) ≤ flat D.max from fun _ => hD.2.2.2.2))
  unfold Ledger.band Ledger.book
  rw [← he]
  exact m.cuts hp hl (h.cut (by omega))

include hp in
theorem close_map (m : Q.Matches Q' e p R old old') (h : Q.Agree Q' e p (R+span u D) i)
    {z : ℕ} (hs : s ∈ L.close i z) : e.finsetCongr s ∈ L'.close (e i) z := by
  obtain ⟨hs,j,hj,ho,hl,hh⟩ := Finset.mem_filter.mp hs
  have hD := D.order
  have hb : flat (4*D.near) ≤ flat D.max := fun _ => show 4*D.near ≤ D.max by omega
  have h₁ := bound u hb
  have h₂ := Nat.le_mul_of_pos_right (size u) (by omega : 0 < D.max)
  have h' := h.cut (show R+1+size u ≤ R+span u D by unfold span; omega)
  have le : flat D.near ≤ flat (4*D.near) := fun _ => show D.near ≤ 4*D.near by omega
  obtain ⟨hs,hs'⟩ := m.cut_map hp le (h.cut (by omega)) hs
  have eq := (hs' _ hj).num d
  have eq' := (h'.cut (show R+1 ≤ _ by omega)).num d
  have he := left_eq (d := d) hs'
  exact Finset.mem_filter.mpr ⟨hs,e j,by simpa using hj,m.on ho h',by omega,by omega⟩

include hp in
theorem close (m : Q.Matches Q' e p R old old') (h : Q.Agree Q' e p (R+span u D) i) (z : ℕ) :
    e.finsetCongr.finsetCongr (L.close i z) = L'.close (e i) z := by
  ext t
  constructor
  · intro hh
    obtain ⟨s,hs,rfl⟩ := Finset.mem_map.mp hh
    exact close_map hp L L' m h hs
  · intro ht
    have hs := close_map hp.symm L' L m.symm h.symm ht
    rw [e.symm_apply_apply,← Equiv.finsetCongr_symm] at hs
    exact Finset.mem_map.mpr ⟨_,hs,e.finsetCongr.apply_symm_apply t⟩

end Matches
end OAI.Geometry.Hirsch.Layer.Board.Network
