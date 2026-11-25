import OAI.Geometry.Hirsch.Frequency

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer

namespace Law

variable {X Y : Type} [Fintype X] [Fintype Y]

def uniform (hx : 0 < Fintype.card X) : Law X where
  mass _ := (Fintype.card X : ℝ)⁻¹
  nonneg _ := by positivity
  total := by simp [hx.ne']

theorem sample (hx : 0 < Fintype.card X) (q : Law Y) (s : Finset X) {E : X × Y → Prop} {b : ℝ}
    (h : ∀ x ∈ s, b ≤ q.prob (fun y => E (x,y))) :
    s.card*b / Fintype.card X ≤ ((uniform hx).tensor q).prob E := by
  rw [tensor_prob]
  unfold mean
  calc
    _ = ∑ _ ∈ s, (Fintype.card X : ℝ)⁻¹*b := by simp; ring
    _ ≤ ∑ x ∈ s, (uniform hx).mass x * q.prob (fun y => E (x,y)) :=
      Finset.sum_le_sum fun x hx' => mul_le_mul_of_nonneg_left (h x hx') (by positivity)
    _ ≤ _ := Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ _)
      (fun _ _ _ => mul_nonneg ((uniform hx).nonneg _) (q.positive _))

end Law

namespace Board.Naming

variable (u : Dials)



abbrev Sample := Radii u × u.History u.h × Table (u.Cell (NodeName u))

theorem radii_pos : 0 < Fintype.card (Radii u) := by rw [Fintype.card_fin]; exact Npos u

theorem colors_pos : 0 < Fintype.card (u.History u.h) := by rw [u.card_history]; positivity

def law (v : u.Valid) : Law (Sample u) :=
  (Law.uniform (radii_pos u)).tensor ((Law.uniform (colors_pos u)).tensor v.coin.law)

end Board.Naming

namespace Board.Legs.Decoration

open Naming

variable {u : Dials} {X : Type} {L : Legs u X} (A : L.Decoration) (v : u.Valid) (z : Sample u)

def Pass (i : X) := ∃ Q : Network u (NodeName u),
  (A.active z.1).Agree Q (A.name z.1) (Naming.P u) (R u) i ∧ Q.passes v z.2.1 z.2.2 (A.name z.1 i)

def Occurs (i : X) := L.w.Middle i ∧ L.w.live i ∧
  (∀ a, Network.Enrolled u u.h z.2.1 a → A.Earn v a (block u (u.phase a) z.1) (L.w.step i (u.side a))) ∧
  ∀ d, A.Pass v z (L.w.step i d)

variable {A v z}

theorem Pass.propagate {i : X} (h : A.Pass v z i) {Q : Network u (NodeName u)}
    (hq : (A.active z.1).Agree Q (A.name z.1) (Naming.P u) (Network.window u) i) :
    Q.passes v z.2.1 z.2.2 (A.name z.1 i) := by
  obtain ⟨Q',hh,hp⟩ := h
  have hr : Network.window u ≤ R u := by unfold R; omega
  have agree := (hh.cut hr).compare (e := Equiv.refl _) hq (fun _ _ => rfl)
  have hs := (Network.local_pass v z.2.1 agree z.2.2).mp hp
  simpa only [Dials.tables_id,Equiv.refl_apply] using hs

theorem dense_bin (safe : A.Safe) (fixed : A.Fixed) (v : u.Valid) {i : X} (hm : L.w.Middle i)
    (hl : L.w.live i) {r : Radii u} (hr : A.Good (L.w.step i) r) :
    ∃ c : u.History u.h, u.gamma*(u.rate u.h)^2 ≤ v.coin.law.prob (fun x => A.Occurs v (r,c,x) i) := by
  obtain ⟨Q,hQ⟩ := hr.model safe
  let key := fun d => A.name r (L.w.step i d)
  obtain ⟨c,hc⟩ := Q.color v key _ le_rfl
  have hh : ∀ d, L.w.layer (L.w.step i d) = Q.w.layer (key d) :=
    fun d => ((hQ d).cut (show 1 ≤ R u by unfold R; omega)).1
  have place : Q.w.place (key false) = Q.w.place (key true) := by
    unfold Board.place; rw [← hh,← hh]
    exact (L.w.middle_step hm hl false).2.trans (L.w.middle_step hm hl true).2.symm
  have ne : key false ≠ key true := by
    intro he
    have := (hh false).trans ((congrArg Q.w.layer he).trans (hh true).symm)
    have := L.w.east _ hl
    have := L.w.west _ hl
    omega
  refine ⟨c,(Q.pair v c place ne).trans (v.coin.law.mono ?_)⟩
  intro x hx
  refine ⟨hm,hl,fun a ha => hr.earn fixed v a _ (hQ _) (hc a ha),fun d => ⟨Q,hQ d,?_⟩⟩
  cases d
  · exact hx.1
  · exact hx.2

theorem dense (safe : A.Safe) (fixed : A.Fixed) (v : u.Valid) {i : X} (hm : L.w.Middle i)
    (hl : L.w.live i) {chance : ℕ} (hch : 0 < chance)
    (hsize : 2*(u.count : ℝ) ≤ chance*u.gamma*(u.rate u.h)^2) :
    (chance : ℝ)⁻¹ ≤ (law u v).prob (fun z => A.Occurs v z i) := by
  let s := Finset.univ.filter (A.Good (L.w.step i))
  let q := (Law.uniform (colors_pos u)).tensor (v.coin (I := NodeName u)).law
  have hc : 0 < (chance : ℝ) := Nat.cast_pos.mpr hch
  have each : ∀ r ∈ s, 2/(chance : ℝ) ≤ q.prob (fun y => A.Occurs v (r,y) i) := by
    intro r hr
    obtain ⟨c,hh⟩ := dense_bin safe fixed v hm hl (Finset.mem_filter.mp hr).2
    have hb := Law.sample (colors_pos u) v.coin.law {c} (E := fun y => A.Occurs v (r,y) i)
      (b := u.gamma*(u.rate u.h)^2) (by simpa using hh)
    simp only [Finset.card_singleton,Nat.cast_one,one_mul] at hb
    apply le_trans _ hb
    rw [div_le_div_iff₀ hc (Nat.cast_pos.mpr (colors_pos u)),u.card_history]
    unfold Dials.count at hsize; linarith
  apply le_trans _ (Law.sample (radii_pos u) q s each)
  have large : (N u : ℝ) ≤ 2*s.card := by exact_mod_cast A.frequent (L.w.step i) fixed
  rw [le_div_iff₀ (Nat.cast_pos.mpr (radii_pos u)),Fintype.card_fin]
  rw [div_eq_mul_inv]; nlinarith only [mul_le_mul_of_nonneg_left large (inv_nonneg.mpr hc.le)]

end Board.Legs.Decoration
end OAI.Geometry.Hirsch.Layer
