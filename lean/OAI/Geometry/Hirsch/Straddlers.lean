import OAI.Geometry.Hirsch.Switch

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Ledger

theorem scale_exists {a x h : ℕ} (hx : 0 < x) (hb : x < a^h) :
    ∃ j : Fin h, a^j.val ≤ x ∧ x < a*a^j.val := by
  induction h with
  | zero => simp at hb; omega
  | succ h ih =>
    by_cases he : x < a^h
    · obtain ⟨j,hj⟩ := ih he
      exact ⟨j.castSucc,hj⟩
    · exact ⟨Fin.last h,Nat.le_of_not_gt he,by simpa [pow_succ'] using hb⟩

abbrev Box (a h : ℕ) := Fin h × Fin (4*a) × Fin (4*a)

def Box.fits {a h : ℕ} (box : Box a h) (l v r : ℕ) :=
  let s := a^box.1.val
  l+s ≤ r ∧
  4*l + box.2.1.val*s ≤ 4*v ∧ 4*v ≤ 4*l + box.2.1.val*s+s ∧
  4*v + box.2.2.val*s ≤ 4*r ∧ 4*r ≤ 4*v + box.2.2.val*s+s

theorem Box.exists_fits {a h l v r : ℕ} (ha : 0 < a) (hl : l ≤ v) (hr : v < r) (hn : r < a^h) :
    ∃ box : Box a h, box.fits l v r := by
  obtain ⟨j,hj,he⟩ := scale_exists (a := a) (h := h) (x := r-l) (by omega) (by omega)
  let s := a^j.val
  have hs : 0 < s := pow_pos ha _
  have choose : ∀ k ≤ r-l, ∃ z : Fin (4*a), z.val*s ≤ 4*k ∧ 4*k ≤ z.val*s+s := by
    intro k hk
    have small : 4*k < (4*a)*s := by rw [mul_assoc]; change r-l < a*s at he; omega
    have hb := Nat.div_mul_le_self (4*k) s
    have hmod := Nat.mod_lt (4*k) hs
    have hid := Nat.mod_add_div (4*k) s
    rw [mul_comm s] at hid
    exact ⟨⟨4*k/s,(Nat.div_lt_iff_lt_mul hs).mpr small⟩,hb,by dsimp; omega⟩
  obtain ⟨p,hp,hp'⟩ := choose (v-l) (by omega)
  obtain ⟨q,hq,hq'⟩ := choose (r-v) (by omega)
  refine ⟨(j,p,q),?_⟩
  dsimp only [fits,s] at *
  omega

variable {I Ω : Type} [Fintype Ω] [Fintype I] {p : Law Ω} {pins : Pins p I}
  {n K : ℕ} {w : Board I n} {gamma alpha : ℝ} {gate : Trial.Gates pins w.place K gamma alpha}
  {old r : w.Round} {area : Set ℕ} {d : Bool} {D : Depths K} {M A : ℝ}
  (L : Ledger gate old area d D M A)

def colors (a h : ℕ) (theta : ℝ) (i : I) (j : Fin h) : Bool :=
  decide (theta ≤ pins.mass (L.close i (a^j.val)))

def factor (a h : ℕ) : ℝ := 1 + 9*Fintype.card (Box a h)

def remaining (r : w.Round) (area : Set ℕ) (d : Bool) (i : I) (s : Finset I) :=
  s.filter fun g => w.num d g ≤ r.right d s area i

omit [Fintype I] in
theorem drops {i y : I} {s : Finset I} (hs : r.Straddles d s area i)
    (h : r.right d s area y < r.right d s area i) :
    (remaining r area d y s).card < (remaining r area d i s).card := by
  apply Finset.card_lt_card
  apply Finset.ssubset_iff_subset_ne.mpr
  constructor
  · intro g hg
    obtain ⟨hg,hg'⟩ := Finset.mem_filter.mp hg
    exact Finset.mem_filter.mpr ⟨hg,hg'.trans h.le⟩
  · intro he
    obtain ⟨g,hg,_,he'⟩ := hs.endpoint
    have hh : g ∈ remaining r area d i s := Finset.mem_filter.mpr ⟨hg,he'.le⟩
    rw [← he] at hh
    exact h.not_ge (he' ▸ (Finset.mem_filter.mp hh).2)

theorem straddlers (hr : r.Finer old) {a h : ℕ} (ha : 0 < a) (hn : n ≤ a^h)
    {theta : ℝ} (hth : 0 < theta) (hbeta : 3*L.beta < theta^2) (herr : L.key+L.loss ≤ theta)
    {color : Fin h → Bool} (link : r.Links d (fun u => w.place u ∈ area → L.colors a h theta u = color))
    {i : I} (hi : w.place i ∈ area) (he : w.Shore d i) :
    pins.mass ((L.book r i (flat D.limit)).filter (fun s => r.Straddles d s area i)) ≤ factor a h ^ K * theta := by
  have hF : 1 ≤ factor a h := by unfold factor; exact le_add_of_nonneg_right (by positivity)
  have aux : ∀ k i, w.place i ∈ area → w.Shore d i → ∀ B ⊆ L.book r i (flat ((3*k+6)*D.near)),
      (∀ s ∈ B, r.Straddles d s area i ∧ (remaining r area d i s).card ≤ k) →
      pins.mass B ≤ factor a h ^ k * theta := by
    intro k
    induction k with
    | zero =>
      intro i _ _ B _ hB
      have empty : B = ∅ := Finset.eq_empty_iff_forall_notMem.mpr (by
        intro s hs
        obtain ⟨hs,hk⟩ := hB s hs
        obtain ⟨g,hg,_,he⟩ := hs.endpoint
        have hh : (remaining r area d i s).Nonempty := ⟨g,Finset.mem_filter.mpr ⟨hg,he.le⟩⟩
        exact hh.card_pos.not_ge hk)
      simp [empty,Pins.mass,hth.le]
    | succ k ih =>
      intro i hi he B hB hb
      let f := (3*(k+1)+6)*D.near
      have hf : 9*D.near ≤ f := Nat.mul_le_mul_right _ (by omega)
      have heq : f-3*D.near = (3*k+6)*D.near := by
        have : f = (3*k+6)*D.near + 3*D.near := by unfold f; ring
        omega
      let group := fun box : Box a h => B.filter fun s => box.fits (w.left d s) (w.num d i) (r.right d s area i)
      have split : pins.mass B ≤ ∑ box, pins.mass (group box) := by
        apply pins.mass_cover
        intro s hs
        have cov := (L.mem.mp (hB hs)).2.1
        have h₁ := (Round.west hi (show flat 1 ≤ flat f from fun _ => by
          have := D.order.2.1; simp only [flat]; omega) cov).1
        have h₂ := (hb _ hs).1.greater he
        obtain ⟨g,_,_,hg⟩ := (hb _ hs).1.endpoint
        obtain ⟨box,hbox⟩ := Box.exists_fits ha h₁ h₂ (hg ▸ (w.num_lt d g).trans_le hn)
        exact ⟨box,Finset.mem_univ _,Finset.mem_filter.mpr ⟨hs,hbox⟩⟩
      have low : theta ≤ factor a h^k * theta := le_mul_of_one_le_left hth.le (one_le_pow₀ hF)
      have each : ∀ box : Box a h, pins.mass (group box) ≤ 9*(factor a h^k*theta) := by
        intro box
        let scale := a^box.1.val
        have sub : group box ⊆ B := Finset.filter_subset ..
        have hc : L.Cohort r i scale (group box) := by
          refine ⟨fun s hs => ⟨(hb _ (sub hs)).1,(Finset.mem_filter.mp hs).2.1⟩,?_⟩
          intro s hs t ht
          have lhs := (Finset.mem_filter.mp hs).2
          have rhs := (Finset.mem_filter.mp ht).2
          unfold Box.fits at lhs rhs
          dsimp only [scale] at *
          omega
        by_cases hm : 3*(theta+L.loss) ≤ pins.mass (group box)
        swap
        · linarith [L.positive.2.1]
        obtain ⟨y,C,hy,hey,hsub,hcov,hkeep,hdrop⟩ :=
          L.shift hr hi hf (sub.trans hB) hc (pow_pos ha _) hth hbeta hm link (by
            intro u y hui hyi hu hy
            have eq := congrFun ((hu hui).trans (hy hyi).symm) box.1
            intro hu'
            have he : L.colors a h theta u box.1 = true := decide_eq_true hu'
            exact of_decide_eq_true (eq.symm.trans he))
        rw [heq] at hcov
        have high := ih y hy hey C hcov (by
          intro s hs
          obtain ⟨hold,hk⟩ := hb _ (sub (hsub hs))
          obtain ⟨hnew,hlt⟩ := hdrop _ hs
          exact ⟨hnew,Nat.lt_succ_iff.mp ((drops hold hlt).trans_le hk)⟩)
        linarith
      calc
        _ ≤ ∑ box, pins.mass (group box) := split
        _ ≤ ∑ _ : Box a h, 9*(factor a h^k*theta) := Finset.sum_le_sum fun b _ => each b
        _ ≤ _ := by
          simp only [Finset.sum_const,Finset.card_univ,nsmul_eq_mul,pow_succ]
          have he : factor a h = 1 + 9*Fintype.card (Box a h) := rfl
          calc
            _ ≤ (factor a h)*(factor a h^k*theta) := by
              rw [← mul_assoc]; gcongr; linarith
            _ = _ := by ring
  apply aux K i hi he _ (Finset.filter_subset ..)
  intro s hs
  obtain ⟨hs,hstr⟩ := Finset.mem_filter.mp hs
  exact ⟨hstr,(Finset.card_filter_le ..).trans (L.mem.mp hs).1⟩

end OAI.Geometry.Hirsch.Layer.Board.Ledger
