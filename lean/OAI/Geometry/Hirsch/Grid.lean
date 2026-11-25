import OAI.Geometry.Hirsch.Hitting

noncomputable section

namespace OAI.Geometry.Hirsch.Layer.World

variable {X : Type} {n : ℕ} (w : World X n)

def Blank (width : ℕ) (x : X) := width ∣ w.layer x ∨ width ∣ w.layer x + 1

def block (width : ℕ) (x : X) := w.layer x / width

theorem blank_mono {a b : ℕ} (hab : a ∣ b) {x : X} (hx : w.Blank b x) : w.Blank a x :=
  hx.imp hab.trans hab.trans

theorem boundary {x : X} (hx : w.Blank n x) : ¬ w.live x := by
  intro hl
  have h₁ := w.west x hl
  have h₂ := w.east x hl
  have h₃ := w.bound (w.step x true)
  rcases hx with hx | hx <;> have := Nat.le_of_dvd (by omega) hx <;> omega

theorem blank_micro {L k : ℕ} {s : Fin L} {j : Fin k} {x : X} (hx : w.layer x = micro s j) :
    ¬w.Blank (k+2) x := by
  unfold Blank
  rw [hx,micro]
  simp only [add_assoc,Nat.dvd_iff_mod_eq_zero,Nat.mul_add_mod_self_right]
  rw [Nat.mod_eq_of_lt (by omega : 1+j.val < k+2),Nat.mod_eq_of_lt (by omega : 1+(j.val+1) < k+2)]
  omega

theorem parent (width base : ℕ) (x : X) :
    w.block (width*base) x = w.block width x / base := (Nat.div_div_eq_div_mul ..).symm

theorem same_step {width : ℕ} {x : X} (hl : w.live x) (hn : ¬w.Blank width x) (d : Bool) :
    w.block width (w.step x d) = w.block width x := by
  have hs : ∀ a : ℕ, ¬ width ∣ a+1 → (a+1)/width = a/width := by
    intro a ha
    exact Nat.succ_div_of_not_dvd ha
  cases d
  · unfold block
    have hw := w.west x hl
    rw [← hw]
    exact (hs _ (fun h => hn (Or.inl (hw ▸ h)))).symm
  · unfold block
    rw [w.east x hl]
    exact hs _ (fun h => hn (Or.inr h))

theorem spine (width : ℕ) (d : Bool) : ∀ x,
    w.Walk (fun y => w.block width y = w.block width x)
      (fun y => ¬w.live y ∨ w.Blank width y) x d 0 := by
  apply w.induct
  intro x ih
  by_cases hl : w.live x
  swap
  · exact .done rfl (.inl hl)
  by_cases hb : w.Blank width x
  · exact .done rfl (.inr hb)
  have ht := ih hl d
  rw [w.same_step hl hb d] at ht
  exact .go rfl hl (by simp [turn]) ht

theorem Walk.endpoint {w : World X n} {ok stop : X → Prop} {x d k} (hw : w.Walk ok stop x d k) :
    ∃ y, ok y ∧ stop y ∧ w.Walk ok (· = y) x d k := by
  induction hw with
  | done hg hl => exact ⟨_,hg,hl,.done hg rfl⟩
  | go hg hl hb _ ih =>
    obtain ⟨y,hy,hs,ht⟩ := ih
    exact ⟨y,hy,hs,.go hg hl hb ht⟩

def digit (width base : ℕ) [NeZero base] (x : X) : Fin base :=
  ⟨w.block width x % base,Nat.mod_lt _ (NeZero.pos base)⟩

theorem index_inj {width base : ℕ} [NeZero base] {x y : X}
    (hp : w.block (width*base) x = w.block (width*base) y)
    (hd : w.digit width base x = w.digit width base y) : w.block width x = w.block width y := by
  rw [parent,parent] at hp
  have hm : w.block width x % base = w.block width y % base := congrArg Fin.val hd
  exact (Nat.mod_add_div _ _).symm.trans (by rw [hp,hm,Nat.mod_add_div])

structure Potential {Ω : Type} [Fintype Ω] (p : Law Ω) (chance D width base : ℕ) where
  sets : X → Set Ω
  dense : ∀ x, ¬w.Blank width x → (chance : ℝ)⁻¹ ≤ p.prob (· ∈ sets x)
  path : ∀ x, w.Blank width x → ∀ a : Ω, ∃ j ≠ w.block width x,
    w.Walk (fun y => w.block (width*base) y = w.block (width*base) x ∧
      (a ∈ sets y → w.block width y = j))
      (fun y => ¬w.live y ∨ w.Blank (width*base) y) x false D

end OAI.Geometry.Hirsch.Layer.World
