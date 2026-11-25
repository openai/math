import OAI.Geometry.Hirsch.Tournament

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

variable {X : Type} {q K : ℝ}

def tally (q : ℝ) (l : List X) : Vec X →ₗ[ℝ] ℝ where
  toFun u := score q u l
  map_add' x y := by induction l <;> simp [score, *]; ring
  map_smul' a x := by induction l <;> simp [score, *]; ring

theorem score_mono (hq : 0 ≤ q) {u v : Vec X} (h : u ≤ v) (l : List X) :
    score q u l ≤ score q v l := by
  induction l with
  | nil => rfl
  | cons a l ih => exact add_le_add (h a) (mul_le_mul_of_nonneg_left ih hq)

theorem score_zero {u : Vec X} {l : List X} (hz : ∀ x ∈ l, u x = 0) : score q u l = 0 := by
  induction l with
  | nil => rfl
  | cons a l ih =>
    rw [score,hz a (by simp),ih (fun x hx => hz x (List.mem_cons_of_mem _ hx)),mul_zero,add_zero]

theorem score_bound (hq : 0 < q) (hh : q ≤ 1/2) (hk : 0 ≤ K) (n : ℕ) (C : ℝ) :
    ∃ D > 0, ∀ (u : Vec X), (∀ x, u x ≤ K) → ∀ l : List X, l.length = n →
      -C ≤ score q u l → ∀ x ∈ l, -D ≤ u x := by
  induction n generalizing C with
  | zero => exact ⟨1,one_pos,fun _ _ l he => by simp [List.length_eq_zero_iff.mp he]⟩
  | succ n ih =>
    obtain ⟨D,hd,hD⟩ := ih ((C+K)/q)
    refine ⟨max D (C+2*q*K),hd.trans_le (le_max_left ..),fun u hu l he hs x hx => ?_⟩
    cases l with
    | nil => simp at he
    | cons a l =>
      rw [score] at hs
      rcases List.mem_cons.mp hx with rfl | hx
      · linarith [mul_le_mul_of_nonneg_left (score_le hq.le hh hk hu l) hq.le,le_max_right D (C+2*q*K)]
      · have ht : -((C+K)/q) ≤ score q u l := by
          rw [← neg_div,div_le_iff₀ hq]
          linarith [hu a]
        exact (neg_le_neg (le_max_left ..)).trans (hD u hu l (by simpa using he) ht x hx)

structure Bundles (L V : ℕ) where
  r : ℕ
  X : Type
  [finite : Fintype X]
  idx : Type
  [indices : Fintype idx]
  game : Arena X (2^r)
  label : Fin L → idx → X → Fin V
  unique : ∀ s i j a b, label s i a = label s j b → i = j ∧ a = b

attribute [instance] Bundles.finite Bundles.indices

namespace Bundles

variable {L V : ℕ} (code : Bundles L V)

abbrev Chain := {w : Forest.Word code.X (code.r+1) //
  w.val.length = code.r+1 ∧ w.val.Pairwise code.game.before}

instance : Fintype code.Chain := Fintype.ofFinite _

abbrev Contest := Fin L × code.idx × code.Chain

def member (e : code.Contest) (l : Fin V) := ∃ a ∈ e.2.2.val.val, code.label e.1 e.2.1 a = l

def bid (q : ℝ) (e : code.Contest) : Values V →ₗ[ℝ] ℝ :=
  (tally q e.2.2.val.val).comp (LinearMap.funLeft ℝ ℝ (code.label e.1 e.2.1))

theorem bid_mono (hq : 0 ≤ q) (e : code.Contest) : Monotone (code.bid q e) :=
  fun _ _ hh => score_mono hq (fun a => hh (code.label e.1 e.2.1 a)) _

theorem bid_pos (hq : 0 < q) (e : code.Contest) : 0 < code.bid q e 1 :=
  score_pos hq (by intro he; have := e.2.2.property.1; simp [he] at this) (fun _ _ => one_pos)

theorem bid_zero {u : Values V} {e : code.Contest} (hz : ∀ l, code.member e l → u l = 0) :
    code.bid q e u = 0 := score_zero (fun a ha => hz _ ⟨a,ha,rfl⟩)

def Identifies (s : Fin L) (y : Values V) : Prop :=
  (∃ i, ∀ a, y (code.label s i a) = 0) ∧
  ∀ e : code.Contest, e.1 ≠ s → ∃ l, code.member e l ∧ y l ≠ 0

theorem select {s : Fin L} {y : Values V} (hy : code.Identifies s y)
    {delta : ℝ} (hq : 0 < q) (hh : q ≤ 1/2) (hk : 0 ≤ K) (hsmall : q*(2*K) ≤ delta/2)
    (u : Fin L → Values V) (hu : ∀ t l, u t l ≤ K)
    (feas : ∀ e, code.bid q e (u e.1) ≤ 0)
    (tight : ∀ e, code.bid q e (u e.1) = 0 → ∀ l, code.member e l → y l = 0) :
    ∃ l, y l = 0 ∧ u s l ≤ 0 ∧ (u s l < -delta/2 →
      ∀ e, code.member e l → code.bid q e (u e.1) < 0) := by
  obtain ⟨⟨i,hi⟩,hf⟩ := hy
  let v := fun a => u s (code.label s i a)
  have hs : ∀ w, w.length = code.r+1 → w.Pairwise code.game.before → score q v w ≤ 0 :=
    fun w hl hp => feas (s,i,⟨⟨w,hl.le⟩,hl,hp⟩)
  obtain ⟨a,ha,hl⟩ := code.game.select hq hh hk hsmall (fun a => hu s (code.label s i a)) hs
  refine ⟨code.label s i a,hi a,ha,fun hn e hm => ?_⟩
  by_cases he : e.1 = s
  · obtain ⟨t,j,w⟩ := e
    change t = s at he
    subst t
    obtain ⟨b,hb,hab⟩ := hm
    obtain ⟨rfl,rfl⟩ := code.unique s _ _ _ _ hab
    exact hl hn _ w.property.2 hb
  · obtain ⟨l,hm,hn⟩ := hf e he
    exact lt_of_le_of_ne (feas e) (fun he => hn (tight e he l hm))

theorem tight_bound (hq : 0 < q) (hh : q ≤ 1/2) (hk : 0 ≤ K) :
    ∃ D > 0, ∀ (e : code.Contest) (u : Values V), (∀ l, u l ≤ K) →
      code.bid q e u = 0 → ∀ l, code.member e l → -D ≤ u l := by
  obtain ⟨D,hd,hh⟩ := score_bound (X := code.X) hq hh hk (code.r+1) 0
  refine ⟨D,hd,fun e u hu he l ⟨a,ha,hl⟩ => ?_⟩
  rw [← hl]
  exact hh _ (fun x => hu (code.label e.1 e.2.1 x)) _ e.2.2.property.1
    (show -(0 : ℝ) ≤ code.bid q e u by simp [he]) _ ha

end Bundles
end OAI.Geometry.Hirsch.Layer
