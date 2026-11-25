import OAI.Geometry.Hirsch.Outputs

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

open Forest

variable {I : Type} {L V h B : ℕ} {code : Bundles L V}
  {tree : Forest I (Fin V) h} {net : Network tree code} {b : Fin B}

structure Scene (net : Network tree code) (b : Fin B) where
  data : ∀ i, tree.depth i < h → SampleData (net.par i)
  z : I → Values V
  p : I → Values V
  out : ∀ i, Position V → net.Track i B
  feasible : ∀ i hi, (data i hi).Prices (z i) (p i)
  cost : ∀ i hi, (data i hi).cost (p i) = net.cost i
  raised : ∀ i pos d, 0 ≤ (out i pos).red d ∧ (out i pos).red d ≤ (out i pos).val (tree.depth i) d
  first : ∀ i, tree.depth i < h → ∀ l d, d ≠ b → z i l ≤ (out i (false,l)).val 0 d
  second : ∀ i, tree.depth i < h → ∀ l d, d ≠ b →
    (net.par i).eps * (net.cost i l + (net.par i).lam) ≤ (out i (true,l)).val 0 d
  firstGap : ∀ i, tree.depth i < h → ∀ l, (out i (false,l)).gap 0 = (net.par i).mu
  secondGap : ∀ i, tree.depth i < h → ∀ l, (out i (true,l)).gap 0 = (net.par i).allow
  leaf : ∀ i, ¬ tree.depth i < h → ∀ pos d, d ≠ b → (out i pos).gap 0 < (out i pos).val 0 d

namespace Scene

variable (scene : Scene net b)

def hits : Set I := {i | ∃ pos, (scene.out i pos).Hit b}

def Quiet (dir : Space I B V) (i : I) : Prop :=
  Silent dir i ∨
  (∃ hi : tree.depth i < h, ∃ w v f g, (scene.data i hi).Motion (scene.z i) (scene.p i) w v f g ∧
    dir = impulse i b w v f g ∧ ∀ pos, 0 < (scene.out i pos).val 0 b) ∨
  (¬ tree.depth i < h ∧ ∃ f, dir = impulse i b 0 0 f 0)

def speed (net : Network tree code) (dir : Space I B V) (i : I) (pos : Position V) (k : ℕ) (d : Fin B) :=
  output tree (fun j => (net.par j).eps) i pos d k dir

def Stationary (dir : Space I B V) : Prop :=
  (∀ i, scene.Quiet dir i) ∧ ∀ i pos k, k ≤ tree.depth i → ∀ d,
    speed net dir i pos k d ≠ 0 → (scene.out i pos).Safe k d

def Extreme (usable : Set (Port I B V)) : Prop :=
  ∀ dir ∈ supported usable, scene.Stationary dir → dir = 0

theorem safe_start {i : I} (hg : net.Good (tree.path i)) (hn : i ∉ scene.hits) (pos : Position V)
    (other : ∀ d, d ≠ b → (scene.out i pos).gap 0 < (scene.out i pos).val 0 d) (d : Fin B) :
    (scene.out i pos).Safe 0 d := by
  let tr := scene.out i pos
  refine ⟨hg,?_,fun e he => ?_⟩
  · by_cases hd : d = b
    · exact .inr (fun hh => hn ⟨pos,hd ▸ hh⟩)
    · exact .inl ((tr.gapLow 0 (by omega)).trans_lt (other d hd))
  · by_cases hd : d = b
    · exact (other e (hd ▸ he.symm)).trans_le (le_add_of_nonneg_left (tr.floor 0 (by omega) d))
    · exact (other d hd).trans_le (le_add_of_nonneg_right (tr.floor 0 (by omega) e))

theorem stationary {i : I} {w v f g : Values V} (hg : net.Good (tree.path i))
    (hq : scene.Quiet (impulse i b w v f g) i)
    (low : ∀ l, net.cost i l ≤ (net.par i).lam/4 → v l = 0)
    (start : ∀ pos d, quick tree i pos d (impulse i b w v f g) ≠ 0 → (scene.out i pos).Safe 0 d) :
    scene.Stationary (impulse i b w v f g) := by
  let dir := impulse i b w v f g
  have silent : ∀ j ≠ i, Silent dir j := fun j hj => impulse.other _ _ _ _ _ _ hj
  constructor
  · intro j
    by_cases hj : j = i
    · exact hj.symm ▸ hq
    · exact .inl (silent j hj)
  · intro j pos
    apply Network.Track.safe_run _ _ (fun a l => P a l dir)
    · intro d hn
      by_cases he : j = i
      · subst j; exact start pos d hn
      · exact (hn ((silent j he).quick tree pos d)).elim
    · intro a l hn
      by_cases he : a = i
      · subst a
        exact ⟨hg,lt_of_not_ge (fun hh => hn ((impulse.price ..).trans (low l hh)))⟩
      · exact (hn ((silent a he).price l)).elim
    · intro k hk d
      exact output_next _ _ _ _ _ hk _

theorem fixed {usable : Set (Port I B V)} (he : scene.Extreme usable) {i : I}
    (hg : net.Good (tree.path i)) (hr : Ready usable b i) (hn : i ∉ scene.hits)
    (hi : tree.depth i < h) : (scene.data i hi).Fixed (scene.z i) (scene.p i) := by
  intro w v f g hm
  apply impulse.zero i b
  apply he _ (impulse.supported _ _ _ _ _ _ hr)
  have hpos : ∀ pos, 0 < (scene.out i pos).val 0 b := fun pos =>
    (scene.out i pos).quick_pos hg (scene.raised i pos b).1 (scene.raised i pos b).2
      (fun hh => hn ⟨pos,hh⟩)
  have low := hm.low
  have second := hm.second
  rw [scene.cost] at low second
  apply scene.stationary hg (.inr (.inl ⟨hi,w,v,f,g,hm,rfl,hpos⟩)) low
  rintro ⟨_ | _,l⟩ d hmove
  · apply scene.safe_start hg hn
    intro e he
    rw [scene.firstGap i hi]
    apply lt_of_lt_of_le _ (scene.first i hi l e he)
    by_contra! hh
    obtain ⟨hw,hf⟩ := hm.first l hh
    simp [quick,base,hi,hw,hf] at hmove
  · apply scene.safe_start hg hn
    intro e he
    rw [scene.secondGap i hi,Parameters.allow,mul_div_assoc]
    apply lt_of_lt_of_le _ (scene.second i hi l e he)
    apply mul_lt_mul_of_pos_left _ (net.par i).epos
    by_contra! hh
    have hv := low l (by linarith [(net.par i).lpos])
    have hg := second l (by linarith)
    simp [quick,base,hi,hv,hg] at hmove

theorem descent [NeZero V] {usable : Set (Port I B V)} (he : scene.Extreme usable) :
    tree.Descent usable b scene.hits := by
  refine ⟨net.Good,by simp [Network.Good],fun i hg hr hn => ?_⟩
  by_cases hi : tree.depth i < h
  · have hf := scene.feasible i hi
    obtain ⟨l,hl,hu⟩ := hf.select ((scene.fixed he hg hr hn hi).rigid hf)
    rw [scene.cost] at hl hu
    exact ⟨hi,l,(net.good_cons ..).mpr ⟨⟨hl,by linarith [(net.par i).lpos]⟩,hg⟩⟩
  · have hs : scene.Stationary (impulse i b 0 0 1 0) :=
      scene.stationary hg (.inr (.inr ⟨hi,1,rfl⟩)) (fun _ _ => rfl)
        (fun pos d _ => scene.safe_start hg hn pos (scene.leaf i hi pos) d)
    have hh := he _ (impulse.supported _ _ _ _ _ _ hr) hs
    exact (one_ne_zero (impulse.zero _ _ _ _ _ _ hh).2.2.1).elim

end Scene
end OAI.Geometry.Hirsch.Layer
