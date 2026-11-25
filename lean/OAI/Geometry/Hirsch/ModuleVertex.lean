import OAI.Geometry.Hirsch.ModuleRows

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer.Plan

open Forest

variable {I : Type} {L V h B N C : ℕ} {code : Bundles L V}
  {tree : Forest I (Fin V) h} {ep : Episodes N} {plan : Plan tree code ep B C}
  {t : Probe N B} {x : Space I B V} {a : Red I B V → ℝ}

structure Feasible (plan : Plan tree code ep B C) (t : Probe N B) (a : Red I B V → ℝ)
    (x : Space I B V) : Prop where
  raise : ∀ i pos d, 0 ≤ a (i,pos,d) ∧ a (i,pos,d) ≤ plan.size (tree.node i (tree.depth i))
  rows : ∀ row, plan.raised t a row ≤ plan.coeff row x

namespace Feasible

variable (hf : plan.Feasible t a x)

include hf

theorem panel (i : I) : (plan.panel i).Feasible (plan.time t) x := fun r => hf.rows (.inl ⟨i,r⟩)

theorem floor (i : I) (pos : Position V) (k : ℕ) (hk : k ≤ tree.depth i) (b : Fin B) :
    0 ≤ plan.value t x i pos k b := by
  have hh := hf.rows (plan.pair i pos ⟨k,by omega⟩ t b b)
  simpa [pair,raised,rhs,coeff,value,plan.line_touch] using hh

theorem pairs (i : I) (pos : Position V) (k : ℕ) (hk : k ≤ tree.depth i) (b d : Fin B) (hne : b ≠ d) :
    plan.gap i pos k ≤ plan.value t x i pos k b + plan.value t x i pos k d := by
  have hh := hf.rows (plan.pair i pos ⟨k,by omega⟩ t b d)
  simp only [pair,raised,rhs,coeff,hne,↓reduceIte,Line.add_apply,Line.smul_apply,Line.const_apply,
    plan.line_touch,LinearMap.add_apply] at hh
  unfold value
  linarith

def track (i : I) (pos : Position V) : (plan.net t x).Track i B where
  val := plan.value t x i pos
  gap := plan.gap i pos
  red d := a (i,pos,d)
  raised d := (hf.raise i pos d).2
  floor := hf.floor i pos
  pair := hf.pairs i pos
  gapLow _ hk := plan.gap_low i pos hk
  step := plan.value_step t x i pos
  stepGap k _ := by simp [gap,eps,net]

def scene : Scene (plan.net t x) t.2 where
  data i hi := plan.data i hi t
  z i l := W i l x - plan.shift i t/2 - if hi : tree.depth i < h then (plan.data i hi t).shift else 0
  p := plan.price t x
  out := hf.track
  feasible i hi := by
    simp only [hi,↓reduceDIte]
    exact (plan.internal i hi t x (hf.panel i)).1
  cost i hi := by simp [net,hi]
  raised i pos d := by
    refine ⟨(hf.raise i pos d).1,?_⟩
    change a (i,pos,d) ≤ plan.value t x i pos (tree.depth i) d
    rw [value_root]
    exact hf.rows (plan.red i pos d)
  first i hi l d hd := by
    simp only [hi,↓reduceDIte,track,plan.value_internal t x i hi]
    exact (plan.internal i hi t x (hf.panel i)).2.1 l d hd
  second i hi l d hd := by
    simp only [net,hi,↓reduceDIte,track,plan.value_internal t x i hi]
    exact (plan.internal i hi t x (hf.panel i)).2.2.1 l d hd
  firstGap i hi l := by simp [track,gap,hi,net]
  secondGap i hi l := by simp [track,gap,hi,net]
  leaf i hi pos d hd := by
    simp only [track,gap,hi,↓reduceIte,plan.value_leaf t x i hi]
    exact (plan.leaf i hi t x (hf.panel i)).1 pos d hd

theorem stops {dir : Space I B V} {i : I} (hs : hf.scene.Quiet dir i) :
    (plan.panel i).Stops (plan.time t) x dir := by
  rcases hs with hs | ⟨hi,w,v,f,g,hm,rfl,hp⟩ | ⟨hi,f,rfl⟩
  · exact (plan.panel i).silent hs
  · apply (plan.internal i hi t x (hf.panel i)).2.2.2
    · simpa only [scene,track,plan.value_internal t x i hi] using hp
    · simp only [scene,hi,↓reduceDIte] at hm
      exact hm
  · apply (plan.leaf i hi t x (hf.panel i)).2
    intro pos
    simpa [plan.value_leaf t x i hi] using hf.floor i pos 0 (by omega) t.2

theorem kills {dir : Space I B V} (hs : hf.scene.Stationary dir) (r : plan.Rows)
    (he : plan.coeff r x = plan.raised t a r) : plan.coeff r dir = 0 := by
  have safe : ∀ i pos k, k ≤ tree.depth i → ∀ d, output tree plan.eps i pos d k dir ≠ 0 →
      (hf.track i pos).Safe k d := hs.2
  rcases r with ⟨i,r⟩ | ⟨i,pos,b⟩ | ⟨i,pos,k,s,b,d⟩
  · exact hf.stops (hs.1 i) r he
  · by_contra hn
    have hh := (hf.track i pos).safe_floor le_rfl (safe i pos _ le_rfl b hn)
    simp only [track,↓reduceIte,value_root] at hh
    exact hh he
  · have hk : k.val ≤ tree.depth i := by omega
    have hl := plan.line_below i k s t
    by_cases hd : b = d
    · simp only [coeff,raised,rhs,hd,↓reduceIte] at he ⊢
      by_contra hn
      have hh := (hf.track i pos).safe_floor hk (safe i pos _ hk d hn)
      have hzero : plan.value t x i pos k d = 0 :=
        le_antisymm (by unfold value; linarith) (hf.floor _ _ _ hk _)
      apply hh
      change plan.value t x i pos k d = _
      rw [hzero]
      split
      · rename_i hr
        have ha := hf.scene.raised i pos d
        change 0 ≤ a (i,pos,d) ∧ a (i,pos,d) ≤ plan.value t x i pos (tree.depth i) d at ha
        rw [hr] at hzero
        exact le_antisymm ha.1 (ha.2.trans_eq hzero)
      · rfl
    · simp only [coeff,raised,rhs,hd,↓reduceIte,Line.add_apply,Line.smul_apply,Line.const_apply,
        LinearMap.add_apply] at he ⊢
      have bound : plan.value t x i pos k b + plan.value t x i pos k d ≤ plan.gap i pos k := by
        unfold value
        linarith
      have hb : output tree plan.eps i pos b k dir = 0 := by
        by_contra hn
        exact bound.not_gt ((safe i pos _ hk b hn).2.2 d hd)
      have hd' : output tree plan.eps i pos d k dir = 0 := by
        by_contra hn
        rw [add_comm] at bound
        exact bound.not_gt ((safe i pos _ hk d hn).2.2 b (Ne.symm hd))
      rw [hb,hd',add_zero]

end Feasible

theorem descent [Fintype I] [NeZero V] (plan : Plan tree code ep B C)
    (ha : ∀ i pos d, 0 ≤ a (i,pos,d) ∧ a (i,pos,d) ≤ plan.size (tree.node i (tree.depth i)))
    (usable : Set (Port I B V)) :
    let sys := plan.block.restriction usable (plan.raised t a)
    ∀ pt ∈ sys.body.extremePoints ℝ,
      tree.Descent usable t.2 {i | ∃ pos, plan.red i pos t.2 ∈ Subtype.val '' sys.active pt} := by
  intro sys pt hp
  obtain ⟨x,hx,he,hd⟩ := plan.block.extend_vertex hp
  let hf : plan.Feasible t a x := ⟨ha,hx⟩
  have extreme : hf.scene.Extreme usable := fun dir hs ht => hd dir hs (hf.kills ht)
  have hits : {i | ∃ pos, plan.red i pos t.2 ∈ Subtype.val '' sys.active pt} = hf.scene.hits := by
    rw [← he]
    ext i
    simp only [Scene.hits,Feasible.scene,Network.Track.Hit,Feasible.track,value_root,mem_ofPred_eq]
    rfl
  rw [hits]
  exact hf.scene.descent extreme

end OAI.Geometry.Hirsch.Layer.Plan
