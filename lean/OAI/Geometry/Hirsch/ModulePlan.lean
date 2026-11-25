import OAI.Geometry.Hirsch.ModuleBudget

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer

open Forest

namespace Plan

variable {client : Program} {A : Type} [Nonempty A] {L V h H B N C : ℕ} [NeZero V]
  {code : Bundles L V} {src : Forest client.Coord (Upgrade V A) (h+2*H)}
  {ep : Episodes N} (plan : Plan src.physical code ep B C)

def paint : Coloring (src.device plan.block) client B where
  color := plan.color
  covered b i := ⟨plan.red i (false,0) b,rfl⟩
  ordinary := plan.ordinary

theorem represented (b : Fin B) (rows : Set plan.Rows) :
    plan.paint.represented b rows = {i | ∃ pos, plan.red i pos b ∈ rows} := by
  ext i
  constructor
  · rintro ⟨r,hr,he⟩
    obtain ⟨pos,rfl⟩ := (plan.color_iff r i b).mp he
    exact ⟨pos,hr⟩
  · rintro ⟨pos,hp⟩
    exact ⟨plan.red i pos b,hp,rfl⟩

theorem perturb (t : Probe N B) (delta : plan.Rows → ℝ) :
    (plan.block.slice (plan.time t)).rhs + plan.paint.vary true delta =
      plan.raised t (fun r => delta (.inr (.inl r))) := by
  classical
  funext r
  change plan.rhs r (plan.time t) + plan.paint.vary true delta r = _
  rcases r with ⟨i,r⟩ | ⟨i,pos,b⟩ | ⟨i,pos,k,s,b,d⟩ <;>
    simp [Coloring.vary,paint,color,raised,rhs]

include plan in
theorem modules (hn : 0 < N) (hb : 0 < B) (hm : 0 < Fintype.card client.Coord) :
    Nonempty (src.Modules ep B (C+4*V)) := by
  classical
  let : NeZero N := ⟨hn.ne'⟩
  let : Nonempty client.Coord := Fintype.card_pos_iff.mp hm
  let tol := least plan.size / 6
  have ht : 0 < tol := by
    obtain ⟨i,he⟩ := least_attained plan.size
    unfold tol; rw [he]; exact div_pos (plan.size_pos i) (by norm_num)
  have hs : ∀ i, 6*tol ≤ plan.size i := fun i => by unfold tol; linarith [least_le plan.size i]
  refine ⟨{
    Row := plan.Rows, block := plan.block, paint := plan.paint, time := fun i b => plan.time (i,b),
    interior := fun i b => plan.interior (i,b), eps := tol, positive := ht,
    probe := ?_, anchor := ?_, groupBound := ?_, red := ?_, support := plan.support,
    rows := plan.row_count hn hb hm }⟩
  · intro delta hd i b usable
    rw [plan.perturb]
    intro sys pt hp
    rw [plan.represented]
    exact plan.descent (t := (i,b)) (a := fun r => delta (.inr (.inl r))) (fun j pos d =>
      ⟨(hd _).1,(hd _).2.le.trans ((show tol ≤ 6*tol by linarith).trans (hs _))⟩) usable pt hp
  · intro _ time _ x hx
    apply le_trans _ (plan.anchor hs time x hx)
    refine ncard_le_ncard ?_ (toFinite _)
    intro b hh
    change (plan.paint.represented _ _).Nonempty at hh
    rw [plan.represented] at hh
    exact hh
  · intro b i
    have he : plan.paint.group b i = range (fun pos => plan.red i pos b) := by
      ext r
      change plan.color r = some (b,i) ↔ _
      rw [plan.color_iff]
      exact exists_congr fun _ => eq_comm
    rw [he]
    simpa [Position] using ncard_image_le (s := univ) (f := fun pos => plan.red i pos b)
  · intro b i r hr
    obtain ⟨pos,rfl⟩ := (plan.color_iff r i b).mp hr
    exact plan.red_support i pos b

end Plan

def PlanTheorem : Prop :=
  ∀ rate : ℕ, ∃ L V C : ℕ, 2 ≤ L ∧ 0 < V ∧ (2*V)^rate ≤ L ∧ ∃ code : Bundles L V,
    ∀ h, 0 < h → ∀ (I : Type) (tree : Forest I (Fin V) h) B, 0 < B →
      ∀ ep : Episodes (L^h), Nonempty (Plan tree code ep B C)

theorem modules_of_plan (input : PlanTheorem) : ModuleTheorem := by
  intro rate
  obtain ⟨L,V,C,hL,hV,hr,code,hs⟩ := input rate
  let : NeZero V := ⟨hV.ne'⟩
  refine ⟨L,V,C+4*V,hL,hV,hr,by omega,fun h H hh A _ prog src hm B hb ep => ?_⟩
  obtain ⟨plan⟩ := hs h hh _ src.physical B hb ep
  exact plan.modules (by positivity) hb hm

end OAI.Geometry.Hirsch.Layer
