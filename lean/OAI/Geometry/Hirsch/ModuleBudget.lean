import OAI.Geometry.Hirsch.ModuleSupport

noncomputable section

open Set

namespace OAI.Geometry.Hirsch.Layer.Plan

open Forest

variable {I : Type} [Fintype I] {L V h B N C : ℕ} {code : Bundles L V}
  {tree : Forest I (Fin V) h} {ep : Episodes N} (plan : Plan tree code ep B C)

theorem row_count (hn : 0 < N) (hb : 0 < B) (hm : 0 < Fintype.card I) :
    Fintype.card plan.Rows ≤ (C+4*V)*N*(B*Fintype.card I)^3 := by
  have hN : 1 ≤ N := hn
  let m := Fintype.card I
  have hp : Fintype.card (Σ i, (plan.panel i).Row) ≤ m*(C*N*B^2) := by
    rw [Fintype.card_sigma]
    simpa [m] using Finset.sum_le_sum (s := Finset.univ) (fun i _ => plan.rows i)
  have hr : Fintype.card (Red I B V) = 2*V*B*m := by simp [Red,Position,m]; ring
  have hs : Fintype.card (Pairs tree N B) ≤ m*(2*V*m*(N*B)*B*B) := by
    simp only [Pairs,Fintype.card_sigma,Position,Probe,Fintype.card_prod,Fintype.card_bool,Fintype.card_fin]
    calc
      _ ≤ ∑ _ : I, 2*V*m*(N*B)*B*B := by
        apply Finset.sum_le_sum
        intro i _
        simp only [mul_assoc]
        gcongr
        exact tree.depth_card i
      _ = _ := by simp [m]
  have bm : 0 < m := hm
  have h₂ : B^2 ≤ B^3 := Nat.pow_le_pow_right hb (by decide)
  have h₃ : m^2 ≤ m^3 := Nat.pow_le_pow_right bm (by decide)
  have h₁ : m ≤ m^3 := Nat.le_self_pow (by decide) _
  have h₀ : B ≤ B^3 := Nat.le_self_pow (by decide) _
  change Fintype.card (_ ⊕ _ ⊕ _) ≤ (C+4*V)*N*(B*m)^3
  rw [Fintype.card_sum,Fintype.card_sum,hr]
  calc
    _ ≤ m*(C*N*B^2) + (2*V*B*m + m*(2*V*m*(N*B)*B*B)) := by gcongr
    _ = C*N*B^2*m + (2*V*1*B*m + 2*V*N*B^3*m^2) := by ring
    _ ≤ C*N*B^3*m^3 + (2*V*N*B^3*m^3 + 2*V*N*B^3*m^3) := by gcongr
    _ = _ := by ring

omit [Fintype I] in
theorem color_iff (r : plan.Rows) (i : I) (b : Fin B) :
    plan.color r = some (b,i) ↔ ∃ pos, r = plan.red i pos b := by
  constructor
  · rcases r with ⟨j,r⟩ | ⟨j,pos,d⟩ | ⟨j,p⟩
    · simp [color]
    · intro he
      obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj he)
      exact ⟨pos,rfl⟩
    · simp [color]
  · rintro ⟨pos,rfl⟩; rfl

omit [Fintype I] in
theorem red_slack (i : I) (pos : Position V) (b : Fin B) (time : ℝ) (x : Space I B V) :
    plan.block.slack (plan.red i pos b) (time,x) = output tree plan.eps i pos b (tree.depth i) x := by
  simp [Blocking.slack,block,red,coeff,rhs,Line.const]

omit [Fintype I] in
theorem pair_slack (i : I) (pos : Position V) (s : Probe N B) (b d : Fin B) (hne : b ≠ d)
    (time : ℝ) (x : Space I B V) :
    plan.block.slack (plan.pair i pos (Fin.last _) s b d) (time,x) =
      plan.block.slack (plan.red i pos b) (time,x) + plan.block.slack (plan.red i pos d) (time,x)
        - plan.gap i pos (tree.depth i) := by
  rw [red_slack,red_slack]
  change plan.coeff _ x - plan.rhs _ time = _
  simp [pair,coeff,rhs,line,hne]

theorem anchor [NeZero N] [NeZero V] [Nonempty I] {eps : ℝ}
    (he : ∀ i, 6*eps ≤ plan.size i) (time : ℝ) (x : Space I B V)
    (hf : ∀ r, -(2*eps) < plan.block.slack r (time,x)) :
    {b | ∃ i pos, plan.block.slack (plan.red i pos b) (time,x) < 2*eps}.ncard ≤ 2*V*Fintype.card I := by
  classical
  let S := {b | ∃ i pos, plan.block.slack (plan.red i pos b) (time,x) < 2*eps}
  have hex : ∀ b, ∃ z : I × Position V, b ∈ S → plan.block.slack (plan.red z.1 z.2 b) (time,x) < 2*eps := by
    intro b
    by_cases hb : b ∈ S
    · obtain ⟨i,pos,hh⟩ := hb
      exact ⟨(i,pos),fun _ => hh⟩
    · exact ⟨Classical.arbitrary _,fun hh => (hb hh).elim⟩
  choose f hp using hex
  have hinj : InjOn f S := by
    intro b hb d hd heq
    by_contra hn
    obtain ⟨⟨i,pos⟩,hi⟩ := show ∃ z, f b = z from ⟨_,rfl⟩
    have h₁ := hp b hb
    have h₂ := hp d hd
    rw [hi] at h₁
    rw [← heq,hi] at h₂
    have h₃ := hf (plan.pair i pos (Fin.last _) (0,b) b d)
    rw [pair_slack _ _ _ _ _ _ hn] at h₃
    have h₄ := (he _).trans (plan.gap_low i pos le_rfl)
    dsimp only at h₁ h₂
    linarith
  simpa [S,Position,mul_comm] using ncard_le_ncard_of_injOn f (t := univ) (fun _ _ => mem_univ _) hinj

end OAI.Geometry.Hirsch.Layer.Plan
