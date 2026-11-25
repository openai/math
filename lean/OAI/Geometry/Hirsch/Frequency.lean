import OAI.Geometry.Hirsch.Bins

noncomputable section

open Classical

namespace OAI.Geometry.Hirsch.Layer.Board.Legs.Decoration

open Naming

variable {u : Dials} {X : Type} {L : Legs u X} (A : L.Decoration) (key : Bool → X) (p : ℕ)

def failures := Finset.univ.filter fun r => ¬A.Calm key p r

theorem few (fixed : A.Fixed) (hp : p ≤ Naming.P u) :
    (A.failures key p).card * H u ≤ M u ^ 2 * N u := by
  let fail := fun j => (A.failures key p).filter fun r => block u p r.val / H u = j
  have each : ∀ j, (fail j).card ≤ M u^2 * length u p := by
    intro j
    by_cases hem : (fail j).Nonempty
    swap
    · simp [Finset.not_nonempty_iff_eq_empty.mp hem]
    obtain ⟨r,hr⟩ := hem
    have eq := (Finset.mem_filter.mp hr).2
    let S := A.region key p r
    let idx := fun t : X × X => sInf {m | A.Break m t.1 t.2}
    let cover := fun t => Finset.univ.filter fun s : Radii u => block u p s = block u p (idx t)
    have sub : fail j ⊆ (S ×ˢ S).biUnion cover := by
      intro s hs
      obtain ⟨hs,he⟩ := Finset.mem_filter.mp hs
      have hh := (Finset.mem_filter.mp hs).2
      unfold Calm at hh
      rw [fixed.region hp (he.trans eq.symm)] at hh
      push Not at hh
      obtain ⟨x,hx,y,hy,m,hm,hbreak⟩ := hh
      have hid : idx (x,y) = m := A.unique_break (Nat.sInf_mem (s := {m | A.Break m x y}) ⟨m,hbreak⟩) hbreak
      exact Finset.mem_biUnion.mpr ⟨(x,y),Finset.mem_product.mpr ⟨hx,hy⟩,
        Finset.mem_filter.mpr ⟨Finset.mem_univ _,by rw [hid,hm]⟩⟩
    have bound := Finset.card_biUnion_le_card_mul (S ×ˢ S) cover _ (fun t _ => card_block u p _)
    refine ((Finset.card_le_card sub).trans bound).trans ?_
    rw [Finset.card_product,pow_two]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul (A.region_bound key p r) (A.region_bound key p r))
  let parents := Finset.range (H u ^ p)
  have sub : A.failures key p ⊆ parents.biUnion fail := fun r hr =>
    Finset.mem_biUnion.mpr ⟨_,Finset.mem_range.mpr (parent_lt u p hp r),Finset.mem_filter.mpr ⟨hr,rfl⟩⟩
  have high := (Finset.card_le_card sub).trans (Finset.card_biUnion_le_card_mul parents fail _ (fun j _ => each j))
  calc
    _ ≤ parents.card * (M u^2 * length u p) * H u := Nat.mul_le_mul_right _ high
    _ = _ := by rw [← product u p hp]; simp only [parents,Finset.card_range]; ring

theorem frequent (fixed : A.Fixed) :
    N u ≤ 2*(Finset.univ.filter (A.Good key)).card := by
  let bad := Finset.univ.filter fun r => ¬A.Good key r
  let stages := Finset.range (Naming.P u+1)
  have incl : bad ⊆ stages.biUnion (A.failures key) := by
    intro r hr
    have h := (Finset.mem_filter.mp hr).2
    unfold Good at h; push Not at h
    obtain ⟨p,hp,hn⟩ := h
    exact Finset.mem_biUnion.mpr ⟨p,Finset.mem_range.mpr (by omega),Finset.mem_filter.mpr ⟨Finset.mem_univ _,hn⟩⟩
  have high : bad.card * H u ≤ (Naming.P u+1)*(M u^2*N u) := by
    calc
      _ ≤ (∑ p ∈ stages, (A.failures key p).card)*H u :=
        Nat.mul_le_mul_right _ ((Finset.card_le_card incl).trans Finset.card_biUnion_le)
      _ ≤ ∑ _ ∈ stages, M u^2*N u := by
        rw [Finset.sum_mul]
        exact Finset.sum_le_sum fun p hp => A.few key p fixed (Nat.lt_succ_iff.mp (Finset.mem_range.mp hp))
      _ = _ := by simp [stages]
  have small : 2*bad.card ≤ N u := by
    apply Nat.le_of_mul_le_mul_right _ (Hpos u)
    calc
      _ = 2*(bad.card*H u) := by ring
      _ ≤ 2*((Naming.P u+1)*(M u^2*N u)) := Nat.mul_le_mul_left _ high
      _ ≤ _ := by unfold H; nlinarith
  have split := Finset.card_filter_add_card_filter_not (s := Finset.univ) (A.Good key)
  simp only [Finset.card_univ,Fintype.card_fin] at split
  change _ + bad.card = N u at split
  omega

end OAI.Geometry.Hirsch.Layer.Board.Legs.Decoration
