import OAI.Hierarchy.ProbeChains
import OAI.ThreeFlat.Concentrator.GreedyMixing
import OAI.ThreeFlat.Concentrator.ExpanderSize

namespace OAI
/-! # A bounded-degree sampler at every group size -/

namespace Hierarchy.AdaptiveProbe
open ThreeFlat.Concentrator
open BinPackingGames.Foundations.PCP PoweringWalks SpectralReturn
noncomputable section

/-- A single finite list per input describes all legal sampler edges, and both port degrees
are bounded independently of the group size. The output permutation of a tile matching
can be chosen after the graph is fixed. -/
theorem exists_group_samplers {δ : ℝ} (hd : 0<δ) :
    ∃ D : ℕ, ∀ l : ℕ, 0 < l → ∃ next : Fin l → List (Fin l),
      (∀ i, (next i).length ≤ D) ∧
      (∀ j, (Finset.univ.filter fun i => j ∈ next i).card ≤ D) ∧
      ∀ (perm : Equiv.Perm (Fin l)) (a : ℕ), δ*l ≤ a → SamplerMixes (fun i j => j ∈ next (perm i)) a := by
  classical
  obtain ⟨D,hD,_,lam,hlam,hsmall,graphs,_⟩ := exists_concentrator_expanders 0 (ε:=δ/4) (by positivity)
  refine ⟨D,fun l hl => ?_⟩
  obtain ⟨k,hlo,hhi,G,cert⟩ := graphs l hl
  let m := 2^k
  have hm : 0 < m := hl.trans_le hlo
  let : NeZero D := ⟨hD.ne'⟩
  let : NeZero m := ⟨hm.ne'⟩
  let port : Fin l ↪ Fin m := Fin.castLEEmb hlo
  let read := Function.partialInv port
  let ports := List.finRange D
  let next := portCandidates G ports port read
  refine ⟨next,?_,?_,?_⟩
  · intro i
    simpa only [ports,List.length_finRange] using portCandidates_length G ports port read i
  · intro j
    simpa only [Fintype.card_fin] using portCandidates_contenders_card G ports port port read
      (fun eq => ((port.injective.isPartialInv _ _).mp eq).symm) j
  · intro perm a density A B ha hb
    let source := perm.toEmbedding.trans port
    have size : (0:ℝ) < m := by exact_mod_cast hm
    have scaled : lam<(a:ℝ)/m := by
      apply (lt_div_iff₀ size).2
      calc
        lam*m < (δ/2)*m := mul_lt_mul_of_pos_right (by linarith) size
        _ ≤ (δ/2)*(2*l) := mul_le_mul_of_nonneg_left (by exact_mod_cast hhi) (by positivity)
        _ = δ*l := by ring
        _ ≤ _ := density
    have bigA : lam<(A.card:ℝ)/m := scaled.trans_le
      (div_le_div_of_nonneg_right (by exact_mod_cast ha) size.le)
    have bigB : lam<(B.card:ℝ)/m := scaled.trans_le
      (div_le_div_of_nonneg_right (by exact_mod_cast hb) size.le)
    have strong : lam^2 < ((A.card:ℝ)/m)*((B.card:ℝ)/m) := by
      rw [sq]
      exact (mul_le_mul_of_nonneg_left bigB.le hlam).trans_lt
        (mul_lt_mul_of_pos_right bigA (hlam.trans_lt bigB))
    obtain ⟨x,hx,d,hdst⟩ := exists_port_between G cert (A.map source) (B.map port) (by simpa [m] using strong)
    obtain ⟨i,hi,rfl⟩ := Finset.mem_map.mp hx
    obtain ⟨j,hj,e⟩ := Finset.mem_map.mp hdst
    refine ⟨i,hi,j,hj,List.mem_filterMap.mpr ⟨d,List.mem_finRange _,?_⟩⟩
    change read (G.rot (source i,d)).1=some j
    rw [←e]
    exact port.injective.isPartialInv.eq _

end
end Hierarchy.AdaptiveProbe

end OAI
