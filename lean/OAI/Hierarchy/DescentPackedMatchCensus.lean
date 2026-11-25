import OAI.Hierarchy.DescentPackedMatchPhysicalOrder
import OAI.Hierarchy.DescentPackedMatchFinal

namespace OAI
/-! # Reading every real source count and every empty lane of the topology bank -/
namespace Hierarchy.DescentPacking.PackedMatch
open DescentSIMDLookup
open scoped Classical BigOperators
noncomputable section
variable {H G M : ℕ}

/-- Bounded output digits on a live typed row, with genuine numerical zero
in every non-source lane, including the last partial chunk. -/
theorem topology_count (s : Shape) (x : Fin H→Fin G→Inputs s) (small : ∀h j,Bounded (x h j))
    (p : Row H G M) (i : Fin M) :
    (laneCounts s M (topologyWords s x (row H G M p)) i).val =
      if h : p.2.val*M+i.val<G then amount (x p.1 ⟨_,h⟩) else 0 := by
  let key:=topologyWords s x (row H G M p)
  change (laneCounts s M key i).val=_
  have entry : ∀a, digit s.outputBits i.val key.val=a ↔
      digit s.outputBits i.val (masked (lookupCell s) (fun h j=>encodeInput (x h j)) p)=a := by
    intro a;rw [topology_key]
  by_cases h : p.2.val*M+i.val<G
  · rw [dite_eq_left h]
    apply lane_actual s _ (small _ _) key i
    apply (entry _).mpr
    simpa only [lookupCell,decode_encode] using
      active_read (lookupCell s) (fun h j=>encodeInput (x h j)) p i h
  · rw [dite_eq_right h]
    apply lane_unused s key i
    apply (entry 0).mpr
    apply padding_zero
    unfold used
    omega

theorem graph_counts {C : Type} [Fintype C] (s : Shape) (hm : 0<M)
    (x : Fin H→Fin G→Inputs s) (small : ∀h j,Bounded (x h j))
    (slot : C ↪ Fin H×Fin G) (rows : C→ℕ) (live : ∀c,amount (x (slot c).1 (slot c).2)=rows c)
    (vacant : ∀h g,(∀c,slot c≠(h,g))→amount (x h g)=0)
    (seat : C↪Fin (H*chunks G M)×Fin M)
    (physical : ∀c,seat c=(row H G M (position (slot c).1 (slot c).2 hm),lane (slot c).2 hm)) :
    Chronology.Counts seat rows (fun i=>laneCounts s M (topologyWords s x i)) := by
  refine ⟨?_,?_⟩
  · intro c
    rw [physical c]
    let p:=position (slot c).1 (slot c).2 hm
    let j:=lane (slot c).2 hm
    have eqn : p.2.val*M+j.val=(slot c).2.val := Nat.div_add_mod' ..
    have h:=eqn.trans_lt (slot c).2.isLt
    have rd:=topology_count s x small p j
    rw [dite_eq_left h] at rd
    have id : (⟨p.2.val*M+j.val,h⟩ : Fin G)=(slot c).2:=Fin.ext eqn
    rw [id] at rd
    exact rd.trans (live c)
  · intro r a absent
    let p:=(row H G M).symm r
    have eqn : row H G M p=r := (row H G M).apply_symm_apply r
    have rd := topology_count s x small p a
    rw [eqn] at rd
    rw [rd]
    split
    · rename_i h
      let g : Fin G:=⟨p.2.val*M+a.val,h⟩
      apply vacant p.1 g
      intro c present
      apply absent c
      rw [physical c,present]
      have dec : (position p.1 g hm).2.val=p.2.val := by
        change (p.2.val*M+a.val)/M=p.2.val
        rw [Nat.mul_comm p.2.val M,Nat.mul_add_div hm,Nat.div_eq_of_lt a.isLt,Nat.add_zero]
      have res : lane g hm=a := by
        apply Fin.ext
        change (p.2.val*M+a.val)%M=a.val
        simp [Nat.add_mod,Nat.mod_eq_of_lt a.isLt]
      have same : position p.1 g hm=p := Prod.ext rfl (Fin.ext dec)
      rw [same,eqn,res]
    · rfl

theorem amount_zero (s : Shape) (x : Inputs s) (zero : ∀i,x.need i=0) : amount x=0 := by
  have eqn : ∀i,need x i=0 := fun i=>by simp only [need,zero,Fin.val_zero]
  apply Nat.eq_zero_of_le_zero
  calc
    amount x ≤ ∑ i, need x i := PackedLocalMatch.count_le (need x) (cap x)
    _ = 0 := by simp only [eqn,Finset.sum_const_zero]

end
end Hierarchy.DescentPacking.PackedMatch

end OAI
