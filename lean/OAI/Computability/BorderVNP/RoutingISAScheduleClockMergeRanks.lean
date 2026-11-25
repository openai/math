import OAI.Computability.BorderVNP.CellPacketGeometryBufferedOutput

/-! # Separation of consecutive descriptor sections in the actual sorted bank -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.Schema

open PackedHistogram ParseBatchSort Packing.Word VPVNP.VerifierNetwork GeometryFrameEncoding

/-- A stable sort places the stop marker of a smaller cell before the start
marker of a larger cell, regardless of their original input ordinals. -/
theorem marker_rank_lt {C N d : ℕ} (space : C+N+C ≤ 2^d) (owner : Fin N → Fin C)
    (π : Equiv.Perm (Fin (2^d)))
    (sorted : Monotone fun i => 2*Markers.key owner (Markers.row C N (π i).val)*2^d+(π i).val)
    {c c' : Fin C} (h : c<c') : (π.symm (Markers.stop space c)).val < (π.symm (Markers.start space c')).val := by
  by_contra! rev
  have rank := sorted (show π.symm (Markers.start space c') ≤ π.symm (Markers.stop space c) from rev)
  simp only [Equiv.apply_symm_apply,Markers.row_start,Markers.row_stop,Markers.key] at rank
  have gap := Nat.mul_le_mul_right (2^d) (show 2*c.val+1 ≤ 2*c'.val by change c.val<c'.val at h; omega)
  rw [Nat.add_mul,one_mul] at gap
  have stop := (Markers.stop space c).isLt
  omega

/-- The descriptor sort writes its actual inverse permutation into the second
half of the descriptor bank. Reading those two words gives disjoint sections
for any two different cells in their native order. -/
theorem descriptor_ranks_of_output {σ E : Type} [Fintype σ] [Fintype E] {C N M p d k w : ℕ}
    (fit : C+N+C ≤ 2^p) (space : C+(coords M).length+C ≤ 2^d)
    (dest H : ℕ) (refs : Fin M → Reference N E) (upstream : Frame σ (Pins N M k w E)) (x : σ → Bool)
    (wordOwner : Fin N → Fin C) (partOwner : Fin M → Fin C)
    (keysFit : C<2^k) (sourceFit : dest+2^p<2^w) (hd : 2^d≤2^w) (header : H<2^w) (one : 1<2^w)
    (pw : ∀ i, value (fun j => upstream.eval x (.inl (i,.inl j)))=(wordOwner i).val)
    (pr : ∀ i, value (fun j => upstream.eval x (.inr (.inl (i,j))))=(partOwner i).val)
    (mem : ℕ → ℕ) (output : ∀ i : Fin (Total p d), mem (dest+i.val)=
      value (fun j => (joint (source C p d upstream) (expression C d fit dest H refs)).eval x (.inl (i,j)))) :
    ∀ c c' : Fin C, c<c' →
      mem (descriptorBank dest p+2^d+(C+(coords M).length+c.val)) <
      mem (descriptorBank dest p+2^d+c'.val) := by
  let sf := source C p d upstream
  let expr := expression C d fit dest H refs
  let up := sf.eval x
  let down := fun i : Fin (coords M).length => partOwner ((coords M)[i.val]).1
  have dk := (source_values (p:=p) (d:=d) upstream x wordOwner partOwner keysFit pw pr).2.2.1
  obtain ⟨π,_,_,_,second⟩ := joint_values sf expr x (by omega) hd
  obtain ⟨τ,order,_,ranks⟩ := second (fun i => expression_fits fit dest H refs up π i sourceFit header one)
  have sorted : Monotone fun i => 2*Markers.key down (Markers.row C (coords M).length (τ i).val)*2^d+(τ i).val := by
    simpa only [sf,dk] using order
  have pos (i : Fin (2^d)) : mem (descriptorBank dest p+2^d+i.val)=(τ.symm i).val := by
    simpa only [descriptorBank,Nat.add_assoc,outputIndex,Sum.map_inr,finSumFinEquiv_apply_right,Fin.val_natAdd] using
      (output (outputIndex (.inr (.inr i)))).trans (ranks i)
  intro c c' h
  change mem (descriptorBank dest p+2^d+(Markers.stop space c).val) < mem (descriptorBank dest p+2^d+(Markers.start space c').val)
  rw [pos,pos]
  exact marker_rank_lt space down τ sorted h

end CellPacketGeometry.Schema

end BorderVNP
end Computability
end OAI
