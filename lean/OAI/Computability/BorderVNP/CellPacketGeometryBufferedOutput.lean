import OAI.Computability.BorderVNP.CellPacketGeometryFixed

/-! # Reading the sparse cell buffers out of the joint Boolean geometry output

A larger native emitter may publish the cell-packet output as one of its banks.
The two sorting permutations and every section address then follow directly from
the words actually written by that emitter.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry.Schema

open PackedHistogram ParseBatchSort Packing.Word VPVNP.VerifierNetwork GeometryFrameEncoding RoutingISA.CellPacket
open private values_length from OAI.Computability.BorderVNP.CellPacketGeometryNative

variable {σ E S Orig : Type} [Fintype σ] [Fintype E] {C p d k w M N : ℕ}

/-- Decode the two sorted banks in RAM solely from the word-by-word output of
the true joint geometry frame. The header and descriptor positions are taken
from their inverse-permutation banks. -/
theorem buffers_of_output (D : SiteWords.Directory S Orig C) (fit : C+D.words.length+C ≤ 2^p)
    (space : C+(coords M).length+C ≤ 2^d) (dest H : ℕ) (refs : Fin M → Reference D.words.length E)
    (own : Fin M → Fin C) (upstream : Frame σ (Pins D.words.length M k w E)) (input : σ → Bool)
    (keysFit : C < 2^k) (sourceFit : dest+2^p < 2^w) (hd : 2^d ≤ 2^w) (header : H<2^w) (one : 1<2^w)
    (pw : ∀ i : Fin D.words.length, value (fun j => upstream.eval input (.inl (i,.inl j))) = D.words[i.val].1.val)
    (words : ∀ i : Fin D.words.length, value (fun j => upstream.eval input (.inl (i,.inr j))) = D.words[i.val].2)
    (pr : ∀ i : Fin M, value (fun j => upstream.eval input (.inr (.inl (i,j)))) = (own i).val)
    (mem : ℕ → ℕ)
    (output : ∀ i : Fin (Total p d), mem (dest+i.val) =
      value (fun j => (joint (source C p d upstream) (expression C d fit dest H refs)).eval input (.inl (i,j)))) :
    ∃ π : Equiv.Perm (Fin (2^p)), Buffers D fit space dest H refs own
      (fun e => value fun j => upstream.eval input (.inr (.inr (.inl (e,j))))) mem π := by
  let sourceFrame := source C p d upstream
  let expr := expression C d fit dest H refs
  let up := sourceFrame.eval input
  let raw := fun i => up (.inl i)
  let owner := fun i : Fin D.words.length => D.words[i.val].1
  let down := fun i : Fin (coords M).length => own ((coords M)[i.val]).1
  let arg := fun e => value fun j => upstream.eval input (.inr (.inr (.inl (e,j))))
  obtain ⟨pk,pv,dk,rest⟩ := source_values (p := p) (d := d) upstream input owner own keysFit pw pr
  have hp : 2^p ≤ 2^w := by omega
  obtain ⟨π,rank,wp,rp,second⟩ := joint_values sourceFrame expr input hp hd
  obtain ⟨τ,order,wd,rt⟩ := second (fun i => expression_fits fit dest H refs up π i sourceFit header one)
  let K := fun i : Fin (2^d) => value fun j => up (.inr (.inl (i,j)))
  have pkey : Stable.key raw = fun i => Markers.key owner (Markers.row C D.words.length i.val) := funext pk
  have pword : Stable.weight raw = fun i => Markers.word (fun j : Fin D.words.length => D.words[j.val].2)
      (Markers.row C D.words.length i.val) := funext fun i => (pv i).trans
        (congrArg (fun g => Markers.word g (Markers.row C D.words.length i.val)) (funext words))
  have dkey : K = fun i => Markers.key down (Markers.row C (coords M).length i.val) := funext dk
  have op : operands up π = Sum.elim arg (fun j => (π.symm j).val) := by
    funext e
    cases e with
    | inl v => exact congrArg value (funext fun j => rest (.inl (v,j)))
    | inr j => rfl
  have pos (i : Fin (2^p)) : mem (dest+(2^p+i.val)) = (π.symm i).val :=
    (output (outputIndex (.inl (.inr i)))).trans (rp i)
  change Monotone (fun i => 2*Stable.key raw (π i)*2^p+(π i).val) at rank
  refine ⟨π,⟨by simpa only [pkey] using rank,pos,?_,?_⟩⟩
  · intro c
    have same : Stable.key raw (Markers.start fit c) = Stable.key raw (Markers.stop fit c) := by rw [pkey]; simp [Markers.key]
    obtain ⟨size,stored⟩ := range_read (Stable.key raw) (Stable.weight raw) mem dest π rank
      (fun i => (output (outputIndex (.inl (.inl i)))).trans (wp i)) pos _ _ same
    rw [pkey,pword,publicArray] at stored
    rw [pkey] at size
    have len := congrArg List.length (publicArray D fit c)
    simp only [List.length_map] at len
    exact ⟨size.trans len,stored⟩
  · intro c
    have vals (i : Fin (2^d)) : mem (descriptorBank dest p+i.val) = (expr (τ i)).eval (operands up π) := by
      simpa only [descriptorBank,Nat.add_assoc,outputIndex,Sum.map_inr,Sum.map_inl,
        finSumFinEquiv_apply_right,finSumFinEquiv_apply_left,Fin.val_natAdd,Fin.val_castAdd] using
        (output (outputIndex (.inr (.inl i)))).trans (wd i)
    have positions (i : Fin (2^d)) : mem (descriptorBank dest p+(2^d+i.val)) = (τ.symm i).val := by
      simpa only [descriptorBank,Nat.add_assoc,outputIndex,Sum.map_inr,finSumFinEquiv_apply_right,Fin.val_natAdd] using
        (output (outputIndex (.inr (.inr i)))).trans (rt i)
    have same : K (Markers.start space c) = K (Markers.stop space c) := by rw [dkey]; simp [Markers.key]
    obtain ⟨size,stored⟩ := range_read K (fun i => (expr i).eval (operands up π)) mem (descriptorBank dest p)
      τ order vals positions _ _ same
    rw [dkey,op] at stored
    have selected := descriptorSection fit space dest H own refs c (Sum.elim arg (fun j => (π.symm j).val))
    rw [selected] at stored
    rw [dkey] at size
    have len := congrArg List.length selected
    simp only [List.length_map,values_length] at len
    exact ⟨by simpa only [List.length_map] using size.trans len,stored⟩

/-- Instantiate a fixed geometry frame on the branch whose source ordinals and
true descriptor operands it represents. The RAM evidence is only the frame's
public output words in their canonical bank order. -/
theorem fixed_buffers_of_output (fit : C+N+C ≤ 2^p) (space : C+(coords M).length+C ≤ 2^d)
    (dest H : ℕ) (refs : Fin M → Reference N E) (up : Frame σ (Pins N M k w E)) (x : σ → Bool)
    (keysFit : C<2^k) (sourceFit : dest+2^p<2^w) (hd : 2^d≤2^w) (header : H<2^w) (one : 1<2^w)
    (D : SiteWords.Directory S Orig C) (pin : Orig → E)
    (nEq : N = D.words.length) (mEq : M = (D.referenceRows pin).length)
    (same : ∀ i, cast (congrArg (fun n => Reference n E) nEq) (refs i) = ((D.referenceRows pin).get (i.cast mEq)).2)
    (words : ∀ i : Fin N, (D.words[i.val]?).map (fun z => (z.1.val,z.2)) =
      some (value (fun j => up.eval x (.inl (i,.inl j))),value (fun j => up.eval x (.inl (i,.inr j)))))
    (owners : ∀ i, value (fun j => up.eval x (.inr (.inl (i,j)))) = ((D.referenceRows pin).get (i.cast mEq)).1.val)
    (mem : ℕ → ℕ) (output : ∀ i : Fin (Total p d), mem (dest+i.val) =
      value (fun j => (joint (source C p d up) (expression C d fit dest H refs)).eval x (.inl (i,j)))) :
    ∃ π : Equiv.Perm (Fin (2^p)), Buffers D (nEq ▸ fit) (mEq ▸ space) dest H (fun i => ((D.referenceRows pin).get i).2)
      (fun i => ((D.referenceRows pin).get i).1) (fun e => value fun j => up.eval x (.inr (.inr (.inl (e,j))))) mem π := by
  subst N
  subst M
  have href : refs = fun i => ((D.referenceRows pin).get i).2 := funext same
  subst refs
  have both i := words i
  simp only [List.getElem?_eq_getElem (Fin.isLt _),Option.map_some,Option.some.injEq,Prod.mk.injEq] at both
  exact buffers_of_output D fit space dest H _ _ up x keysFit sourceFit hd header one
    (fun i => (both i).1.symm) (fun i => (both i).2.symm) owners mem output

end CellPacketGeometry.Schema

end BorderVNP
end Computability
end OAI
