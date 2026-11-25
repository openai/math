import OAI.Computability.BorderVNP.CellPacketGeometryDirectory

/-! # Simultaneous physical public-word and descriptor arrays

Executing the one advised geometry gate table writes the original-word and chunk
directory intervals. The first sort's returned ranks are the real inputs to address
arithmetic in the second sort. Both kinds of section can be empty.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellPacketGeometry

open PackedHistogram ParseBatchSort VPVNP.VerifierNetwork GeometryFrameEncoding Packing.Word
open VPVNP VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM
open GeometryAdvice RoutingISA.CellPacket

variable {σ E : Type*} [Fintype σ] [Fintype E] {p d k w u : ℕ}

/-- The descriptor sort's dense region directly follows the public words and ranks. -/
def descriptorBank (dest p : ℕ) : ℕ := dest+(2^p+2^p)

set_option maxRecDepth 4500 in
/-- Native execution from the actual geometry stripes returns both compact arrays at
their computed addresses, together with the unique trace and full serialization charge. -/
theorem execute_directory (source : Frame σ (Columns p d k w E))
    (expr : Fin (2^d) → WidthExpr (E ⊕ Fin (2^p))) (pub : Arg → Word w)
    (mac : TeamOpcode.Macros w 8) (s : RoutingISA.Bank w) (m : Memory w) (f : BroadcastFrame)
    (a : Stripe) (L : Pins.Layout) (P : Pins.ProcessorFields L) (l : GeometryOutput.Layout)
    (base start : ℕ) (src : Fin u → ℕ) (pins : σ → (Fin u ⊕ Fin 0) ⊕ Bool) (x : Fin u → Bool)
    (fit : f.Fits w (pub 0).val) (space : a.Fits f w (pub 0).val) (hp : 2^p ≤ 2^w) (hd : 2^d ≤ 2^w) :
    let g := joint source expr
    let t := compile g pins
    let input := fun i => (pins i).elim (Sum.elim x Fin.elim0) id
    let up := source.eval input
    let raw := fun i => up (.inl i)
    let key := fun (i : Fin (2^d)) => value fun j => up (.inr (.inl (i,j)))
    GeometryOutput.Placement pub l base start a.dense src t →
    PhysicalInput pub m f a L P l base start src t x →
    up (.inr (.inr (.inr ()))) = true →
    (∀ (π : Equiv.Perm (Fin (2^p))) i, (expr i).Fits w (operands up π)) →
    ∃ es z mz, ∃ π : Equiv.Perm (Fin (2^p)),
      Runs pub mac reconstruct s m es z mz ∧
      traceCost es ≤ GeometryAdviceRate.ticks t.size u (Total p d) w w ∧
      Monotone (fun i => 2*Stable.key raw (π i)*2^p+(π i).val) ∧
      (∀ i, readings mz (l.dest+(2^p+i.val)) = (π.symm i).val) ∧
      (∀ lo hi : Fin (2^p), Stable.key raw lo = Stable.key raw hi →
        (sectionRange (readings mz) l.dest lo hi).2 = (inside (Stable.key raw) lo hi).length ∧
        WordsAt (readings mz) (sectionRange (readings mz) l.dest lo hi).1
          ((inside (Stable.key raw) lo hi).map (Stable.weight raw))) ∧
      (∀ lo hi : Fin (2^d), key lo = key hi →
        (sectionRange (readings mz) (descriptorBank l.dest p) lo hi).2 = (inside key lo hi).length ∧
        WordsAt (readings mz) (sectionRange (readings mz) (descriptorBank l.dest p) lo hi).1
          ((inside key lo hi).map fun i => (expr i).eval (operands up π))) ∧
      ∀ bits fs, TeamRAM.execute (reconstruct.program.fetch pub mac) ⟨0,s⟩ m bits = some fs ↔
        fs = es ∧ bits = es.map TeamRAM.Event.choices := by
  intro g t input up raw key layout physical valid safe
  have accepted : g.eval input (.inr ()) = true := (joint_valid ..).trans valid
  obtain ⟨es,z,mz,run,ticks,output,unique⟩ :=
    (frame_execute pub mac s m f a L P l base start src g pins x fit space layout physical).2 accepted
  obtain ⟨π,rk,wp,rp,hdesc⟩ := joint_values source expr input hp hd
  obtain ⟨τ,rd,wd,rt⟩ := hdesc (safe π)
  have mem (r : Bank p ⊕ Bank d) : readings mz (l.dest+(outputIndex r).val) =
      value (fun j => g.eval input (.inl (outputIndex r,j))) := by
    rw [readings,output]
    exact Nat.mod_eq_of_lt (value_lt _)
  have pos (i : Fin (2^p)) : readings mz (l.dest+(2^p+i.val)) = (π.symm i).val :=
    (mem (.inl (.inr i))).trans (rp i)
  refine ⟨es,z,mz,π,run,ticks,rk,pos,fun lo hi same => range_read _ _ _ l.dest π rk
    (fun i => (mem (.inl (.inl i))).trans (wp i)) pos lo hi same,fun lo hi same => ?_,unique⟩
  apply range_read key _ _ (descriptorBank l.dest p) τ rd _ _ lo hi same
  · intro i
    simpa only [descriptorBank,Nat.add_assoc,outputIndex,Sum.map_inr,Sum.map_inl,
      finSumFinEquiv_apply_right,finSumFinEquiv_apply_left,Fin.val_natAdd,Fin.val_castAdd] using
      (mem (.inr (.inl i))).trans (wd i)
  · intro i
    simpa only [descriptorBank,Nat.add_assoc,outputIndex,Sum.map_inr,finSumFinEquiv_apply_right,
      Fin.val_natAdd] using (mem (.inr (.inr i))).trans (rt i)

end CellPacketGeometry

end BorderVNP
end Computability
end OAI
