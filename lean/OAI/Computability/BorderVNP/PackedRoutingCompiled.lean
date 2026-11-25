import OAI.Computability.BorderVNP.PackedRoutingExport
import OAI.Computability.BorderVNP.PackedRoutingCost
import OAI.Computability.BorderVNP.DiagonalExternalSewFieldFrame

/-! # Native routing export on the output of the actual compressed history

The public geometry history runs once, followed by the two hardwired sewing
constants and the full routing/placement frame. Only the underlying profile
pins of the history are inputs to the native advice interpreter.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open VPVNP VPVNP.VerifierNetwork VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open RoutingISA GeometryAdvice GeometryFrameEncoding DiagonalResidueRAM ParseBatchSort CellAddressCircuit

variable {s m n C d k w J A o u W : ℕ} {σ γ : Type*} [Fintype σ] [Fintype γ]
    (F : Fields s m n C d k w σ)

/-- Select the precise compiled image from all native result words. -/
theorem of_packed_words (hk : k ≤ w) (width : w ≤ W) (old : Fin J → Fin s) (ports : Fin A → Fin n)
    (rest : Frame σ (Outputs o w)) (y : σ → Bool) (origin : ℕ) (mz : Memory W)
    (raw : ∀ i : Fin (m*3+(count m C J A+o)), mz (origin+i.val) =
      word W (value fun j => (full F hk old ports rest).eval y (.inl (i,j)))) :
    Image F old ports y origin (readings mz) ∧
      ∀ i : Fin o, mz (origin+m*3+count m C J A+i.val) = word W (value fun j => rest.eval y (.inl (i,j))) := by
  have convert (v : Fin w → Bool) : (word W (value v)).val = value v :=
    word_val _ _ ((value_lt _).trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) width))
  refine ⟨⟨?_,?_⟩,?_⟩
  · intro i c
    have a := raw ((CableTriples.index i c).castAdd _)
    simp only [full,GeometryOutput.prepend_first,Fin.val_castAdd,CableTriples.index_val] at a
    simpa only [readings,Nat.add_assoc] using ((congrArg Fin.val a).trans (convert _)).trans
      (CableTriples.frame_value F hk le_rfl y i c)
  · intro col
    have a := raw (Fin.natAdd (m*3) ((order col).castAdd o))
    simp only [full,GeometryOutput.prepend_rest,GeometryOutput.prepend_first,Fin.val_castAdd,Fin.val_natAdd] at a
    simpa only [readings,bases,Nat.add_assoc] using ((congrArg Fin.val a).trans (convert _)).trans
      (tail_value F hk old ports y col)
  · intro i
    simpa only [full,GeometryOutput.prepend_rest,Fin.val_natAdd,Nat.add_assoc] using
      raw (Fin.natAdd (m*3) (Fin.natAdd (count m C J A) i))

/-- Run the selected sparse history and every downstream routing word in the same
native gate program. The history's output fields are derived from its profile bits. -/
theorem history_export_runs (hk : k ≤ w) (width : w ≤ W) (old : Fin J → Fin s) (ports : Fin A → Fin n)
    (rest : Frame σ (Outputs o w)) (history : Frame γ σ) (pins : γ → (Fin u ⊕ Fin 0) ⊕ Bool) (x : Fin u → Bool)
    (pub : Arg → Word W) (mac : TeamOpcode.Macros W 8) (s0 : Bank W) (m0 : Memory W)
    (f : BroadcastFrame) (st : Stripe) (L : Pins.Layout) (P : Pins.ProcessorFields L)
    (l : GeometryOutput.Layout) (base start : ℕ) (src : Fin u → ℕ)
    (fit : f.Fits W (pub 0).val) (space : st.Fits f W (pub 0).val) :
    let program := (full F hk old ports rest).subst history
    let t := compile program pins
    let input := fun i => (pins i).elim (Sum.elim x Fin.elim0) id
    let y := history.eval input
    GeometryOutput.Placement pub l base start st.dense src t → PhysicalInput pub m0 f st L P l base start src t x →
    rest.eval y (.inr ()) = true →
    ∃ es z mz, Runs pub mac reconstruct s0 m0 es z mz ∧
      traceCost es ≤ GeometryAdvice.cost W u t.size (m*3+(count m C J A+o)) w ∧
      Image F old ports y l.dest (readings mz) ∧
      (∀ i : Fin o, mz (l.dest+m*3+count m C J A+i.val) = word W (value fun j => rest.eval y (.inl (i,j)))) ∧
      ∀ addr, addr < base → addr < start → addr < l.temp → addr < l.dest → addr < st.dense → mz addr = m0 addr := by
  intro program t input y place phys valid
  have good : GeometryOutput.validBit t (Sum.elim x Fin.elim0) = true := by
    rw [GeometryOutput.compiled_valid]
    simpa only [program,Frame.subst_eval,full,GeometryOutput.prepend_valid] using valid
  obtain ⟨es,z,mz,run,ct,_,out⟩ := reconstruct_runs pub mac s0 m0 f st L P l base start src t x fit space place phys good
  have raw (i : Fin (m*3+(count m C J A+o))) : mz (l.dest+i.val) =
      word W (value fun j => (full F hk old ports rest).eval y (.inl (i,j))) := by
    apply (out.words i).trans
    apply congrArg (word W)
    apply congrArg value
    funext j
    exact (bit_eval program pins i j _).trans (Frame.subst_eval ..)
  obtain ⟨image,remaining⟩ := of_packed_words F hk width old ports rest y l.dest mz raw
  exact ⟨es,z,mz,run,ct,image,remaining,fun addr ha hb hc hd he =>
    (out.outside addr (Or.inl ha) (Or.inl hb) (Or.inl hc) (Or.inl hd)).trans (st.image_outside m0 (Or.inl he))⟩

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
