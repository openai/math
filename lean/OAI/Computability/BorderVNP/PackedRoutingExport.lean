import OAI.Computability.BorderVNP.PackedRoutingImage
import OAI.Computability.BorderVNP.GeometryAdviceAllocation

/-! # Native execution exporting the routing and placement arrays

A single return of the geometry decoder supplies all addressed cable, endpoint,
supplied-count, private counter, and placement arrays, in their native word ABI.
The public frame and other inputs preceding the geometry allocation survive.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open VPVNP VPVNP.VerifierNetwork VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open RoutingISA GeometryAdvice GeometryFrameEncoding DiagonalResidueRAM ParseBatchSort CellAddressCircuit

variable {s m n C d k w J A o u W : ℕ} {σ : Type*} [Fintype σ] (F : Fields s m n C d k w σ)

/-- The actual geometry ISA reconstructs all routing outputs and leaves the base/count
frame words below its allocation unchanged. No arrays are supplied by an oracle. -/
theorem export_runs (hk : k ≤ w) (width : w ≤ W) (old : Fin J → Fin s) (ports : Fin A → Fin n)
    (rest : VerifierNetwork.Frame σ (Outputs o w)) (pins : σ → (Fin u ⊕ Fin 0) ⊕ Bool) (x : Fin u → Bool)
    (pub : Arg → Word W) (mac : TeamOpcode.Macros W 8) (s0 : Bank W) (m0 : Memory W)
    (f : BroadcastFrame) (st : Stripe) (L : Pins.Layout) (P : Pins.ProcessorFields L)
    (l : GeometryOutput.Layout) (base start : ℕ) (src : Fin u → ℕ)
    (fit : f.Fits W (pub 0).val) (space : st.Fits f W (pub 0).val) :
    let t := compile (full F hk old ports rest) pins
    let input := fun i => (pins i).elim (Sum.elim x Fin.elim0) id
    GeometryOutput.Placement pub l base start st.dense src t → PhysicalInput pub m0 f st L P l base start src t x →
    rest.eval input (.inr ()) = true →
    ∃ es z mz, Runs pub mac reconstruct s0 m0 es z mz ∧
      traceCost es ≤ GeometryAdvice.cost W u t.size (m*3+(count m C J A+o)) w ∧
      Image F old ports input l.dest (readings mz) ∧
      (∀ i : Fin o, mz (l.dest+m*3+count m C J A+i.val) = word W (value fun j => rest.eval input (.inl (i,j)))) ∧
      ∀ addr, addr < base → addr < start → addr < l.temp → addr < l.dest → addr < st.dense → mz addr = m0 addr := by
  intro t input place physical valid
  let p := CableTriples.frame F hk (le_refl w)
  let e := tail F hk old ports
  let q := GeometryOutput.prepend e rest
  obtain ⟨es,z,mz,run,ct,first,next,preserve⟩ := GeometryOutput.prefix_runs pub mac s0 m0 f st L P l
    base start src p q pins x fit space place physical ((GeometryOutput.prepend_valid e rest input).trans valid)
  have convert (v : Fin w → Bool) : (word W (value v)).val = value v :=
    word_val _ _ ((value_lt _).trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) width))
  refine ⟨es,z,mz,run,ct,⟨?_,?_⟩,?_,preserve⟩
  · intro i c
    have a := first (CableTriples.index i c)
    have hc := (congrArg Fin.val a).trans (convert _)
    rw [CableTriples.index_val] at hc
    exact (by simpa only [readings,Nat.add_assoc] using hc.trans (CableTriples.frame_value F hk le_rfl input i c))
  · intro col
    have a := next ((order col).castAdd o)
    simp only [q,GeometryOutput.prepend_first,Fin.val_castAdd] at a
    exact ((congrArg Fin.val a).trans (convert _)).trans (tail_value F hk old ports input col)
  · intro i
    have a := next (Fin.natAdd (count m C J A) i)
    simpa only [q,GeometryOutput.prepend_rest,Fin.val_natAdd,Nat.add_assoc] using a

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
