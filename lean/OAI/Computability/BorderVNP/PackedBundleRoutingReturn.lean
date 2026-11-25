import OAI.Computability.BorderVNP.PackedBundleBankConfig
import OAI.Computability.BorderVNP.PackedRoutingExport

/-! # Returning bundle-header and routing words from one shared geometry execution

The two stable-sort banks follow the ordinary routing and private-placement columns.
Further geometry output can follow them, retaining its original validity wire.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.BottomReports.BundleSort

open RoutingISA ParseBatchSort PackedHistogram CellPacketGeometry CellAddressCircuit
open VPVNP VPVNP.VerifierNetwork VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open GeometryAdvice GeometryFrameEncoding DiagonalResidueRAM

variable {σ : Type*} [Fintype σ] {s m n d k w J A o b u W : ℕ} (banks : CellBanks.Layout)
variable (F : Fields s m n banks.cells d k w σ)

/-- The two dense sort banks for the true original site rows, with no extra native calls. -/
noncomputable def headerBanks (b : ℕ) (old : Fin J → Fin s) (desc gap : ℕ)
    (shape : Fin J → Shape) (valid : Frame σ Unit) : Frame σ (Fin (2^b+2^b) × Fin w) :=
  (geometry (source banks.cells b (geometryHeaders F old desc (bankConfig banks gap valid) shape))).select Sum.inl

/-- Append the rest of the required geometry result after the header words. -/
noncomputable def withHeaderBanks (b : ℕ) (old : Fin J → Fin s) (desc gap : ℕ) (shape : Fin J → Shape)
    (valid : Frame σ Unit) (rest : Frame σ (Outputs o w)) : Frame σ (Outputs ((2^b+2^b)+o) w) :=
  GeometryOutput.prepend (headerBanks banks F b old desc gap shape valid) rest

/-- The true geometry interpreter writes the routing rows, both header-sort banks,
and any additional public outputs to distinct consecutive intervals in its own RAM. -/
theorem routing_return (old : Fin J → Fin s) (ports : Fin A → Fin n) (desc gap : ℕ)
    (shape : Fin J → Shape) (valid : Frame σ Unit) (rest : Frame σ (Outputs o w))
    (hk : k ≤ w) (width : w ≤ W) (pins : σ → (Fin u ⊕ Fin 0) ⊕ Bool) (x : Fin u → Bool)
    (pub : Arg → Word W) (mac : TeamOpcode.Macros W 8) (s₀ : RoutingISA.Bank W) (m₀ : Memory W)
    (f : BroadcastFrame) (st : Stripe) (L : RoutingISA.Pins.Layout) (P : RoutingISA.Pins.ProcessorFields L)
    (l : GeometryOutput.Layout) (base start : ℕ) (src : Fin u → ℕ)
    (fit : f.Fits W (pub 0).val) (space : st.Fits f W (pub 0).val) :
    let up := geometryHeaders F old desc (bankConfig banks gap valid) shape
    let suff := withHeaderBanks banks F b old desc gap shape valid rest
    let t := compile (RoutingOutputs.full F hk old ports suff) pins
    let input := fun i => (pins i).elim (Sum.elim x Fin.elim0) id
    let dest := l.dest+m*3+RoutingOutputs.count m banks.cells J A
    GeometryOutput.Placement pub l base start st.dense src t → PhysicalInput pub m₀ f st L P l base start src t x →
    rest.eval input (.inr ()) = true →
    ∃ es z mz, Runs pub mac reconstruct s₀ m₀ es z mz ∧
      traceCost es ≤ GeometryAdvice.cost W u t.size (m*3+(RoutingOutputs.count m banks.cells J A+((2^b+2^b)+o))) w ∧
      RoutingOutputs.Image F old ports input l.dest (readings mz) ∧
      (∀ i : Fin (2^b+2^b), readings mz (dest+i.val) =
        value (fun j => (geometry (source banks.cells b up)).eval input (.inl (i,j)))) ∧
      (∀ i : Fin o, mz (dest+(2^b+2^b)+i.val) = word W (value (fun j => rest.eval input (.inl (i,j))))) ∧
      ∀ addr, addr < base → addr < start → addr < l.temp → addr < l.dest → addr < st.dense → mz addr = m₀ addr := by
  intro up suff t input dest place physical accepted
  have pass : suff.eval input (.inr ()) = true := (GeometryOutput.prepend_valid ..).trans accepted
  obtain ⟨es,z,mz,run,ticks,image,out,keep⟩ := RoutingOutputs.export_runs F hk width old ports suff pins x pub mac
    s₀ m₀ f st L P l base start src fit space place physical pass
  refine ⟨es,z,mz,run,ticks,image,fun i => ?_,fun i => ?_,keep⟩
  · have result := congrArg Fin.val (out (i.castAdd o))
    simp only [suff,withHeaderBanks,GeometryOutput.prepend_first,Fin.val_castAdd,headerBanks,Frame.select_eval] at result
    exact result.trans (word_val _ _ ((value_lt _).trans_le (Nat.pow_le_pow_right (by decide : 0 < 2) width)))
  · simpa only [suff,withHeaderBanks,GeometryOutput.prepend_rest,Fin.val_natAdd,dest,Nat.add_assoc] using
      out (Fin.natAdd (2^b+2^b) i)

end Packing.BottomReports.BundleSort

end BorderVNP
end Computability
end OAI
