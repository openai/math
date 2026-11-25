import OAI.Computability.BorderVNP.PackedRoutingCompiled
import OAI.Computability.BorderVNP.PackedRoutingPlaced

/-! # Export of the genuine final sewn network from its measured public history

The static exterior rectangle supplies exactly four possible interval rows per
original grid block. Only occupied pieces have positive width. The original site
pins are fixed across histories, while their present owners come from the shared
history's output. No new guesses are introduced by the routing export.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.RoutingOutputs

open Crossing CellAddressCircuit CellAddressPhysical Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport
open VPVNP VPVNP.VerifierNetwork VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM
open RoutingISA GeometryAdvice GeometryFrameEncoding DiagonalResidueRAM

variable {D s old n C d k w J o u W : ℕ} {σ γ : Type*} [Fintype σ] [Fintype γ]

/-- The native output represents the physical grouped and sewn network, with both
interior and exterior cables in the checked ordinal order and every free port in
team-major order. Only the previous (pre-sewing) sparse history is required. -/
theorem sewn_export_runs (p : Params) (hp : p.Valid) {A P₀ : Type} {bits : A → ℕ}
    (N : Network D A bits) (lane : P₀ ↪ Σ a, Fin (bits a))
    {phys : PublicPort p.R p.processors p.literal p.link ≃ P₀} (hosts : BlockHosts (FineView.layout N lane) phys p.g)
    (cell : N.Site → Fin C) (aux : N.Site → ℕ) (siteID : N.Site ↪ Fin s)
    (edgeID : N.Edge ↪ Fin old) (portID : A ↪ Fin n)
    (F : Fields s old n C d k w σ) (source : Frame γ σ) (name : ℕ → ℕ → ℕ)
    (hostNames : ∀ (t : Fin (p.R+1)) i, i < p.sites → name t.val i = (F.sites (siteID (hosts.host (t,i)))).val)
    (groupFits : p.g < 2^w) (hk : k ≤ w) (width : w ≤ W) (oldPins : Fin J → Fin s)
    (rest : Frame (σ ⊕ Bool) (Outputs o w)) (pins : γ → (Fin u ⊕ Fin 0) ⊕ Bool) (x : Fin u → Bool)
    (pub : Arg → Word W) (mac : TeamOpcode.Macros W 8) (s0 : Bank W) (m0 : Memory W)
    (f : BroadcastFrame) (st : Stripe) (L : Pins.Layout) (P : Pins.ProcessorFields L)
    (l : GeometryOutput.Layout) (base start : ℕ) (src : Fin u → ℕ)
    (fit : f.Fits W (pub 0).val) (space : st.Fits f W (pub 0).val) :
    let M := finalLayout p hosts
    let B := fields F p name
    let hist := withSewnFields source
    let t := compile ((full B hk oldPins id rest).subst hist) pins
    let input := fun i => (pins i).elim (Sum.elim x Fin.elim0) id
    let y := hist.eval input
    Represents N cell aux siteID edgeID portID F (source.eval input) →
    GeometryOutput.Placement pub l base start st.dense src t → PhysicalInput pub m0 f st L P l base start src t x →
    rest.eval y (.inr ()) = true →
      Represents M cell aux siteID (mergedEdges p hp edgeID) finProdFinEquiv.toEmbedding B y ∧
      ∃ es z mz, Runs pub mac reconstruct s0 m0 es z mz ∧
        traceCost es ≤ GeometryAdvice.cost W u t.size ((old+p.slots)*3+(count (old+p.slots) C J ((p.R+1)*p.sites)+o)) w ∧
        Image B oldPins id y l.dest (readings mz) ∧
        (∀ i : Fin o, mz (l.dest+(old+p.slots)*3+count (old+p.slots) C J ((p.R+1)*p.sites)+i.val) =
          word W (ParseBatchSort.value fun j => rest.eval y (.inl (i,j)))) ∧
        ∀ addr, addr < base → addr < start → addr < l.temp → addr < l.dest → addr < st.dense → mz addr = m0 addr := by
  intro M B hist t input y before place actual valid
  exact ⟨frame_represents p hp N lane hosts cell aux siteID edgeID portID F source input before name hostNames groupFits,
    history_export_runs B hk width oldPins id rest hist pins x pub mac s0 m0 f st L P l base start src fit space
      place actual valid⟩

/-- The same history is charged once when appended to the actual full export, with
all private-marker and original staging outputs. -/
theorem sewn_export_size {s old n C d k w J o L R : ℕ} (p : Params)
    (F : Fields s old n C d k w σ) (source : Frame γ σ) (name : ℕ → ℕ → ℕ) (hk : k ≤ w)
    (oldPins : Fin J → Fin s) (rest : Frame (σ ⊕ Bool) (Outputs o w))
    (rows : 1+CellAddressCircuit.count s (old+p.slots) ((p.R+1)*p.sites) C+J+((p.R+1)*p.sites) ≤ R)
    (widths : d ≤ L ∧ k ≤ L ∧ w ≤ L ∧ Nat.clog 2 R ≤ L) :
    let B := fields F p name
    ((full B hk oldPins id (withPrivateViews B oldPins rest)).subst (withSewnFields source)).size ≤
      source.size+2+rest.size+15000*R*(L+1)^3 := by
  intro B
  rw [Frame.subst_size]
  exact (Nat.add_le_add (withSewnFields_size source) (full_size_le B hk oldPins id rest rows widths)).trans (by omega)

end Packing.RoutingOutputs

end BorderVNP
end Computability
end OAI
