import OAI.Computability.BorderVNP.PackedGridSeedTape
import OAI.Computability.VPVNP.GrammarSize

/-! # Exact integer decoding of the prewired seed's padded body and sidecar -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.DeckGrid

open VPVNP VPVNP.ParseGrammar TeamScales
open scoped Classical

/-- The finite parameter number actually written to a canonical seed sidecar. -/
noncomputable def seedLabelCode (n g : ℕ) : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ :=
  (Fintype.equivFin _).toEmbedding.trans Fin.valEmbedding

/-- The canonical enumeration takes values strictly inside its public parameter count. -/
theorem seedLabelCode_lt (n g : ℕ) (p : GrammarLabel (Fin n × Bool) (Fin g) n) :
    seedLabelCode n g p < Fintype.card (GrammarLabel (Fin n × Bool) (Fin g) n) :=
  (Fintype.equivFin _ p).isLt

/-- The actual state count of the parse circuit fits the parameter header estimate
under the processor hypothesis used to construct the prewired witness. -/
theorem seed_states_le (n s r : ℕ) (hr : (n+s+2)^24 ≤ r) :
    Fintype.card (ParseTable.State (Fin n × Bool) s) ≤ r := by
  simp only [ParseTable.State,Fintype.card_fin,Fintype.card_prod,Fintype.card_bool]
  apply le_trans (b := (n+s+2)^2) (by nlinarith)
  exact (Nat.pow_le_pow_right (by omega : 0 < n+s+2) (by decide : 2 ≤ 24)).trans hr

/-- Grammar labels and exponent places fit in the common fixed binary header.
The parameter numbering can be any enumeration of the actual finite labels. -/
theorem label_header_room {n g r factor : ℕ} (hn : 1 ≤ n) (hr : 1 ≤ r) (hg : g ≤ r) (hf : 8 ≤ factor) :
    Fintype.card (GrammarLabel (Fin n × Bool) (Fin g) n) ≤ 2^(factor*logWidth r n) := by
  let B := 2*n*r
  have hnB : n ≤ B := by dsimp [B]; nlinarith
  have hrB : r ≤ B := by dsimp [B]; nlinarith
  have hB : 2 ≤ B := by dsimp [B]; nlinarith
  have ht : g*(n*2) ≤ B := by dsimp [B]; nlinarith [Nat.mul_le_mul_right (2*n) hg]
  have hq : n^2*g^3 ≤ B^5 := by
    calc
      _ ≤ B^2*B^3 := Nat.mul_le_mul (Nat.pow_le_pow_left hnB _) (Nat.pow_le_pow_left (hg.trans hrB) _)
      _ = _ := by ring
  have hcount : Fintype.card (GrammarLabel (Fin n × Bool) (Fin g) n) ≤ g*(n*2)+n^2*g^3 := by
    simpa using card_grammarLabel_le (Fin n × Bool) (Fin g) n
  have hB5 : B ≤ B^5 := by simpa using Nat.pow_le_pow_right (by omega : 0 < B) (by decide : 1 ≤ 5)
  have hpower : B ≤ 2^(logWidth r n) := by
    rw [Shortening.PublicCapacity.public_logWidth]
    exact Nat.le_pow_clog (by decide) _
  calc
    _ ≤ B+B^5 := hcount.trans (Nat.add_le_add ht hq)
    _ ≤ B*B^5 := by nlinarith [Nat.mul_le_mul_right (B^5) hB]
    _ = B^6 := by ring
    _ ≤ (2^(logWidth r n))^6 := Nat.pow_le_pow_left hpower _
    _ = 2^(6*logWidth r n) := by rw [Nat.mul_comm 6,pow_mul]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right _ (by omega))

end Packing.DeckGrid

namespace Packing.DeckGrid.WiredWitness

open Crossing CellSparse GridBoxes GridPlacement BottomGridBank BottomReports Inherited Cover TeamContraction
open Diagonal.CellEntries Diagonal.ExternalSew ParseBatch ParseBatchVerifier Prewire VPVNP VPVNP.ParseGrammar TeamScales
open scoped Classical
variable {R r t pins link inner n g : ℕ} {Edge : Type} [Fintype Edge]
    {G : Wiring R r t pins link inner n Edge} {d : Fin n} {D q depth : ℕ}
    {order : Fin (Fintype.card (Fin q → Deck (depth+2))) ≃ (Fin q → Deck (depth+2))} {state : Fin g}
    (W : WiredWitness G d D q depth order state)
    (position : (Fin q → Deck (depth+2)) → {v : EuclideanSpace ℝ (Fin D) // ‖v‖ ≤ 1})
    (code : GrammarLabel (Fin n × Bool) (Fin g) n ↪ ℕ)
    {s m p qe qa : ℕ} (siteID : (W.routedFine position).Site ↪ Fin s) (edgeID : (W.routedFine position).Edge ↪ Fin m)
    (portID : (Fin r × Fin (publicWidth G)) ↪ Fin p) (channelID : ((Fin q → Deck (depth+2)) × Direction q) ↪ Fin qe)
    (groupID : Fin (GridHosts.tileCount q depth) ↪ Fin qa) (c : Fin q → Deck (depth+2))
local notation "K₀" => seedBoxCapacity n r q depth (Fintype.card (Direction q))
local notation "body₀" => bodyBudget K₀
local notation "ps₀" => W.seedPositions position code siteID edgeID portID c
local notation "orig₀" => 3*seedSiteCapacity n r q depth + incoming (W.seedGrouped position) c

private theorem n_header {factor : ℕ} (hr : 1 ≤ r) (hf : 8 ≤ factor) : n < 2^(factor*logWidth r n) := by
  apply (Nat.size_le.mp (CellMacro.Generator.size_le_logWidth n r hr)).trans_le
  apply Nat.pow_le_pow_right (by decide)
  simpa only [Nat.one_mul] using Nat.mul_le_mul_right (logWidth r n) (show 1 ≤ factor by omega)

/-- The true source tape's count, parameter, bit place and staged relative address
all fit before encoding in the fixed header words. -/
theorem seedPositions_fit {factor : ℕ} (hr : 1 ≤ r) (hg : g ≤ r) (hf : 8 ≤ factor) (room : K₀ ≤ n)
    (bounded : ∀ p, code p < Fintype.card (GrammarLabel (Fin n × Bool) (Fin g) n)) :
    TallySidecar.Fits (factor*logWidth r n) ps₀ := by
  have hn : 1 ≤ n := by have := d.isLt; omega
  have capS : seedSiteCapacity n r q depth ≤ K₀ := by unfold seedBoxCapacity; omega
  have hnH := n_header (n := n) hr hf
  have len := W.seedPositions_length position code siteID edgeID portID c
  have capRoom := W.seedBorn_room position c
  intro k hk
  rcases List.mem_cons.mp hk with he | hk
  · exact he ▸ (len.trans (capS.trans room)).trans_lt hnH
  obtain ⟨p,hp,hk⟩ := List.mem_flatMap.mp hk
  obtain ⟨i,rfl⟩ := List.mem_iff_get.mp hp
  let j := W.sidecarEquiv position code siteID edgeID portID c orig₀ i
  have h := W.sidecarEquiv_fields position code siteID edgeID portID c orig₀ i
  change _ = code j.val.1 ∧ _ = j.val.2.val ∧ _ = orig₀+i.val at h
  rcases List.mem_cons.mp hk with h₁ | hk
  · exact h₁ ▸ h.1.symm ▸ (bounded j.val.1).trans_le (label_header_room hn hr hg hf)
  rcases List.mem_cons.mp hk with h₂ | hk
  · rw [h₂,h.2.1]
    have hArg : r*(2*d.val+1)+1 ≤ 2*n*r := by
      have hd : 2*d.val+2 ≤ 2*n := by have := d.isLt; omega
      nlinarith [Nat.mul_le_mul_left r hd]
    have hL : Nat.clog 2 (r*(2*d.val+1)+1) ≤ logWidth r n := by
      rw [Shortening.PublicCapacity.public_logWidth]
      exact Nat.clog_mono_right _ hArg
    apply (j.val.2.isLt.trans_le hL).trans_le (Nat.lt_two_pow_self.le.trans _)
    exact Nat.pow_le_pow_right (by decide) (by simpa using Nat.mul_le_mul_right (logWidth r n) (show 1 ≤ factor by omega))
  have he : k = _ := List.mem_singleton.mp hk
  rw [he,h.2.2]
  have hi := i.isLt.trans_le len
  unfold bottomStride at capRoom
  exact (show orig₀+i.val ≤ K₀ by omega).trans_lt (room.trans_lt hnH)

/-- Any received seed tape satisfying the paper's public common-size bounds
supplies the actual opaque body length and every named metadata integer exactly. -/
theorem seedTape_decoded {w factor : ℕ} (mem : BurstRAM.Memory w) (slot : ℕ)
    (hr : 1 ≤ r) (hg : g ≤ r) (hf : 8 ≤ factor) (room : K₀ ≤ n)
    (lengthRoom : seedDescriptionWidth n r q depth (factor*logWidth r n) body₀ ≤ n)
    (bounded : ∀ p, code p < Fintype.card (GrammarLabel (Fin n × Bool) (Fin g) n))
    (received : ∀ j : Fin (seedDescriptionWidth n r q depth (factor*logWidth r n) body₀), (mem (slot+j.val)).val =
      (W.seedTape position code siteID edgeID portID channelID groupID c (factor*logWidth r n) j).toNat) :
    let H := factor*logWidth r n
    let fs := W.seedStored position code siteID edgeID portID channelID groupID c
    (RoutingISA.CellPacket.Chunk.box slot H (Packet.Source.boxBody fs)).Stored (fun a => (mem a).val) ∧
      DiagonalTallyBits.WordsAt mem (slot+H+body₀) (TallySidecar.words H ps₀) ∧
      (TallySidecar.words H ps₀).map TapeWord.value = TallySidecar.fields ps₀ := by
  intro H fs
  have sent := W.seedTape_delivered position code siteID edgeID portID channelID groupID c mem H slot received
  have hb := W.seedBody_room position code siteID edgeID portID channelID groupID c
  have hs := sidecar_room H body₀ _ (W.seedPositions_length position code siteID edgeID portID c)
  have hlen : H + (Packet.Source.boxBody fs).length ≤ seedDescriptionWidth n r q depth H body₀ :=
    (Nat.add_le_add_left hb H).trans (Nat.le_add_right _ _)
  exact ⟨Packet.Source.box_stored _ slot H fs sent.1 hlen ((Nat.le_add_left _ _).trans hlen |>.trans_lt (lengthRoom.trans_lt (n_header hr hf))),
    sent.2,TallySidecar.words_values H _ (W.seedPositions_fit position code siteID edgeID portID c hr hg hf room bounded)⟩

end Packing.DeckGrid.WiredWitness

end BorderVNP
end Computability
end OAI
