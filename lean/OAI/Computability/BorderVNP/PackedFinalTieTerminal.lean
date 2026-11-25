import OAI.Computability.BorderVNP.PackedFinalTieSewn
import OAI.Computability.BorderVNP.PackedFinalTieFrozen

/-! # Uniform final binding tape on the original terminal output pins

The shared field frame supplies the complete final site and cable geometry,
including work extents. Recovery and all sparse commands run before the
specific accepted history is chosen. On the terminal ordinal codebook the
native frozen rows already carry the sparse site IDs expected by the packet
template.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalTies

open Crossing Shortening.PublicCapacity CellAddresses CellAddressCircuit CellAddressPhysical
open ParseBatchSort VPVNP.VerifierNetwork FrozenTape

variable {s : Shape} {np C d k w : ℕ} {σ : Type*} [Fintype σ]
    (F : Fields s.sites s.edges np C d k w σ)
    (occupied : Fin s.edges → σ) (portUsed : Fin np → Bool)

/-- Work is recovered directly from the already exported full staging extent. -/
noncomputable def workFrame := Classical.choose (recover F)

/-- The newly exposed endpoint work words lie immediately alongside the original geometry. -/
def recoveredPins (i : Fin s.sites) (j : Fin w) : σ ⊕ (Fin s.sites × Fin w) := .inr (i,j)

/-- Uniform final sparse binding tape computed from the actual terminal geometry. -/
noncomputable def terminalTape :=
  (codeTape (retained F) recoveredPins (Sum.inl ∘ occupied) portUsed).subst (workFrame F).withInput

/-- Work recovery, shared allocation scans, and the one sparse equality per incident word. -/
theorem terminalTape_size : (terminalTape F occupied portUsed).size ≤
    (Views.frame F).size + 1 + s.sites*3*(100*(w+1)^2) +
    ((inputs (retained F) recoveredPins (Sum.inl ∘ occupied) portUsed).size + 1 +
      (2*s.edges+np)*(4500*(w+1)^2)) := by
  have emitCost := (Classical.choose_spec (Layer.emit d w
    (inputs (retained F) recoveredPins (Sum.inl ∘ occupied) portUsed))).1
  rw [terminalTape,Frame.subst_size,Frame.withInput_size,codeTape,NineWords.adapt_size,numeric]
  apply Nat.add_le_add (Classical.choose_spec (recover F)).1
  simpa only [Row,Subdivision.Gates.Old,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,
    Fintype.card_fin,Nat.mul_comm s.edges 2] using emitCost

variable {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
    (rows : Rows s N) (ports : P ↪ Fin np) (cell : N.Site → Fin C) (state : N.Site → Site)
    (x : σ → Bool) (rep : Represents N cell (fun u => (state u).size) rows.site rows.edge ports F x)
    (fit : ∀ c, guessedSize N cell c + siteSize N cell c (fun u => (state u).size) + suppliedSize N cell c < 2^w)
    (hin : ∀ v, (state v).incoming = incoming N v) (one : 1 < 2^w)
    (live : ∀ i, x (occupied i) = true ↔ i ∈ Set.range rows.edge)
    (used : ∀ i, portUsed i = true ↔ i ∈ Set.range ports)

include rep fit hin one live used in
/-- Exact native row sequence of absolute final ties at every site, including all
true zero-width incidences, using only the geometry output and true occupancy. -/
theorem terminal_section :
    (tieSchema s.edges np w).Section ((terminalTape F occupied portUsed).eval x)
      ((rows.site.trans F.sites).trans Fin.valEmbedding)
      (fun v => Placement.ties N cell (cell v) rows.site rows.edge ports state ⟨v,rfl⟩) := by
  let wf := workFrame F
  let y := wf.withInput.eval x
  have cover := recover_value F N cell state rows.site rows.edge ports rep hin wf
    ((Classical.choose_spec (recover F)).2 x)
  have workRead (v : N.Site) : value (y ∘ recoveredPins (σ := σ) (rows.site v)) = (state v).work := by
    simpa only [y,recoveredPins,Function.comp_def,Frame.withInput_eval_inr] using cover.live v
  have present (i : Fin s.edges) : y ((Sum.inl ∘ occupied) i) = true ↔ i ∈ Set.range rows.edge := by
    simpa only [y,Function.comp_apply,Frame.withInput_eval_inl] using live i
  have image := codeTape_section (retained F) recoveredPins (Sum.inl ∘ occupied) portUsed one
    N rows ports cell state (retained_rep F N cell (fun u => (state u).size) rows.site rows.edge ports wf x rep)
    fit hin workRead present used
  have eqn : (terminalTape F occupied portUsed).eval x =
      (codeTape (retained F) recoveredPins (Sum.inl ∘ occupied) portUsed).eval y :=
    funext fun j => Frame.subst_eval _ _ _ _
  rw [eqn]; exact image

include rep fit hin one live used in
/-- With the terminal routing codebook, these true owner keys are exactly the ordinary row IDs. -/
theorem terminal_id_section (ordinal : ∀ i, (F.sites i).val = i.val) :
    (tieSchema s.edges np w).Section ((terminalTape F occupied portUsed).eval x)
      (rows.site.trans Fin.valEmbedding)
      (fun v => Placement.ties N cell (cell v) rows.site rows.edge ports state ⟨v,rfl⟩) := by
  have eqn : ((rows.site.trans F.sites).trans Fin.valEmbedding) = (rows.site.trans Fin.valEmbedding) :=
    Function.Embedding.ext (fun v => ordinal (rows.site v))
  exact eqn ▸ terminal_section F occupied portUsed N rows ports cell state x rep fit hin one live used

end Packing.Inherited.FinalTies

end BorderVNP
end Computability
end OAI
