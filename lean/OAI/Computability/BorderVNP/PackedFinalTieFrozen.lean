import OAI.Computability.BorderVNP.PackedFinalTieActive
import OAI.Computability.BorderVNP.PackedFinalTieOrder
import OAI.Computability.BorderVNP.PackedFinalTiePhysical
import OAI.Computability.BorderVNP.PackedFrozenNineWords
import OAI.Computability.BorderVNP.PackedFrozenTapeSections

/-! # Complete final binding sections on the actual sparse site IDs

The final binding rectangle includes every true cable or port row, including width
zero. A batched key lookup translates the physical site's directory code to its
stable site ID. The fields already use the final owning cell's absolute addresses.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.FinalTies

open Crossing CellAddresses CellAddressCircuit CellAddressPhysical Shortening.PublicCapacity
open FrozenTape Subdivision VPVNP.VerifierNetwork ParseBatchSort
open scoped Classical

variable {s : Shape} {np C d k w : ℕ} {σ : Type*} [Fintype σ]
variable (F : CellAddressCircuit.Fields s.sites s.edges np C d k w σ) (work : Fin s.sites → Fin w → σ)
variable (occupied : Fin s.edges → σ) (portUsed : Fin np → Bool) (one : 1 < 2^w)

/-- The same stable rectangular row order used in the final native geometry template. -/
def tieSchema (m np w : ℕ) := NineWords.schema (staticRows m np) w

/-- The uniform numeric emitter of absolute binding records. -/
noncomputable def numeric :=
  Classical.choose (Layer.emit d w (inputs F work occupied portUsed))

local notation3 "f" => numeric F work occupied portUsed

/-- Wiring all numeric outputs into an immutable nine-field tape. -/
noncomputable def codeTape := NineWords.adapt (f)

/-- The ordinal site code fits the width already allocated for the injective public codebook. -/
def ordinalCode : Fin s.sites ↪ Fin (2^d) :=
  Fin.castLEEmb (by simpa only [Fintype.card_fin] using Fintype.card_le_of_injective _ F.sites.injective)

/-- Restore the actual sparse site ID in every active row, including IDs with leading zeros. -/
noncomputable def indexTape :=
  (FrozenTape.rekey F.sites (ordinalCode F)).subst (codeTape F work occupied portUsed)

private theorem numeric_flag (x : σ → Bool) (r : Row s.edges np) :
    (f).eval x (r,.inl ()) = true ↔ enabled F occupied portUsed x r = true := by
  rw [numeric,(Classical.choose_spec (Layer.emit d w (inputs F work occupied portUsed))).2.1 x r,input_flag]
  rcases r with ⟨i,side⟩ | p <;> simp [enabled]

private theorem numeric_owner (x : σ → Bool) (r : Row s.edges np) :
    value (fun j => (f).eval x (r,.inr (.inl j))) = FinalTies.owner F x r := by
  simp only [numeric,(Classical.choose_spec (Layer.emit d w (inputs F work occupied portUsed))).2.2.1]
  exact input_owner F work occupied portUsed x r

variable {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (rows : Rows s N) (ports : P ↪ Fin np) (cell : N.Site → Fin C) (state : N.Site → Site)
variable {x : σ → Bool} (rep : Represents N cell (fun u => (state u).size) rows.site rows.edge ports F x)
variable (fit : ∀ c, guessedSize N cell c+siteSize N cell c (fun u => (state u).size)+suppliedSize N cell c < 2^w)
variable (size : ∀ v, (state v).incoming = incoming N v)
variable (hw : ∀ v, value (x ∘ work (rows.site v)) = (state v).work)
variable (used : ∀ i, x (occupied i) = true ↔ i ∈ Set.range rows.edge)
variable (live : ∀ i, portUsed i = true ↔ i ∈ Set.range ports)
local notation3 "ties" => fun v => Placement.ties N cell (cell v) rows.site rows.edge ports state ⟨v,rfl⟩

include one rep fit size hw used live in
/-- Physical key fields and nine numeric words realize all of the true final bindings,
in stable cable-then-port order. Every enabled row names an attained real site. -/
theorem codeTape_section :
    (tieSchema s.edges np w).Section ((codeTape F work occupied portUsed).eval x)
      ((rows.site.trans F.sites).trans Fin.valEmbedding) ties := by
  let key := fun v => (F.sites (rows.site v)).val
  have data := Views.EndpointData.of_rep N F rows.site rows.edge ports rep
  constructor
  · intro t _ alive
    simp only [codeTape,NineWords.adapt,Frame.select_eval,NineWords.pin] at alive
    obtain ⟨v,r,rfl⟩ := (enabled_iff F occupied portUsed rows ports data used live t).mp
      ((numeric_flag F work occupied portUsed x t).mp alive)
    refine ⟨v,?_⟩
    simp only [FrozenTape.owner,codeTape,NineWords.adapt,Frame.select_eval,NineWords.pin,numeric_owner]
    exact incidence_owner F rows ports data v r
  · intro v
    rw [tieSchema,codeTape,NineWords.atSite]
    let keep := fun r => (f).eval x (r,.inl ()) && decide
      (value (fun j => (f).eval x (r,.inr (.inl j))) = key v)
    have correct (r) : keep r = true ↔ ∃ a, Gates.nameOld rows ports v a = r := by
      simp only [keep,Bool.and_eq_true,decide_eq_true_eq,numeric_flag,numeric_owner]
      simpa only [atKey,Bool.and_eq_true,decide_eq_true_eq,key] using atKey_iff F occupied portUsed rows ports data used live v r
    change ((staticRows s.edges np).filter keep).map _ = _
    rw [selected_names rows ports v keep correct]
    simp only [Placement.ties,List.map_map]
    apply List.map_congr_left
    intro r _
    have room := address_room rows ports cell state F work occupied portUsed rep fit size hw v r
    have cmd := command_eq rows ports cell state F work occupied portUsed rep fit size hw v r
    exact ((Classical.choose_spec (Layer.emit d w (inputs F work occupied portUsed))).2.2.2
      x (Gates.nameOld rows ports v r) one room.1 room.2).trans (congrArg marked cmd)


include one rep fit size hw used live in
/-- The final template can read the complete owner and absolute-binding image directly
by the site's ordinary sparse ID, independently of its source codebook. -/
theorem indexTape_section :
    (tieSchema s.edges np w).Section ((indexTape F work occupied portUsed).eval x)
      (rows.site.trans Fin.valEmbedding) ties := by
  let S := tieSchema s.edges np w
  let old := codeTape F work occupied portUsed
  have physical := codeTape_section F work occupied portUsed one N rows ports cell state rep fit size hw used live
  have prior : S.Block (old.eval x) (fun v => (F.sites (rows.site v)).val) (fun v => (ties v).map marked) := physical
  have transferred := prior.rekey S F.sites (ordinalCode F)
  let tr := FrozenTape.rekey (R:=Row s.edges np) (B:=Row s.edges np × Fin 9 × Fin w) F.sites (ordinalCode F)
  have ev : (tr.subst old).eval x = tr.eval (old.eval x) := funext fun i => Frame.subst_eval _ _ _ _
  change S.Section ((tr.subst old).eval x) _ _
  rw [ev]
  exact transferred

/-- The complete index tape charges only the physical tie encoder and one batched
lookup of the sparse original site IDs. -/
theorem indexTape_size :
    (indexTape F work occupied portUsed).size ≤
      (inputs F work occupied portUsed).size + 1 + (2*s.edges+np)*(4500*(w+1)^2) +
        FrozenTape.lookupCost s.sites (Fintype.card (Row s.edges np)) d d := by
  have emitCost := (Classical.choose_spec (Layer.emit d w (inputs F work occupied portUsed))).1
  have lookup := FrozenTape.rekey_size (R:=Row s.edges np) (B:=Row s.edges np × Fin 9 × Fin w) F.sites (ordinalCode F)
  simp only [indexTape,Frame.subst_size,codeTape,NineWords.adapt_size,numeric]
  exact Nat.add_le_add (by simpa only [Row,Gates.Old,Fintype.card_sum,Fintype.card_prod,Fintype.card_bool,
    Fintype.card_fin,Nat.mul_comm s.edges 2] using emitCost) lookup

end Packing.Inherited.FinalTies

end BorderVNP
end Computability
end OAI
