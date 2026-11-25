import OAI.Hierarchy.ProtocolRAMCalendarStripForestHeader
import OAI.Hierarchy.ProtocolRAMStripTreeFinalFits

namespace OAI
/-! # Address and catalogue bounds for catalyst operands at the mounted directory -/

noncomputable section
namespace Hierarchy.ProtocolRAM.Calendar.StripChart
open AdaptiveProbe ProbeStage CoreBoard CatalogueRows BoughtSockets StockCommit StripDirectory PortPadding
open Computability.VPVNP.BurstRAM
open scoped Classical Fin.CommRing
open private port_selections mate_range from OAI.Hierarchy.ProtocolRAMStripTreeFinalFits
attribute [local irreducible] permutationFabric

variable {z W k q depth w limit : ℕ}
variable (s : Boards z (2^W) k q depth) (c : Mesh) (b : CatalogueRows.Board)
  (G : PortBanks ((c.inject+c.cool)*c.outerFuel)) (H : PortHeader) (old : Traversals) (a : Attempt)
local notation "N" => Stages z (2^W)
local notation "D" => max (Fintype.card (PayloadRole N k)) (Fintype.card (PurchasedRole depth k))

set_option maxHeartbeats 800000 in
private theorem pair_fields (headerBound : H.stop ≤ limit) (word : limit < 2^w)
    (ports : DatePortFits s c b G w limit a) (mask mate : Expr)
    (issued : (forestAtHeader s c b G H old a).catalystMate = some (mask,mate)) :
    let raw := chooseField D 0 (fun i => (radiusMate s c b G a i).atRow H.ballTerm) H.fieldTerm
    mask.Fits w limit ∧ mate = b.checkedEdge raw ∧ raw.Fits w limit := by
  intro raw
  have inputs := H.input_ends headerBound
  have ball := H.ballTerm.fits_of_inputEnd inputs.1 word
  have field := H.fieldTerm.fits_of_inputEnd inputs.2.1 word
  obtain ⟨_,mates,bits⟩ := port_selections (z:=z) (W:=W) (k:=k) (q:=q) (depth:=depth) s c b G a ports
  change some (chooseField D 0 (catalystFlag (z:=z) (W:=W) (k:=k) (depth:=depth) a) H.fieldTerm,
    b.checkedEdge raw) = some (mask,mate) at issued
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj (Option.some.inj issued)
  exact ⟨choose_fits_bound _ _ _ _ bits field,rfl,
    choose_fits_bound _ _ _ _ (fun i => fits_atRow _ _ (mates i) ball) field⟩

/-- The signed role and the unchecked mate only read the mounted port banks and the dated
radius ports. Every possible mate names an original core row or the catalogue sentinel. -/
theorem forest_pair_at (headerBound : H.stop ≤ limit) (word : limit < 2^w)
    (room : b.rows < 2^w) (live : 0 < b.coreRows) (ports : DatePortFits s c b G w limit a)
    (mask mate : Expr) (issued : (forestAtHeader s c b G H old a).catalystMate = some (mask,mate)) :
    mask.Fits w limit ∧ ∃ raw : Expr, mate = b.checkedEdge raw ∧ raw.Fits w limit ∧
      ∀ (m : Memory w) (r : Word w), (raw.eval m r).val < b.coreRows ∨ (raw.eval m r).val = b.rows := by
  obtain ⟨maskFits,guarded,rawFits⟩ := pair_fields s c b G H old a headerBound word ports mask mate issued
  refine ⟨maskFits,_,guarded,rawFits,?_⟩
  intro m r
  apply choice_has 0 _ _ m r (fun x => x.val < b.coreRows ∨ x.val = b.rows) (Or.inl live)
  intro i
  rw [eval_atRow]
  cases a <;> simp only [radiusMate,extend] <;> split
  all_goals first | exact mate_range _ b _ _ _ room | exact Or.inr (Fin.val_cast_of_lt room)

/-- The final catalogue guard also fits when its retained flag is in the funded arena. -/
theorem forest_pair_fits (headerBound : H.stop ≤ limit) (word : limit < 2^w)
    (flag : b.bought.flag.Fits w limit) (ports : DatePortFits s c b G w limit a) (mask mate : Expr)
    (issued : (forestAtHeader s c b G H old a).catalystMate = some (mask,mate)) :
    mask.Fits w limit ∧ mate.Fits w limit := by
  obtain ⟨maskFits,guarded,rawFits⟩ := pair_fields s c b G H old a headerBound word ports mask mate issued
  exact ⟨maskFits,guarded.symm ▸ b.checked_fits _ rawFits flag⟩

end Hierarchy.ProtocolRAM.Calendar.StripChart
end

end OAI
