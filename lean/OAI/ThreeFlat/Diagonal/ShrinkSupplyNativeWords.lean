import OAI.ThreeFlat.Diagonal.ShrinkSupplySend

namespace OAI
/-! # Supply metadata points to the exact balanced edge in the tree's fresh callback -/
namespace ThreeFlat.Diagonal.CompressorPacking.SupplySend
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM PrivateRAM RAM.PhysicalPinsExpr Native Native.Placement Native.Graph Native.ShrinkStage
open scoped Classical Fin.NatCast
variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {W n N t l pad : ℕ}
variable {S : Graph.Stage} {P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors}
variable {E : Codec B W S.colors t l} {b : B ≃ Fin N} {bound : ∀k,S.pieces k≤S.pieceRadix} {lay : Bool} {hc : 2≤S.colors}
variable {ptr : Formula n} {data : Param→Word W} {mem : Memory W} {vs : Fin n→Word W}
variable {prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors→ℕ} {supply : P.Motif→Fin 8→ℕ}
local notation "V" => Formula.value data mem vs
set_option quotPrecheck false in
local notation "order" => edgeOrder P (baseNat b) (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound

private theorem piece_fields_cast {old new count : ℕ} (same : old=new)
    (positive : 0<count) (j : Fin new) :
    let oldPart := (SlotEnergy.pieceIndex old count positive).symm (Fin.cast same.symm j)
    let newPart := (SlotEnergy.pieceIndex new count positive).symm j
    oldPart.1 = newPart.1 ∧ oldPart.2.val = newPart.2.val := by
  cases same
  exact ⟨rfl,rfl⟩

theorem native_fresh_words (files : BitOrigins.SupplyFiles S P E b bound lay hc ptr data mem vs prior supply pad)
    (ok : TagConditions P.slots (shift P) P.offset) (positive : ∀k,0<S.pieces k)
    (wire : CrossEdge P lay) (e : Ends (Formula n)) (enc : e.map V=encodeEnds P E wire.1.val)
    (party edge atBit : Formula n) (u : Fin 6) (col : Fin 4) (h8 : 8≤2^W) (bits : 2^S.colors<2^W)
    (counts : S.pieces (typeIndex P binary_neg ok lay wire)<2^W) (hb : supply wire.1 wire.2.val<2^W)
    (j : Fin (supply wire.1 wire.2.val)) (he : V edge=(wire.2.val.val:Word W))
    (hp : V party=(u.val:Word W)) (hj : V atBit=(j.val:Word W))
    (incident : u=ShrinkMotif.supplySrc wire.2.val ∨ u=ShrinkMotif.supplyDst wire.2.val) :
    let kind:=typeIndex P binary_neg ok lay wire
    let part:=(SlotEnergy.pieceIndex (supply wire.1 wire.2.val) (S.pieces kind) (positive kind)).symm j
    let physical:=(allPieceSlots P binary_neg ok lay S.pieces order hc pad) (.inl ⟨wire,part.1⟩)
    let side:=decide (u≠ShrinkMotif.supplySrc wire.2.val)
    V (BitOrigins.supplyAddress ptr S lay e party edge atBit col)=
      (![2,0,(halfOrdinal files.graph physical side:Word W),(part.2.val:Word W)] : Fin 4→Word W) col := by
  let kind:=typeIndex P binary_neg ok lay wire
  let i:=ShrinkMotif.survivor lay kind
  have hi : i=wire.2.val :=
    congrArg Subtype.val ((crossTypeEquiv P binary_neg ok lay wire.1).apply_symm_apply wire.2)
  let index:=j.cast (congrArg (supply wire.1) hi.symm)
  have read:=files.retained_word wire.1 e enc party edge atBit kind u col h8 bits counts (positive kind)
    (by simpa only [show ShrinkMotif.survivor lay kind=wire.2.val from hi] using hb)
    index (by simpa only [show ShrinkMotif.survivor lay kind=wire.2.val from hi] using he) hp hj
    (by simpa only [show ShrinkMotif.survivor lay kind=wire.2.val from hi] using incident)
  dsimp only at read ⊢
  rw [numbered_half]
  change ShrinkMotif.survivor lay kind=wire.2.val at hi
  have same := piece_fields_cast (congrArg (supply wire.1) hi) (positive kind) j
  simp only [index,same.1,same.2,hi,files.full] at read
  by_cases side : u=ShrinkMotif.supplySrc wire.2.val <;>
    simpa [side] using read


end ThreeFlat.Diagonal.CompressorPacking.SupplySend

end OAI
