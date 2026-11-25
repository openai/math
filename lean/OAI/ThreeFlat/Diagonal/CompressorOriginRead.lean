import OAI.ThreeFlat.Diagonal.CompressorBitOrigins
import OAI.ThreeFlat.Diagonal.CompressorUpperSource
import OAI.ThreeFlat.Diagonal.CompressorDemandROM

namespace OAI
/-! # Recovering the original oriented old arc from a physical incident key -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement
open scoped Classical Fin.NatCast
variable {B H : Type*} [AddCommGroup H] [Fintype B] [Fintype H] {n w N t l : ℕ}
variable (S : Graph.Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors)
variable (E : Codec B w S.colors t l) (b : B ≃ Fin N) (ptr : F n) (data : Param → Word w)
variable (mem : Memory w) (vs : Fin n → Word w)
local notation "V" => Formula.value data mem vs
local notation "f" => atField (Demand.formulaOps n) ptr
local notation "g" => oldColumns (Demand.formulaOps n) ptr
local notation "code" => demandOrdinal P (baseNat b) (Equiv.toEmbedding (tagOrdinal t)) (Equiv.toEmbedding (tagOrdinal l))

omit [Fintype B] [Fintype H] in
theorem arc_read (R : ArcReads P E ((g).map V) mem)
    (bases : ∀v,E.base v=((b v).val:Word w))
    (tagR : V (f tags)=((2^t:ℕ):Word w)) (laneR : V (f remaining)=((2^l:ℕ):Word w))
    (dims : S.degree<2^w ∧ 2^t<2^w ∧ 2^l<2^w) (bits : 2^S.colors<2^w)
    (a : Arc B H (BitWord t) (BitWord l) S.degree S.colors) (ix : F n)
    (key : V ix = (code a:Word w)) (fits : code a<2^w) :
    (oldArc ptr S ix).map V=encodeEnds P E a := by
  let q := (a.1,a.2.2)
  let hi := upperNumber P b (tagOrdinal t) (tagOrdinal l) q
  have div : code a / 2^S.colors=hi.val := upperNumber_physical P b _ _ a
  have high : hi.val<2^w := div ▸ (Nat.div_le_self _ _).trans_lt fits
  have mod : code a % 2^S.colors = (tagOrdinal S.colors a.2.1).val := by
    change appendKey _ (tagOrdinal S.colors a.2.1) % _ = _
    simp [appendKey,Nat.add_mod,Nat.mod_eq_of_lt (tagOrdinal S.colors a.2.1).isLt]
  have lo : (tagOrdinal S.colors a.2.1).val <2^w :=
    (tagOrdinal S.colors a.2.1).isLt.trans bits
  have divWord : V (.op .div ix (.lit (2^S.colors)))=(hi.val:Word w) := by
    apply Fin.ext
    simp [Formula.value,BinaryOp.eval,key,Fin.val_cast_of_lt fits,Fin.val_cast_of_lt bits,
      Fin.val_cast_of_lt high,div]
  have modWord : V (.op .mod ix (.lit (2^S.colors)))=tagWord E.colors a.2.1 := by
    rw [←Demand.tag_cast]
    apply Fin.ext
    simp [Formula.value,BinaryOp.eval,key,Fin.val_cast_of_lt fits,Fin.val_cast_of_lt bits,
      Fin.val_cast_of_lt lo,mod]
  let xt := ShrinkWidth.upperSource (layout ptr S) (f remaining) (.op .div ix (.lit (2^S.colors)))
  obtain ⟨hx,hs⟩ := ShrinkWidth.upper_code P b E (f oldWidths) (f tags) (f oldLanes) (f remaining)
    (.op .div ix (.lit (2^S.colors))) q bases tagR laneR divWord high dims
  have hsite : xt.1.site.map V=siteCode E a.1.1 := congrArg Placement.Position.site hx
  have hslot : V xt.1.slot=slotCode P a.2.2 := congrArg Placement.Position.slot hx
  let src : Position (F n) := {xt.1 with bits := .op .mod ix (.lit (2^S.colors))}
  have hp : src.map V=posCode P E (sourcePosition a) := by
    change Placement.Position.mk (xt.1.site.map V) _ _=_
    rw [hsite,modWord,hslot]
    rfl
  exact Demand.ends_code g R false src xt.2 (sourcePosition a) a.1.2 hp hs

end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.BitOrigins

end OAI
