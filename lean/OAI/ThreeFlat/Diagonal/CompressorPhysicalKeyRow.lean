import OAI.ThreeFlat.Diagonal.CompressorPhysicalGraphRow

namespace OAI
/-! # Materialized source keys for the successor width scan -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement Graph
open scoped Classical Fin.NatCast
variable {B H : Type*} [AddCommGroup H] [Fintype B] [Fintype H] {w N t l n : ℕ}
variable (S : Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors) (b : B ≃ Fin N)
variable (bound : ∀i,S.pieces i≤S.pieceRadix) (lay : Bool) (hc : 2≤S.colors)
local notation "tagged" => tagNumber (t:=t) b
local notation "deg" => (liveDegree S+n)

noncomputable def sourceKey (p : (B × BitWord t) × Fin deg) : ℕ :=
  match CompressorRefresh.slotCases _ (liveDegree S) n p with
  | .inl u => edgeId S P (baseNat b) bound ((ordinalOf S P (baseNat b) bound lay false hc).symm u)
  | .inr _ => 0

@[simp] theorem sourceKey_left (u : (B × BitWord t) × Fin (liveDegree S)) :
    sourceKey S P b bound lay hc (CompressorRefresh.leftRow (b:=n) u) =
      edgeId S P (baseNat b) bound ((ordinalOf S P (baseNat b) bound lay false hc).symm u) := by
  simp [sourceKey,CompressorRefresh.leftRow]

@[simp] theorem sourceKey_right (u : (B × BitWord t) × Fin n) :
    sourceKey S P b bound lay hc (CompressorRefresh.rightRow (a:=liveDegree S) u)=0 := by
  simp [sourceKey,CompressorRefresh.rightRow]

variable (cell : Word w) (pub : Fin 1 → Word w) (m : Memory w) (vs : Fin 1 → Word w)
local notation "V" => Formula.value (fun _=>cell) m vs
variable (E : Codec B w S.colors t l) (R : ArcReads P E ((oldColumns (Demand.formulaOps 1) ptr).map (Formula.value (fun _ => cell) m vs)) m)
variable (hb : ∀z,E.base z=((b z).val:Word w)) (hi : Function.Injective E.base)
variable (fit : ∀e,edgeId S P (baseNat b) bound e<2^w)
include pub R hb hi fit in
theorem physical_key_read (good : TagConditions P.slots (shift P) P.offset)
    (rad : (radices o ptr S).map V = rowRadices (w:=w) (t:=t) (l:=l) S)
    (liveEq : S.liveDegree=liveDegree S) (degreeEq : S.outputDegree=deg)
    (chosen : V (f selected)=if lay then 1 else 0) (one : (1:Word w)≠0)
    (degFit : deg<2^w) (tagsFit : 2^t<2^w)
    (basesFit : ∀v : B × BitWord t,(E.base v.1).val*2^t+(tagOrdinal t v.2).val<2^w)
    (start : ℕ) (fits : (N*2^t)*deg<2^w) (origin : V (f keys)=(start:Word w))
    (p : (B × BitWord t) × Fin deg)
    (here : vs 0=((start+SlotImage.ordinal tagged p:ℕ):Word w)) :
    V (graph S true)=(sourceKey S P b bound lay hc p:Word w) := by
  rw [identifier_read cell m vs S lay chosen one]
  have addr := split_address cell m vs (f keys) start (tagged p.1).val p.2.val S.outputDegree
    (degreeEq.trans_lt degFit) (p.2.isLt.trans_le degreeEq.ge)
    (by rw [degreeEq]; exact (SlotImage.ordinal_lt tagged p).trans fits) origin
    (by simpa only [SlotImage.ordinal,degreeEq] using here)
  have liveFits : liveDegree S<2^w := (Nat.le_add_right _ n).trans_lt degFit
  obtain ⟨x,hx⟩ := (CompressorRefresh.slotCases (B × BitWord t) (liveDegree S) n).symm.surjective p
  cases x with
  | inl u =>
    change CompressorRefresh.leftRow u=p at hx
    subst p
    rw [sourceKey_left]
    let e := (ordinalOf S P (baseNat b) bound lay false hc).symm u
    rw [show (edgeId S P (baseNat b) bound e:Word w)=idEmbedding S P (baseNat b) bound fit e by
      apply Fin.ext
      exact Fin.val_cast_of_lt (fit e)]
    apply retained_field cell pub m vs S P E R (baseNat b) hb hi bound fit lay hc good one rad
      liveFits.le tagsFit basesFit false u .identifier (f keys)
      (addr.1.trans (packed_word S b E hb u.1).symm) addr.2
    rw [liveEq]
    change (u.2.val:Word w).val<(liveDegree S:Word w).val
    rw [Fin.val_cast_of_lt (u.2.isLt.trans liveFits),Fin.val_cast_of_lt liveFits]
    exact u.2.isLt
  | inr u =>
    change CompressorRefresh.rightRow u=p at hx
    subst p
    rw [sourceKey_right,Nat.cast_zero]
    apply padded_field cell m vs S lay false .identifier (f keys) _ _ addr.1 addr.2
    rw [liveEq]
    have f : liveDegree S+u.2.val<2^w := (Nat.add_lt_add_left u.2.isLt _).trans degFit
    change ¬ ((liveDegree S+u.2.val:ℕ):Word w).val<(liveDegree S:Word w).val
    rw [Fin.val_cast_of_lt f,Fin.val_cast_of_lt liveFits]
    omega


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Template

end OAI
