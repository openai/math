import OAI.ThreeFlat.Diagonal.CompressorMaterialized
import OAI.ThreeFlat.Diagonal.ShrinkIssuedWidth

namespace OAI
/-! # Bounds on the encoder, the three outgoing data columns and the lengths of its split pieces -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM _root_.OAI.ThreeFlat.Diagonal.CompressorPacking.Native.Graph
open scoped Classical
variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {N t l pad : ℕ}
variable (S : Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors) (b : B ≃ Fin N)
variable (bound : ∀i,S.pieces i≤S.pieceRadix) (lay : Bool) (hc : 2≤S.colors)
variable (good : TagConditions P.slots (shift P) P.offset) (ht : 0<t)
variable (supply : P.Motif → Fin 8 → ℕ)
local notation "deg" => liveDegree S+pad

private theorem append_lt {q Q r : ℕ} (small : q<Q) (i : Fin r) : appendKey q i<Q*r := by
  unfold appendKey
  calc
    q*r+i.val < q*r+r := Nat.add_lt_add_left i.isLt _
    _ = (q+1)*r := (Nat.succ_mul ..).symm
    _ ≤ Q*r := Nat.mul_le_mul_right r small

def keyBound (S : Stage) (N t : ℕ) := N*2^t*S.degree*2^S.colors*S.degree*4*S.pieceRadix

omit [Fintype B] [Fintype H] in
theorem edgeId_le (u : ShrinkEdge P S.pieces) :
    edgeId S P (baseNat b) bound u≤keyBound S N t := by
  have root:=((b u.2.1.val.val.1.1.1).isLt)
  have k:=append_lt root ((tagOrdinal t) u.2.1.val.val.1.1.2.1)
  have j:=append_lt k u.2.1.val.val.1.2
  have bits:=append_lt j (finFunctionFinEquiv (m:=2) u.2.1.val.val.2.1)
  have label:=append_lt bits (P.slotLabel u.2.1.val.val.2.2)
  have role:=append_lt label u.1
  have last:=append_lt role (u.2.2.castLE (bound u.1))
  change 1+edgeKey P (baseNat b) (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound u≤_
  rw [Nat.one_add]
  exact last

theorem boundFields {V L : Type*} {d n lanes W : ℕ} (G : LiftedSlots V d L) (v : V≃Fin n) (g : L≃Fin lanes)
    (nFit : n≤2^W) (dFit : d≤2^W) (lFit : lanes≤2^W) (u : V×Fin d) (rev : Bool) (j : Fin 3) :
    SlotImage.fields G v g u rev j<2^W := by
  fin_cases j
  · exact (v _).isLt.trans_le nFit
  · exact (SlotImage.oriented G rev u).2.isLt.trans_le dFit
  · exact (g _).isLt.trans_le lFit

theorem boundWidth {Bmax : ℕ} (size : ∀ a e,supply a e≤Bmax) (u : SlotImage.Edge (B×BitWord t) (BitWord l) deg) :
    newWidth (pad:=pad) S P b bound lay hc good supply u≤Bmax := by
  apply SlotRefinement.actualWidth_le
  intro e
  exact size _ _


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

end OAI
