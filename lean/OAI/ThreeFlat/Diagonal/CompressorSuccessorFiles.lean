import OAI.ThreeFlat.Diagonal.CompressorResidentLayout

namespace OAI
/-! # The three typed source-major files emitted for a selected shrinking graph -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM.PhysicalPinsExpr Placement Graph
open scoped Classical Fin.NatCast
namespace Resident
variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {w N t l pad : ℕ}
variable (S : Stage) (P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors) (b : B ≃ Fin N)
variable (bound : ∀i,S.pieces i≤S.pieceRadix) (lay : Bool) (hc : 2≤S.colors)
variable (good : TagConditions P.slots (shift P) P.offset) (ht : 0<t)
variable (supply : P.Motif → Fin 8 → ℕ)
local notation "tagged" => Template.tagNumber (t:=t) b
local notation "deg" => liveDegree S+pad

noncomputable def successor : LiftedSlots (B × BitWord t) deg (BitWord l) :=
  CompressorRefresh.union (shrinkingGraph P lay S.pieces
      (edgeOrder P (baseNat b) (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound) hc binary_neg good)
    (tagPadding (V:=B) (L:=BitWord l) (tagOne ht) (tagOne_ne ht) pad)

noncomputable def newWidth : SlotImage.Edge (B × BitWord t) (BitWord l) deg → ℕ :=
  SlotRefinement.actualWidth (fun e=>S.pieces (typeIndex P binary_neg good lay e))
    (fun e : CrossEdge P lay=>supply e.1 e.2) (allPieceSlots P binary_neg good lay S.pieces
      (edgeOrder P (baseNat b) (tagOrdinal t).toEmbedding S.pieces S.pieceRadix bound) hc pad)

local notation "graph" => successor (pad:=pad) S P b bound lay hc good ht
local notation "width" => newWidth (pad:=pad) S P b bound lay hc good supply

noncomputable def graphFile (lo : ℕ) : ℕ → Word w :=
  PostImage.file (PostImage.graphNumbers (d:=deg) tagged) (fun u=>
    (SlotImage.fields graph tagged (tagOrdinal l) u.2 u.1.1 u.1.2:Word w)) lo

noncomputable def keyFile (lo : ℕ) : ℕ → Word w :=
  PostImage.file (PostImage.slotNumbers (d:=deg) tagged) (fun p=>(Template.sourceKey S P b bound lay hc p:Word w)) lo

noncomputable def widthFile (lo : ℕ) : ℕ → Word w :=
  PostImage.file (PostImage.edgeNumbers (d:=deg) tagged (tagOrdinal l)) (fun e=>(width e:Word w)) lo

theorem graph_at (C : SlotImage.Columns) (rows : C.rows=N*2^t*deg) (p : (B × BitWord t) × Fin deg)
    (rev : Bool) (j : Fin 3) :
    graphFile (w:=w) (pad:=pad) S P b bound lay hc good ht C.graph (SlotImage.cell C tagged p rev j)=
      (SlotImage.fields graph tagged (tagOrdinal l) p rev j:Word w) := by
  rw [←PostImage.graphNumbers_val tagged p rev j C rows]
  simp only [graphFile, PostImage.file_at]

theorem key_at (kb : ℕ) (p : (B × BitWord t) × Fin deg) :
    keyFile (w:=w) (pad:=pad) S P b bound lay hc kb (kb+SlotImage.ordinal tagged p)=
      (Template.sourceKey S P b bound lay hc p:Word w) := by
  rw [←PostImage.slotNumbers_val tagged p]
  simp only [keyFile, PostImage.file_at]

theorem width_at (lo : ℕ) (e : SlotImage.Edge (B × BitWord t) (BitWord l) deg) :
    widthFile (w:=w) (pad:=pad) S P b bound lay hc good supply lo (lo+SlotImage.edgeOrdinal tagged (tagOrdinal l) e)=
      (width e:Word w) := by
  rw [←PostImage.edgeNumbers_val tagged (tagOrdinal l) e]
  simp only [widthFile, PostImage.file_at]


end Resident
end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage

end OAI
