import OAI.ThreeFlat.Diagonal.CompressorOutputRows
import OAI.ThreeFlat.Diagonal.CompressorPostKey

namespace OAI
/-! # Native post-sweeps materialize the selected subdivided physical slot graph -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident
open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM RAM RAM.DescriptorScan Placement Graph
open scoped Classical Fin.NatCast
variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {w N t l pad : ℕ}
variable {S : Stage} {P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors} {b : B ≃ Fin N}
variable {bound : ∀i,S.pieces i≤S.pieceRadix} {lay : Bool} {hc : 2≤S.colors}
variable (good : TagConditions P.slots (shift P) P.offset) (ht : 0<t)
variable {E : Codec B w S.colors t l}
variable {prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ} {supply : P.Motif → Fin 8 → ℕ}
variable {p : Pointers} {cell : Word w} {m : Memory w}
variable (h : Fits (pad:=pad) S P b bound E supply) (z : Separation (w:=w) (dims S N t l) p cell.val)
variable (I : Input S P b hc lay p cell prior supply m)
include h z I in
private theorem graph_spec (pub : Fin 1 → Word w) :
    FileSpec cell pub (Template.graph S false) nextGraph graphWords m p.newGraph
      (6*(outgoing S N t p).rows) (graphFile (pad:=pad) S P b bound lay hc good ht p.newGraph) := by
  let C := outgoing S N t p
  let tagged := Template.tagNumber (t:=t) b
  let deg := liveDegree S + pad
  have rows : C.rows = N*2^t*deg := congrArg (fun d => N*2^t*d) h.degree
  have fit : p.newGraph + 6*C.rows < 2^w := z.graphEnd
  have gk : p.newGraph + 6*C.rows ≤ p.keys := z.graphKey
  have kw : p.keys + C.rows ≤ p.newWidths := z.keyWidth
  have window : p.newGraph + 6*C.rows ≤ p.newWidths + C.rows*2^l :=
    gk.trans ((Nat.le_add_right p.keys C.rows).trans (kw.trans (Nat.le_add_right _ _)))
  change FileSpec _ _ _ _ _ _ _ (6*C.rows) _
  rw [rows]
  let word := fun u : (Bool × Fin 3) × ((B × BitWord t) × Fin deg) => (SlotImage.fields (successor (pad:=pad) S P b bound lay hc good ht)
    tagged (tagOrdinal l) u.2 u.1.1 u.1.2 : Word w)
  apply PostImage.file_spec cell pub (Template.graph S false) nextGraph graphWords m p.newGraph
    (PostImage.graphNumbers (d:=deg) tagged) word (by simpa only [rows] using fit)
  · have baseFit : p.newGraph < 2^w := (Nat.le_add_right _ _).trans_lt fit
    exact (congrArg Fin.val (I.hdr.native (20:Fin 34))).trans (Fin.val_cast_of_lt baseFit)
  · have countFit : 6*C.rows < 2^w := (Nat.le_add_left _ _).trans_lt fit
    have header := congrArg Fin.val (I.hdr.native (21:Fin 34))
    change (headerRead m cell graphWords).val=((6*C.rows:ℕ):Word w).val at header
    rwa [Fin.val_cast_of_lt countFit,rows] at header
  · intro u alt frame
    have keep : Input S P b hc lay p cell prior supply alt :=
      I.frame (fun a r => z.agree p.newGraph (6*C.rows) le_rfl window
        (by simpa only [rows] using frame) r)
    exact graph_row h z keep good ht pub u

include good h z I in
private theorem key_spec (pub : Fin 1 → Word w) :
    FileSpec cell pub (Template.graph S true) keys nextSlots m p.keys
      (outgoing S N t p).rows (keyFile (pad:=pad) S P b bound lay hc p.keys) := by
  let C := outgoing S N t p
  let tagged := Template.tagNumber (t:=t) b
  let deg := liveDegree S + pad
  have rows : C.rows = N*2^t*deg := congrArg (fun d => N*2^t*d) h.degree
  have fit : p.keys + C.rows < 2^w := z.keyEnd
  have gk : p.newGraph + 6*C.rows ≤ p.keys := z.graphKey
  have kw : p.keys + C.rows ≤ p.newWidths := z.keyWidth
  have start : p.newGraph ≤ p.keys := (Nat.le_add_right _ _).trans gk
  have window : p.keys + C.rows ≤ p.newWidths + C.rows*2^l := kw.trans (Nat.le_add_right _ _)
  change FileSpec _ _ _ _ _ _ _ C.rows _
  rw [rows]
  apply PostImage.file_spec cell pub (Template.graph S true) keys nextSlots m p.keys
    (PostImage.slotNumbers (d:=deg) tagged) (fun u => (Template.sourceKey S P b bound lay hc u : Word w))
    (by simpa only [rows] using fit)
  · have baseFit : p.keys < 2^w := (Nat.le_add_right _ _).trans_lt fit
    exact (congrArg Fin.val (I.hdr.native (23:Fin 34))).trans (Fin.val_cast_of_lt baseFit)
  · have countFit : C.rows < 2^w := (Nat.le_add_left _ _).trans_lt fit
    have header := congrArg Fin.val (I.hdr.native (22:Fin 34))
    change (headerRead m cell nextSlots).val=(C.rows:Word w).val at header
    rwa [Fin.val_cast_of_lt countFit,rows] at header
  · intro u alt frame
    have keep : Input S P b hc lay p cell prior supply alt :=
      I.frame (fun a r => z.agree p.keys C.rows start window
        (by simpa only [rows] using frame) r)
    exact key_row h z keep good pub u

include h z I in
private theorem width_spec (pub : Fin 1 → Word w)
    (key : ∀ u : (B × BitWord t) × Fin (liveDegree S + pad),
      m (p.keys + SlotImage.ordinal (Template.tagNumber (t:=t) b) u) =
        (Template.sourceKey S P b bound lay hc u : Word w)) :
    FileSpec cell pub (Template.output S) nextWidths widthWords m p.newWidths
      ((outgoing S N t p).rows*2^l) (widthFile (pad:=pad) S P b bound lay hc good supply p.newWidths) := by
  let C := outgoing S N t p
  let tagged := Template.tagNumber (t:=t) b
  let deg := liveDegree S + pad
  have rows : C.rows = N*2^t*deg := congrArg (fun d => N*2^t*d) h.degree
  have fit : p.newWidths + C.rows*2^l < 2^w := z.safe
  have gk : p.newGraph + 6*C.rows ≤ p.keys := z.graphKey
  have kw : p.keys + C.rows ≤ p.newWidths := z.keyWidth
  have start : p.newGraph ≤ p.newWidths :=
    (Nat.le_add_right _ _).trans (gk.trans ((Nat.le_add_right _ _).trans kw))
  change FileSpec _ _ _ _ _ _ _ (C.rows*2^l) _
  rw [rows]
  apply PostImage.file_spec cell pub (Template.output S) nextWidths widthWords m p.newWidths
    (PostImage.edgeNumbers (d:=deg) tagged (tagOrdinal l))
    (fun e => (newWidth (pad:=pad) S P b bound lay hc good supply e : Word w))
    (by simpa only [rows] using fit)
  · have baseFit : p.newWidths < 2^w := (Nat.le_add_right _ _).trans_lt fit
    exact (congrArg Fin.val (I.hdr.native (24:Fin 34))).trans (Fin.val_cast_of_lt baseFit)
  · have countFit : C.rows*2^l < 2^w := (Nat.le_add_left _ _).trans_lt fit
    have header := congrArg Fin.val (I.hdr.native (25:Fin 34))
    change (headerRead m cell widthWords).val=((C.rows*2^l:ℕ):Word w).val at header
    rwa [Fin.val_cast_of_lt countFit,rows] at header
  · intro e alt frame
    have keep : Input S P b hc lay p cell prior supply alt :=
      I.frame (fun a r => z.agree p.newWidths (C.rows*2^l) start le_rfl
        (by simpa only [rows] using frame) r)
    apply width_row h z keep good pub e
    have ix : SlotImage.ordinal tagged e.1 < C.rows := rows ▸ SlotImage.ordinal_lt tagged e.1
    exact (frame _ (Or.inl ((Nat.add_lt_add_left ix p.keys).trans_le kw))).trans (key e.1)

include h z I in
theorem materialized_with_keys (pub : Fin 1 → Word w)
    (fieldCap : ∀ u rev j, SlotImage.fields (successor (pad:=pad) S P b bound lay hc good ht)
      (Template.tagNumber (t:=t) b) (tagOrdinal l) u rev j < 2^w)
    (widthCap : ∀ u, newWidth (pad:=pad) S P b bound lay hc good supply u < 2^w) :
    SlotImage.Stored (successor (pad:=pad) S P b bound lay hc good ht)
      (Template.tagNumber (t:=t) b) (tagOrdinal l) (outgoing S N t p)
      (fun i => (((post cell S).execute cell pub m).2 i).val)
      (newWidth (pad:=pad) S P b bound lay hc good supply) ∧
    ∀ u : (B × BitWord t) × Fin (liveDegree S + pad),
      ((post cell S).execute cell pub m).2 (p.keys + SlotImage.ordinal (Template.tagNumber (t:=t) b) u) =
      (Template.sourceKey S P b bound lay hc u:Word w) := by
  let deg := liveDegree S + pad
  let tagged := Template.tagNumber (t:=t) b
  let C := outgoing S N t p
  let G := successor (pad:=pad) S P b bound lay hc good ht
  let width := newWidth (pad:=pad) S P b bound lay hc good supply
  let gf:=graphFile (w:=w) (pad:=pad) S P b bound lay hc good ht C.graph
  let kf:=keyFile (w:=w) (pad:=pad) S P b bound lay hc p.keys
  let wf:=widthFile (w:=w) (pad:=pad) S P b bound lay hc good supply C.widths
  let gm:=PostImage.graphMem C m gf
  let km:=PostImage.keyMem C m p.keys gf kf
  have rows : C.rows=N*2^t*deg := congrArg (fun d=>N*2^t*d) h.degree
  have gk := z.graphKey
  have kw := z.keyWidth
  change C.graph+6*C.rows≤p.keys at gk
  change p.keys+C.rows≤C.widths at kw
  have ends := z.safe
  change C.widths+C.rows*2^l<2^w at ends
  have keyStart : C.graph ≤ p.keys := (Nat.le_add_right C.graph (6*C.rows)).trans gk
  have widthStart : C.graph ≤ C.widths := keyStart.trans ((Nat.le_add_right p.keys C.rows).trans kw)
  have keyWindow : p.keys + C.rows ≤ C.widths + C.rows*2^l :=
    kw.trans (Nat.le_add_right C.widths (C.rows*2^l))
  have graphWindow : C.graph + 6*C.rows ≤ C.widths + C.rows*2^l :=
    gk.trans ((Nat.le_add_right p.keys C.rows).trans keyWindow)
  have Ig : Input S P b hc lay p cell prior supply gm :=
    I.frame (z.fill C.graph (6*C.rows) le_rfl graphWindow gf m)
  have Ik : Input S P b hc lay p cell prior supply km :=
    Ig.frame (z.fill p.keys C.rows keyStart keyWindow kf gm)
  have gRun := graph_spec good ht h z I pub
  have kRun := key_spec good h z Ig pub
  have keyWords (u : (B × BitWord t) × Fin deg) :
      km (p.keys + SlotImage.ordinal tagged u) = (Template.sourceKey S P b bound lay hc u : Word w) := by
    have ix : SlotImage.ordinal tagged u < C.rows := rows ▸ SlotImage.ordinal_lt tagged u
    have inside := And.intro (Nat.le_add_right p.keys (SlotImage.ordinal tagged u)) (Nat.add_lt_add_left ix p.keys)
    calc
      _ = kf (p.keys + SlotImage.ordinal tagged u) := ite_eq_left inside
      _ = _ := key_at S P b bound lay hc p.keys u
  have wRun := width_spec good h z Ik pub keyWords
  constructor
  · apply PostImage.stored G tagged (tagOrdinal l) width C S cell pub m p.keys gf kf wf rows gk kw gRun kRun wRun
    · intro u rev j
      rw [show gf (SlotImage.cell C tagged u rev j)=_ from graph_at S P b bound lay hc good ht C rows u rev j]
      exact Fin.val_cast_of_lt (fieldCap u rev j)
    · intro u
      rw [show wf (C.widths+SlotImage.edgeOrdinal tagged (tagOrdinal l) u)=_ from
        width_at S P b bound lay hc good supply C.widths u]
      exact Fin.val_cast_of_lt (widthCap u)
  · intro u
    have ix : SlotImage.ordinal tagged u < C.rows := rows ▸ SlotImage.ordinal_lt tagged u
    have low := Nat.le_add_right p.keys (SlotImage.ordinal tagged u)
    have high := Nat.add_lt_add_left ix p.keys
    exact (PostImage.retains_keys C S cell pub m p.keys (2^l) gf kf wf gRun kRun wRun
      _ low high (high.trans_le kw)).trans (key_at S P b bound lay hc p.keys u)

include h z I in
theorem materialized (pub : Fin 1 → Word w)
    (fieldCap : ∀ u rev j, SlotImage.fields (successor (pad:=pad) S P b bound lay hc good ht)
      (Template.tagNumber (t:=t) b) (tagOrdinal l) u rev j < 2^w)
    (widthCap : ∀ u, newWidth (pad:=pad) S P b bound lay hc good supply u < 2^w) :
    SlotImage.Stored (successor (pad:=pad) S P b bound lay hc good ht)
      (Template.tagNumber (t:=t) b) (tagOrdinal l) (outgoing S N t p)
      (fun i => (((post cell S).execute cell pub m).2 i).val)
      (newWidth (pad:=pad) S P b bound lay hc good supply) :=
  (materialized_with_keys good ht h z I pub fieldCap widthCap).1


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.Resident

end OAI
