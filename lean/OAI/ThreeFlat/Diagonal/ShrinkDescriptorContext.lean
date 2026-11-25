import OAI.ThreeFlat.Diagonal.ShrinkDescriptorPublication
import OAI.ThreeFlat.Diagonal.CompressorIncidentResident
import OAI.ThreeFlat.Diagonal.SlotImageViews

namespace OAI
/-! # The physical tables available to each shrinking-stage metadata row -/
namespace ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.DescriptorSpan

open Computability.VPVNP.Compression Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.DescriptorScan RAM.HeaderScan NavigationDirectory Resident
open scoped Classical Fin.NatCast
variable {w : ℕ} {K : ℕ} {c : Cursor} {cur : Word w} {raw m alt : Memory w}
variable {x : Dimensions}
set_option quotPrecheck false
local notation "p" => pointers K c x
local notation "extra" => ((p).costs+2*(x.motifs+1))
local notation "tail" => (allocate K c (.shrink x)).next.heap

theorem CursorSpace.saved_read (z : CursorSpace cur raw c K x) {i : ℕ}
    (h : Read x p cur.val i) : i<extra ∨ tail≤ i := by
  obtain ⟨a,b,d,e,f,g,j,k,n,v⟩:=z.allocated
  cases h with
  | current h => exact .inr (by rw [h];exact z.controls)
  | header h => left; have:=z.earlier; change c.header≤ i ∧ i<c.header+34 at h; omega
  | graph h => left; have:=z.graph; change c.graph≤ i ∧ i<c.graph+6*x.oldEdges at h; omega
  | widths h => left; have:=z.widths; change c.width≤ i ∧ i<c.width+x.oldEdges*x.originalLanes at h; omega
  | sliced h => left; rcases h with ⟨_,lt⟩;omega
  | colors h => left; rcases h with ⟨_,lt⟩;omega
  | offsets h => left; rcases h with ⟨_,lt⟩;omega
  | issued h => left; rcases h with ⟨_,lt⟩;omega

theorem descriptor_field_frame (z : CursorSpace cur raw c K x) {layout : Bool}
    (H : Scans.Header cur m c.header 63 (fields K c x layout))
    (frame : agreesOutside extra tail alt m) :
    Scans.Header cur alt c.header 63 (fields K c x layout) := by
  have before : c.heap≤extra := by simp [pointers,allocate,headerWord]; omega
  refine ⟨?_,H.fit,?_⟩
  · rw [frame _ (.inr z.controls)];exact H.pointer
  · intro i hi
    rw [frame _ (.inl (by have:=z.earlier;omega))]
    exact H.values i hi

theorem descriptor_choice_frame (z : CursorSpace cur raw c K x)
    (frame : agreesOutside extra tail alt m) {a : ℕ} (h : InSpan a (p).choices (3*x.motifs)) : alt a=m a := by
  obtain ⟨_,b,d,e,f,g,j,k,n,v⟩:=z.allocated
  exact frame a (.inl (by rcases h with ⟨_,lt⟩;omega))

theorem descriptor_counts_frame (z : CursorSpace cur raw c K x)
    (frame : agreesOutside extra tail alt m) {a : ℕ} (h : InSpan a c.dense (K*x.motifs)) : alt a=m a := by
  have bh : c.heap≤extra := by simp [pointers,allocate,headerWord]; omega
  exact frame a (.inl (h.2.trans_le (z.counts.trans bh)))

theorem descriptor_graph_frame {V L : Type*} {d N lanes : ℕ} {G : LiftedSlots V d L}
    {base : V ≃ Fin N} {lane : L ≃ Fin lanes} {width : SlotImage.Edge V L d → ℕ}
    (stored : SlotImage.Stored G base lane ⟨(p).newGraph,x.newEdges,(p).newWidths⟩ (fun i=>(m i).val) width)
    (lanes_eq : lanes=x.residual) (frame : agreesOutside extra tail alt m) :
    SlotImage.Stored G base lane ⟨(p).newGraph,x.newEdges,(p).newWidths⟩ (fun i=>(alt i).val) width := by
  have count : x.newEdges=N*d := stored.rowCount
  have graphEnd : (p).newGraph+6*x.newEdges≤extra := by simp [pointers,allocate,headerWord]; omega
  have widthEnd : (p).newWidths+N*d*lanes≤extra := by
    rw [←count,lanes_eq];simp [pointers,allocate,headerWord]
  exact stored.frame (fun i _ h=>congrArg Fin.val (frame i (.inl (h.trans_le graphEnd))))
    (fun i _ h=>congrArg Fin.val (frame i (.inl (h.trans_le widthEnd))))

variable {B H : Type} [AddCommGroup H] [Fintype B] [Fintype H] {N t l : ℕ} {S : Graph.Stage}
variable {P : PackingData B H (BitWord t) (BitWord l) S.degree S.colors}
variable {b : B ≃ Fin N} {hc : 2≤S.colors} {lay : Bool}
variable {prior : Arc B H (BitWord t) (BitWord l) S.degree S.colors → ℕ} {supply : P.Motif → Fin 8 → ℕ}
local notation "X" => dims S N t l
local notation "ptrs" => pointers K c X

omit [Fintype B] [Fintype H] in
theorem descriptor_input_frame (z : CursorSpace cur raw c K (dims S N t l)) (I : Input S P b hc lay ptrs cur prior supply m)
    (frame : agreesOutside ((ptrs).costs+2*((X).motifs+1)) (allocate K c (.shrink X)).next.heap alt m) :
    Input S P b hc lay ptrs cur prior supply alt :=
  I.frame (fun a h=>frame a (CursorSpace.saved_read z h))


end ThreeFlat.Diagonal.CompressorPacking.Native.ShrinkStage.DescriptorSpan

end OAI
