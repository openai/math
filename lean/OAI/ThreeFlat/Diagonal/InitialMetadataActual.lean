import OAI.ThreeFlat.Diagonal.InitialMetadataRead
import OAI.ThreeFlat.Diagonal.InitialMetadataKernel
import OAI.ThreeFlat.Diagonal.InitialMetadataHalf
import OAI.ThreeFlat.Diagonal.InitialMetadataCost

namespace OAI
/-! # Exact initial node and half-port metadata for the emitted seed graph -/
namespace ThreeFlat.Diagonal.NavigationPass.Archive
open Computability.VPVNP.BurstRAM PrivateRAM RAM RAM.HeaderScan Computability.VPVNP.Compression CompressorPacking Native Native.ShrinkStage.Halves
open scoped Classical Fin.NatCast
noncomputable section
variable {W t : ℕ} {B : Type} (A : Archive)
set_option quotPrecheck false
local notation "d" => A.initialDegree
local notation "C" => (⟨A.cursor.graph,A.axes*d,A.cursor.width⟩ : SlotImage.Columns)
local notation "f" => A.seedWords
local notation "cur" => (A.control:Word W)
variable (G : LiftedSlots B A.initialDegree (BitWord t)) (base : B≃Fin A.axes)
    (width : SlotImage.Edge B (BitWord t) A.initialDegree → ℕ)

structure InitialNodeMetadata (out : Memory W) : Prop where
  kernel : ∀ (r : Fin A.initialSites) (j : Fin 5),out (f 7+(r.val*5+j.val))=
    ((![A.seed,r.val,0,r.val%A.remainingLanes,r.val/A.remainingLanes] : Fin 5→ℕ) j : Word W)
  halfHeader : ∀ (r : Fin A.initialSites) (j : Fin 2),out (f 9+(r.val*2+j.val))=
    ((![2*d,f 11+8*d*r.val] : Fin 2→ℕ) j : Word W)
  half : ∀ (u : B×BitWord t) (j : Fin (2*d)) (col : Fin 4),
    let e:=sourceHalf G u j
    out (f 11+((siteNumber base u*(2*d)+j.val)*4+col.val))=
      ((![edgeNumber base e,if j.val<d then 0 else 1,width e,prefixValue G width u j] : Fin 4→ℕ) col : Word W)

private theorem stride_lt {n m i j : ℕ} (low : i<n) (col : j< m) : i*m+j<n*m :=
  (Nat.add_lt_add_left col (i*m)).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right m low)

/-- Preserve all five kernel fields, the half-table headers and their four-word records
when later navigation writes stay outside the initial metadata interval. -/
theorem InitialNodeMetadata.transfer {m out : Memory W} (h : A.InitialNodeMetadata G base width m)
    (lanes : A.remainingLanes=2^t)
    (frame : ∀ i,A.initialRecords≤ i ∧ i<A.metadataEnd→ out i=m i) :
    A.InitialNodeMetadata G base width out := by
  have finish : A.metadataEnd=A.initialRecords+7*A.initialSites+8*d*A.initialSites := by
    unfold metadataEnd;ring
  constructor
  · intro r j
    have off:=stride_lt r.isLt j.isLt
    rw [frame _ ?_]
    · exact h.kernel r j
    · change A.initialRecords≤A.initialRecords+_ ∧ A.initialRecords+_<A.metadataEnd
      rw [finish];omega
  · intro r j
    have off:=stride_lt r.isLt j.isLt
    rw [frame _ ?_]
    · exact h.halfHeader r j
    · change A.initialRecords≤A.initialRecords+5*A.initialSites+_ ∧ A.initialRecords+5*A.initialSites+_<A.metadataEnd
      rw [finish];omega
  · intro v j col
    have row : siteNumber base v<A.initialSites := by
      unfold siteNumber initialSites
      rw [lanes]
      exact stride_lt (base v.1).isLt (tagOrdinal t v.2).isLt
    have off:=stride_lt (stride_lt row j.isLt) col.isLt
    have count : A.initialSites*(2*d)*4=8*d*A.initialSites := by ring
    rw [count] at off
    rw [frame _ ?_]
    · exact h.half v j col
    · change A.initialRecords≤A.initialRecords+7*A.initialSites+_ ∧ A.initialRecords+7*A.initialSites+_<A.metadataEnd
      rw [finish];omega

theorem metadata_actual (m : Memory W) (sp : A.MetadataSpace W) (H : Scans.Header cur m A.seed 63 f)
    (stored : SlotImage.Stored G base (tagOrdinal t) C (fun i=>(m i).val) width)
    (lanes : A.remainingLanes=2^t)
    (gLow : A.cursor.graph+6*(A.axes*d)≤A.initialRecords)
    (wLow : A.cursor.width+(A.axes*d)*2^t≤A.initialRecords)
    (degRoom : 2*d<2^W) (laneRoom : 2^t<2^W) (wide : 8<2^W) :
    let out:=A.metadataMemory m
    A.InitialNodeMetadata G base width out ∧ SlotImage.Stored G base (tagOrdinal t) C (fun i=>(out i).val) width := by
  have rows:=A.raw_metadata_rows m sp H
  have old:=A.metadata_frame m sp H
  have limit:=sp.endFit
  have begin : A.initialRecords≤A.metadataEnd := Nat.le_add_right ..
  have save (z : Memory W) (keep : A.KeepsMetadata z m) : SlotImage.Stored G base (tagOrdinal t) C (fun i=>(z i).val) width :=
    stored.frame (fun i _ hi=>congrArg Fin.val (keep i (.inl (hi.trans_le gLow))))
      (fun i _ hi=>congrArg Fin.val (keep i (.inl (hi.trans_le wLow))))
  refine ⟨⟨?_,?_,?_⟩,save _ old⟩
  · intro r j
    have rb:=stride_lt r.isLt j.isLt
    apply rows.1 _ (Nat.le_add_right ..) (by change A.initialRecords+_<A.initialRecords+5*A.initialSites;omega)
    intro alt agree
    exact A.initialKernel_word alt (MetadataSpace.stable A sp agree H) sp.controlRoom sp.endFit wide r j
  · intro r j
    have rb:=stride_lt r.isLt j.isLt
    apply rows.2.1 _ (Nat.le_add_right ..) (by change A.initialRecords+5*A.initialSites+_<A.initialRecords+7*A.initialSites;omega)
    intro alt agree
    exact A.initialHalfHeader_word alt (MetadataSpace.stable A sp agree H) sp.controlRoom sp.endFit wide r j
  · intro u j col
    have site : siteNumber base u<A.initialSites := by
      unfold siteNumber initialSites;rw [lanes];exact stride_lt (base u.1).isLt (tagOrdinal t u.2).isLt
    have offset:=stride_lt (stride_lt site j.isLt) col.isLt
    have count : A.initialSites*(2*d)*4=8*d*A.initialSites := by ring
    rw [count] at offset
    have finish : f 11+f 12=A.metadataEnd := by
      change A.initialRecords+7*A.initialSites+8*A.initialDegree*A.initialSites =
        A.initialRecords+(7+8*A.initialDegree)*A.initialSites
      rw [Nat.add_mul,Nat.add_assoc]
    apply rows.2.2 _ (Nat.le_add_right ..) (by rw [←finish];exact Nat.add_lt_add_left offset _)
    intro alt agree
    exact A.initialHalf_word alt (MetadataSpace.stable A sp agree H) G base width (save _ agree) lanes
      sp.controlRoom degRoom laneRoom (gLow.trans (begin.trans limit.le)) (wLow.trans (begin.trans limit.le))
      (by rw [finish];exact limit.le) u j col

theorem initialMetadata_spec (m : Memory W) (sp : A.MetadataSpace W) (H : Scans.Header cur m A.seed 63 f)
    (stored : SlotImage.Stored G base (tagOrdinal t) C (fun i=>(m i).val) width)
    (lanes : A.remainingLanes=2^t)
    (gLow : A.cursor.graph+6*(A.axes*d)≤A.initialRecords)
    (wLow : A.cursor.width+(A.axes*d)*2^t≤A.initialRecords)
    (degRoom : 2*d<2^W) (laneRoom : 2^t<2^W) (wide : 8<2^W) :
    (A.initialMetadata : RAM.PhysicalProcedure.Procedure W).Spec (fun mem=>mem=m)
      (fun _ out=>A.InitialNodeMetadata G base width out ∧
        SlotImage.Stored G base (tagOrdinal t) C (fun i=>(out i).val) width ∧
        ∀i,A.metadataKeep i→ out i=m i) (33+metadataCoefficient d*A.initialSites) := by
  have actual:=A.metadata_actual G base width m sp H stored lanes gLow wLow degRoom laneRoom wide
  intro P R K M pc reg pub exit installed data cfg input start same
  obtain ⟨ticks,cost,last,out,run,finish,rfl,keep⟩ :=
    A.metadata_spec m sp H M pc reg pub exit installed data cfg input start same
  rw [A.metadataUnit_eq] at cost
  exact ⟨ticks,cost,last,A.metadataMemory m,run,finish,actual.1,actual.2,keep⟩


end
end ThreeFlat.Diagonal.NavigationPass.Archive

end OAI
