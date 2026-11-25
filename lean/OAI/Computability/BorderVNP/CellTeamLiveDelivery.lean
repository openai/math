import OAI.Computability.BorderVNP.CellTeamBitDelivery
import OAI.Computability.BorderVNP.CubeGroupDirectoryWords
import OAI.Computability.BorderVNP.PackedCableColumns
import OAI.Computability.BorderVNP.PackedBundleGroups

/-! # Physical split live-field and private-source charges on installed delivery words -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Directory

open VPVNP.BurstRAM Cube.TeamRowClock RoutingISA Cube.LabelIndex

/-- The native compact directory writer gives the real row count and the two
columns used by the subsequent label and group-weight reads. -/
def RowLocations.ofPublish {w : ℕ} (rows : List Row) (dir : Cube.LabelIndex.Layout) (g : Cube.GroupWeights.Layout)
    (cells : g.cells=dir.cells) (m : Memory w) (head : ℕ) (count : dir.deliveryCount=rows.length)
    (clear : head+9 < dir.deliveries) (fits : ∀ i : Fin rows.length, ∀ a ∈ rows[i.val].words, a < 2^w)
    (ep : Cube.LabelIndex.Endpoints dir (readings (ISA.publish m head dir.deliveries rows))) :
    let mem := readings (ISA.publish m head dir.deliveries rows)
    RowLocations rows (fun c : Fin g.cells => c.val) (Cube.GroupWeights.directoryRecv cells ep)
      (fun j => (deliveryAt dir mem j.val).2) := by
  intro mem
  exact ⟨(finCongr count.symm).toEmbedding,
    fun i => congrArg Prod.fst (CableTriples.deliveryAt_publish m head dir rows clear i (fits i)),
    fun i => congrArg Prod.snd (CableTriples.deliveryAt_publish m head dir rows clear i (fits i))⟩

/-- One original live literal or substituted pin bit, in true processor order. -/
abbrev Layout.LiveSource (d : Layout) := Fin d.teams × Fin d.processors × Fin d.fields × Fin d.literal

/-- Receiver of an original live source bit after the input has been split into
its initial site blocks and those blocks have acquired final host positions. -/
def Layout.liveReceiver (d : Layout) (lp : ℕ → ℕ × ℕ) (x : d.LiveSource) :=
  let pos := x.2.1.val*d.stride+x.2.2.1.val*(d.literal+(d.teams-1)*d.link)+x.2.2.2.val
  (lp (x.1.val*d.sites+pos/d.block)).1

private theorem live_source (d : Layout) (pp lp : ℕ → ℕ × ℕ) (block : 0<d.block) (x : d.LiveSource) :
    ∃ y : d.RowBit pp lp, let r := (d.directory pp lp).get y.1
      r.cell = d.liveReceiver lp x ∧ (r.team,r.processor,r.field,r.offset+y.2.val) =
        (x.1.val,x.2.1.val,x.2.2.1.val,x.2.2.2.val) := by
  obtain ⟨row,hr,j,hj,team,proc,field,offset,cell,_⟩ := d.live_delivered pp lp x.1 x.2.1 x.2.2.1 block x.2.2.2
  obtain ⟨i,hi,eq⟩ := List.getElem_of_mem hr
  subst row
  exact ⟨⟨⟨i,hi⟩,⟨j,hj⟩⟩,cell,by simp only [List.get_eq_getElem,team,proc,field,offset]⟩

/-- Port bits assigned to distinct original live input positions inject into
the native seven-word directory's row offsets, including partially filled
boundary pieces. The original `team/processor/field/offset` tuple is recovered
from the actual row, so the same charge cannot be used twice. -/
noncomputable def Layout.liveBitDelivery {P A C : Type*} (d : Layout) (pp lp : ℕ → ℕ × ℕ) (block : 0<d.block)
    (bits : P → ℕ) (cell : P → C) (key : FieldBit bits ↪ d.LiveSource) (encode : C ↪ ℕ) (recv : A → C) (width : A → ℕ)
    (rows : RowLocations (d.directory pp lp) encode recv width)
    (routed : ∀ x, d.liveReceiver lp (key x) = encode (cell x.1)) :
    BitDelivery cell bits recv width := by
  let get (x : FieldBit bits) := (live_source d pp lp block (key x)).choose
  let row (x : FieldBit bits) := (d.directory pp lp).get (get x).1
  let send (x : FieldBit bits) : FieldBit width :=
    ⟨rows.ordinal (get x).1,Fin.cast (rows.span (get x).1).symm (get x).2⟩
  let coords (x : d.LiveSource) := (x.1.val,x.2.1.val,x.2.2.1.val,x.2.2.2.val)
  have source (x : FieldBit bits) :
      (row x).cell=d.liveReceiver lp (key x) ∧
      ((row x).team,(row x).processor,(row x).field,(row x).offset+(get x).2.val) = coords (key x) :=
    (live_source d pp lp block (key x)).choose_spec
  refine ⟨⟨send,?_⟩,fun x => encode.injective ((rows.cell _).trans ((source x).1.trans (routed x)))⟩
  intro x y eq
  have index : (get x).1=(get y).1 := rows.ordinal.injective (congrArg Sigma.fst eq)
  have pos : (get x).2.val=(get y).2.val := congrArg (fun z : FieldBit width => z.2.val) eq
  have hx := (source x).2
  rw [show row x=row y from congrArg (d.directory pp lp).get index,pos,(source y).2] at hx
  exact key.injective (Prod.ext (Fin.ext (congrArg Prod.fst hx).symm)
    (Prod.ext (Fin.ext (congrArg (fun z => z.2.1) hx).symm)
      (Prod.ext (Fin.ext (congrArg (fun z => z.2.2.1) hx).symm) (Fin.ext (congrArg (fun z => z.2.2.2) hx).symm))))

/-- Real retained-bundle ordinals in stable final cell order charge their
original source-site rows, even if two adjacent processor literals share them. -/
noncomputable def Layout.bundleBitDelivery {C N : ℕ} {A Bundle : Type} (d : Layout) (pp lp : ℕ → ℕ × ℕ)
    (cell : Fin N → Fin C) (bundle : Fin N → Bundle) (bs : Fin C → List Bundle)
    (grouped : ∀ c, bs c = (BundleDirectory.sourceRows cell c.val).map bundle)
    (entry : Fin N ↪ Fin d.entries) (placed : ∀ i, (pp (entry i)).1=(cell i).val)
    (recv : A → Fin C) (width : A → ℕ) (rows : RowLocations (d.directory pp lp) Fin.val recv width)
    (tail : 0<d.literal/2) (short : d.description≤d.literal/2) :
    BitDelivery (fun j : (c : Fin C) × Fin (bs c).length => j.1) (fun _ => d.description) recv width := by
  let changeRow (c : Fin C) : Fin (bs c).length ≃ Fin (BundleDirectory.sourceRows cell c.val).length :=
    finCongr ((congrArg List.length (grouped c)).trans (List.length_map ..))
  let ungroup := (Equiv.sigmaCongrRight changeRow).trans (BundleDirectory.sourceEquiv cell)
  apply d.privateBitDelivery pp lp _ (ungroup.toEmbedding.trans entry) ⟨Fin.val,Fin.val_injective⟩ recv width rows _ tail short
  intro j
  change (pp (entry (ungroup j))).1=j.1.val
  rw [placed]
  exact BundleDirectory.mem_sourceRows.mp (List.get_mem (BundleDirectory.sourceRows cell j.1.val) (changeRow j.1 j.2))

end Packing.Directory

end BorderVNP
end Computability
end OAI
