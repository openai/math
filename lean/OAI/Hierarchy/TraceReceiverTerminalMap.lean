import OAI.Hierarchy.TraceReceiverMapSave
import OAI.Hierarchy.TraceReceiverWordSources
import OAI.ThreeFlat.RAM.TickTerminalRecords
import OAI.ThreeFlat.RAM.TerminalWireArchive
import OAI.ThreeFlat.Diagonal.PhysicalStateHalfRows

namespace OAI
/-! # Writing a terminal factor's external and shared pin addresses

The endpoint table is the selected cache's ordered list of external pin
addresses. Every physical half supplies one interval from the shared suffix.
The two copies of a wire read the same prefix even for a loop. -/

noncomputable section
namespace Hierarchy.TraceReceiverTerminalMap

open ThreeFlat Diagonal Diagonal.PhysicalStage Diagonal.HistoryContraction
open RAM RAM.HistoryTerminalTape RAM.TickTerminalRoot Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM
open scoped BigOperators Classical Fin.CommRing

variable {d l W p : ℕ} {Pins : Type} (A : State d l) (L : A.Words Pins) (v : A.Site)

/-- The index of the first bit of an outgoing wire, in the shared string. -/
def wireStart (e : A.shape.Edge) : ℕ :=
  ∑ j : Fin (A.wireOrder e).val, A.wireWidth (Fin.castLE (A.wireOrder e).isLt.le j)

theorem edgeBit_val (e : A.shape.Edge) (j : Fin (A.width e)) :
    (A.edgeBit e j).val=wireStart A e+j.val := A.bitAddress_val _ _

def halfStart (i : Fin (L.count v)) : ℕ :=
  ∑ j : Fin i.val, L.ports.lengths v (Fin.castLE i.isLt.le j)

/-- Four-word half records and the globally numbered outgoing-edge prefix
are interpreted in the same physical order as the assembled network. -/
structure HalfRows (T : Root) (raw : ℕ → ℕ) (suffix : ℕ) : Prop where
  ext_eq : T.ext=L.ext v
  halves_eq : T.halves=L.count v
  wire_start : T.wireStart=2+suffix
  edge : ∀ i : Fin (L.count v), (half T raw i.val).edge=(A.wireOrder (L.order v i).1.1).val
  width : ∀ i : Fin (L.count v), (half T raw i.val).width=L.ports.lengths v i
  start : ∀ i : Fin (L.count v), (half T raw i.val).start=halfStart A L v i
  wire : ∀ i : Fin (L.count v),
    raw (T.wirePrefix+(A.wireOrder (L.order v i).1.1).val)=wireStart A (L.order v i).1.1

/-- Decode the selected archive's actual incident table. Its numeric edge
order is the outgoing-slot order used to store the globally shared wire. -/
theorem of_emitted (T : Root) (raw : ℕ → ℕ) (suffix : ℕ)
    (O : A.ArchiveSites) {safe : ℕ → Prop} (posted : A.HalfRows O safe raw) (order : A.OrderedHalves L)
    (external : T.ext=L.ext v) (origin : T.wireStart=2+suffix)
    (count : T.halves=raw (O.layer.incident+(O.ord v).val*2))
    (pointer : T.halfData=raw (O.layer.incident+(O.ord v).val*2+1))
    (prefixes : ∀ e : A.shape.Edge, raw (T.wirePrefix+(A.wireOrder e).val)=wireStart A e) :
    HalfRows A L v T raw suffix := by
  have number (e : A.shape.Edge) : (A.wireOrder e).val=
      CompressorPacking.Native.ShrinkStage.Halves.edgeNumber A.order e := by
    obtain ⟨⟨b,z⟩,lane⟩ := e
    exact A.wireOrder_val b z lane
  refine ⟨external,count.trans ((posted.count v).trans (order.count v).symm),origin,?_,?_,?_,fun i=>prefixes _⟩
  · intro i
    rw [number,order.edge v i]
    simpa only [half,pointer,Fin.val_cast] using posted.edge v (i.cast (order.count v))
  · intro i
    change (half T raw i.val).width=A.width (L.order v i).1.1
    rw [order.edge v i]
    simpa only [half,pointer,Fin.val_cast] using posted.width v (i.cast (order.count v))
  · intro i
    exact (show (half T raw i.val).start=_ from by
      simpa only [half,pointer,Fin.val_cast] using posted.start v (i.cast (order.count v))).trans (order.start v i)

/-- The bounded native prefix scan on the selected final width array
supplies every shared-wire offset consumed in the terminal map. -/
theorem prefix_image (x : TerminalWireArchive.Layout) (m : Memory W) (bounds : TerminalWireArchive.Bounds x W)
    (count : x.edges=A.edgeCount) (loaded : ∀ i : Fin A.edgeCount,
      (m (x.widthBase+i.val)).val=A.wireWidth i) (fits : A.widthSum ≤ x.capacity) (e : A.shape.Edge) :
    (TerminalWireArchive.image x m (x.prefixBase+(A.wireOrder e).val)).val=wireStart A e := by
  exact TerminalWireArchive.image_exact x m bounds A.wireWidth count loaded
    (A.wireWidth_sum.le.trans fits) _ (A.wireOrder e).isLt.le

def shared (suffix : ℕ) (room : suffix+A.widthSum ≤ p) (e : A.shape.Edge) (j : Fin (A.width e)) :
    Fin p := ⟨suffix+(A.edgeBit e j).val, by have := (A.edgeBit e j).isLt; omega⟩

variable (ext : ∀ v, Fin (L.ext v) → Fin p) (suffix : ℕ) (room : suffix+A.widthSum ≤ p)

/-- The native half table covers precisely the shared part of the selected
factor, and the external records cover its first contiguous block. -/
theorem incidences (T : Root) (raw : ℕ → ℕ) (m : Memory W) (rows : HalfRows A L v T raw suffix)
    (ends : ∀ j : Fin (L.ext v), m (T.endpoints+j.val)=((2+(ext v j).val : ℕ):Word W)) :
    Incidences T raw m (L.ports.physicalSource ext (shared A suffix room) v) := by
  refine ⟨?_,?_,?_⟩
  · intro k hk
    let j : Fin (L.ext v) := ⟨k.val,rows.ext_eq ▸ hk⟩
    have e : k=Fin.castAdd (L.ports.halfBits v) j := Fin.ext rfl
    have here : L.ports.physicalSource ext (shared A suffix room) v (Fin.castAdd (L.ports.halfBits v) j)=ext v j :=
      Fin.append_left (ext v) _ j
    rw [e]
    exact (ends j).trans (congrArg (fun q : Fin p => ((2+q.val : ℕ) : Word W)) here.symm)
  · intro k hk
    have lo : L.ext v ≤ k.val:=rows.ext_eq ▸ hk
    have upper : k.val < L.ext v+L.ports.halfBits v := k.isLt
    let z : Fin (L.ports.halfBits v) := ⟨k.val-L.ext v,by omega⟩
    obtain ⟨⟨i,j⟩,eqn⟩ := finSigmaFinEquiv.surjective z
    have idx := finSigmaFinEquiv_apply (n:=L.ports.lengths v) ⟨i,j⟩
    rw [eqn] at idx
    refine ⟨i.val,rows.halves_eq.symm ▸ i.isLt,j.val,(rows.width i).symm ▸ j.isLt,?_⟩
    have start : (half T raw i.val).start=halfStart A L v i:=rows.start i
    have ext_eq : T.ext=L.ext v:=rows.ext_eq
    change k.val-L.ext v=halfStart A L v i+j.val at idx
    omega
  · intro b hb j hj k eqn
    let i : Fin (L.count v) := ⟨b,rows.halves_eq ▸ hb⟩
    let a : Fin (L.ports.lengths v i) := ⟨j,(rows.width i) ▸ hj⟩
    let z := finSigmaFinEquiv (n:=L.ports.lengths v) ⟨i,a⟩
    have idx : z.val=halfStart A L v i+j := finSigmaFinEquiv_apply _
    have x : k=Fin.natAdd (L.ext v) z := by
      apply Fin.ext
      change k.val=L.ext v+z.val
      calc
        k.val = T.ext+(half T raw i.val).start+j := eqn
        _ = L.ext v+(halfStart A L v i+j) := by rw [rows.ext_eq,rows.start i,Nat.add_assoc]
        _ = L.ext v+z.val := by rw [idx]
    let pick (q : (i : Fin (L.count v)) × Fin (L.ports.lengths v i)) : Fin p :=
      shared A suffix room (L.order v q.1).1.1 q.2
    have here : L.ports.physicalSource ext (shared A suffix room) v (Fin.natAdd (L.ext v) z)=pick ⟨i,a⟩ := by
      change Fin.append (ext v) (fun t=>pick (finSigmaFinEquiv.symm t)) (Fin.natAdd (L.ext v) z)=_
      exact (Fin.append_right _ _ z).trans (congrArg pick (finSigmaFinEquiv.symm_apply_apply ⟨i,a⟩))
    rw [x]
    refine Eq.trans ?_ (congrArg (fun q : Fin p => 2+q.val) here.symm)
    change HistoryTerminalTape.source T raw i.val+j=2+(suffix+(A.edgeBit (L.order v i).1.1 a).val)
    rw [HistoryTerminalTape.source,rows.wire_start,rows.edge,rows.wire]
    have coordinate : (A.edgeBit (L.order v i).1.1 a).val=wireStart A (L.order v i).1.1+j :=
      edgeBit_val A (L.order v i).1.1 a
    exact (show 2+suffix+wireStart A (L.order v i).1.1+j=
        2+(suffix+(wireStart A (L.order v i).1.1+j)) by omega).trans
      (congrArg (fun n : ℕ => 2+(suffix+n)) coordinate.symm)

/-- Numeric contents after the physical terminal copy/fill jobs, at exactly
the addresses consumed by the gathered network's pin-map loads. -/
theorem pin_after (T : Root) (raw : ℕ → ℕ) (m : Memory W) (ctrl : Word W)
    (rows : HalfRows A L v T raw suffix)
    (ends : ∀ j : Fin (L.ext v), m (T.endpoints+j.val)=((2+(ext v j).val : ℕ):Word W))
    (k : Fin (L.ports.form.width v)) (apart : T.map+k.val≠ctrl.val) :
    pinMemory T raw ctrl m (T.map+k.val)=
      ((2+(L.ports.physicalSource ext (shared A suffix room) v k).val : ℕ):Word W) :=
  TickTerminalRoot.pin_after T raw ctrl m _ (incidences A L v ext suffix room T raw m rows ends) k apart

/-- The persistent selected-root map contains the addresses of the physical
pins. Every endpoint comes from the original selected cache and each shared
bit comes from the actual final half record and its exclusive wire prefix. -/
theorem saved_pin (arena : Arena) (m : Memory W) (dst : ℕ) (bounds : RootBounds arena m)
    (rows : HalfRows A L v (terminal arena (natMemory m)) (natMemory m) suffix)
    (ends : ∀ j : Fin (L.ext v), m ((terminal arena (natMemory m)).endpoints+j.val)
      =((2+(ext v j).val : ℕ):Word W))
    (endBefore : let T:=terminal arena (natMemory m); T.endpoints+T.ext ≤ arena.seed)
    (k : Fin (L.ports.form.width v))
    (ctrl : arena.map+k.val ≠ ((arena.seed+5:ℕ):Word W).val)
    (metaFree : let T:=terminal arena (natMemory m); arena.map+k.val < T.meta ∨ T.meta+4*T.rows ≤ arena.map+k.val)
    (saveFree : arena.map+k.val < arena.control ∨ arena.control+4 ≤ arena.map+k.val) :
    fillSegment dst (L.ports.form.width v) (fun a=>output arena m (arena.map+(a-dst)))
      (output arena m) (dst+k.val)
      = ((2+(L.ports.physicalSource ext (shared A suffix room) v k).val:ℕ):Word W) :=
  TraceReceiverMapSave.saved_pin arena m dst _ k
    (TraceReceiverMapSave.ready_incidences arena m bounds _
      (incidences A L v ext suffix room _ _ m rows ends) endBefore) ctrl metaFree saveFree


end Hierarchy.TraceReceiverTerminalMap

end
end OAI
