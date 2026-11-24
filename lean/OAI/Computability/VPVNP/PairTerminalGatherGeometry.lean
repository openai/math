import OAI.Computability.VPVNP.PairTerminalPrefix
import OAI.Computability.VPVNP.PairNodeArguments
import OAI.Computability.VPVNP.PairSimulationTerminalRootGatherLayout

/-!
# Terminal site arguments from the shared final-arc array

The physical source of each outgoing field is its own port. Incoming fields
follow the actual inverse slot permutation. Both copies of a loop therefore
use the same shared payload, at their separate positions in the root argument.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.TerminalGatherGeometry

open BurstRAM BurstRAM.PrivateRAM Compression CompressorRecords LocalHistory
open scoped Fin.CommRing
open private actualWidth payloadBits from OAI.Computability.VPVNP.PairSimulationScanTrace

variable {a g w : ℕ} (X : State a g)

/-- Ordinal of an outgoing arc in the final shared scan. -/
abbrev number := (edgeOrder X).entries.symm

/-- The same equivalence used by the final scan phase of the history. -/
noncomputable def payload := FinalBits.payloads (TerminalPrefix.width X) X.network (number X) (payloadBits X)

/-- The local half-wire assignment at a final site induced by splitting the shared bit string
into the terminal arc payloads. -/
noncomputable def half (f : Fin (∑ i, TerminalPrefix.width X i) → Bool) (v : X.network.Site) :=
  WireTensor.edgeAssignment X.network.src X.network.dst (payload X f) v

/-- The successful native scan of these bits decodes to this very payload
in the chronological history trace. -/
theorem phase_payload {p r k : ℕ} (M : Machine w p r k) (pc : Fin 10 → Fin p)
    (reg : Fin 2 ↪ Fin r) (base : Fin k) (done : Fin p)
    (hl : FinalBits.Linked M pc reg base done) (he : M.entry = pc 0)
    (low : ℕ) (pub : M.publicData base = FinalBits.cursor w low 0) (m : Memory w) (extra : ℕ)
    (fit : low + X.totalWidth < 2 ^ w) (f : Fin (∑ i, TerminalPrefix.width X i) → Bool) :
    (stateScanPhase X M pc reg base done hl he low pub m extra fit).payload
      (FinalBits.scanEquiv hl he low (∑ i, TerminalPrefix.width X i)
        (by rwa [TerminalPrefix.width_sum]) pub m extra f) = payload X f := by
  change payload X ((FinalBits.scanEquiv hl he low _ _ pub m extra).symm
    (FinalBits.scanEquiv hl he low _ _ pub m extra f)) = _
  rw [Equiv.symm_apply_apply]

/-- Source arc underlying an endpoint slot. -/
def arc (v : X.network.Site) (dir : Bool) (j : Fin (2 ^ a)) : X.network.Edge :=
  if dir then X.slots.actualGraph.target.symm (v, j) else (v, j)

theorem scan_width (e : X.network.Edge) :
    TerminalPrefix.width X (number X e) = actualWidth X e :=
  congrArg (actualWidth X) ((edgeOrder X).entries.apply_symm_apply e)

theorem slot_width (v : X.network.Site) (dir : Bool) (j : Fin (2 ^ a)) :
    TerminalPrefix.width X (number X (arc X v dir j)) = X.halfWidth v dir j := by
  rw [scan_width]
  cases dir <;> rfl

private theorem transportedBit {s t : ℕ} (h : s = t) (z : Fin t → Bool) (i : Fin s) :
    ((congrArg (fun n ↦ (Fin t → Bool) ≃ (Fin n → Bool)) h).mpr (Equiv.refl _)) z i =
      z (Fin.cast h i) := by
  cases h
  rfl

private theorem payload_bit (f : Fin (∑ i, TerminalPrefix.width X i) → Bool)
    (e : X.network.Edge) (i : Fin (actualWidth X e)) :
    payload X f e i = f (FinalBits.index (TerminalPrefix.width X) (number X e)
      (Fin.cast (scan_width X e).symm i)) := by
  let j := Fin.cast (scan_width X e).symm i
  have hs := FinalBits.payloads_bit (TerminalPrefix.width X) X.network (number X) (payloadBits X) f e j
  exact (transportedBit (scan_width X e) (payload X f e) j).symm.trans hs

/-- Every bit in a declared node field equals its physical shared-array bit,
including incoming slots matched to a different source ordinal. -/
theorem field_readback (low : ℕ) (fit : low + X.totalWidth < 2 ^ w)
    (f : Fin (∑ i, TerminalPrefix.width X i) → Bool) (initial : Memory w)
    (v : X.network.Site) (dir : Bool) (j : Fin (2 ^ a)) (i : Fin (X.halfWidth v dir j)) :
    let e := number X (arc X v dir j)
    after initial (eventLog (FinalBits.reports w low f))
      (low + EndpointBits.offset (TerminalPrefix.width X) e + i.val) =
      PrivateFields.bitValue w (NodeArguments.fieldBits X v (half X f v) dir j i) := by
  let e := arc X v dir j
  let k := Fin.cast (slot_width X v dir j).symm i
  let idx := FinalBits.index (TerminalPrefix.width X) (number X e) k
  have loc : low + EndpointBits.offset (TerminalPrefix.width X) (number X e) + i.val =
      low + idx.val := by rw [FinalBits.index_val, Nat.add_assoc]; rfl
  dsimp only
  change after initial _ (low + EndpointBits.offset _ (number X e) + i.val) = _
  rw [loc, FinalBits.readback low (by rwa [TerminalPrefix.width_sum])]
  congr 1
  cases dir with
  | false => exact (payload_bit X f (v,j) i).symm
  | true => exact (payload_bit X f (X.slots.actualGraph.target.symm (v,j)) i).symm

open TerminalRootGather

variable (L : Layout)

/-- Physical numbering of the current vertex and the whole terminal graph. -/
structure Numbering (v : X.network.Site) : Prop where
  vertex : L.vertex = ((siteOrder X).entries.symm v).val
  sites : L.sites = (siteOrder X).length
  slots : L.slots = TerminalPrefix.arcCount X

theorem Numbering.degree {v : X.network.Site} (h : Numbering X L v) : L.degree = 2 ^ a := by
  have pos := ((siteOrder X).entries.symm v).isLt
  rw [Layout.degree, h.sites, h.slots]
  change (siteOrder X).length * 2 ^ a / (siteOrder X).length = _
  exact Nat.mul_div_cancel_left _ (by omega)

theorem Numbering.index {v : X.network.Site} (h : Numbering X L v) (j : Fin (2 ^ a)) :
    L.index j.val = (number X (v,j)).val := by
  rw [Layout.index, h.vertex, h.degree]
  change _ = j.val + 2 ^ a * ((siteOrder X).entries.symm v).val
  ring

/-- The gather accesses only these three directory columns. -/
structure Rows (mem : Memory w) : Prop where
  inverse : ∀ e : X.network.Edge, (mem (L.incomingHead + (number X e).val)).val =
    (number X (X.slots.actualGraph.target.symm e)).val
  widths : ∀ i : Fin (TerminalPrefix.arcCount X),
    (mem (L.widthHead + i.val)).val = TerminalPrefix.width X i
  starts : ∀ i : Fin (TerminalPrefix.arcCount X),
    (mem (L.prefixHead + i.val)).val = EndpointBits.offset (TerminalPrefix.width X) i

/-- The physical heads and the separation of the inverse column from the
two destinations of the prefix worker. -/
structure PrefixLayout (T : IncidenceDirectory w) (base total : Word w) : Prop where
  incoming : L.incomingHead = T.actualIn.val
  widths : L.widthHead = T.width.val
  starts : L.prefixHead = base.val
  inverseFit : L.incomingHead + TerminalPrefix.arcCount X ≤ 2 ^ w
  totalApart : total.val < L.incomingHead ∨ L.incomingHead + TerminalPrefix.arcCount X ≤ total.val
  startsApart : L.incomingHead + TerminalPrefix.arcCount X ≤ base.val ∨
    base.val + TerminalPrefix.arcCount X ≤ L.incomingHead

theorem rows_of_prefix {T : IncidenceDirectory w} {base total : Word w} {initial final : Memory w}
    (hl : PrefixLayout X L T base total) (hc : T.ActualColumns X initial)
    (hs : TerminalPrefix.Stored X T base total initial final) : Rows X L final := by
  refine ⟨fun e ↦ ?_, fun i ↦ hl.widths ▸ hs.widths i, fun i ↦ hl.starts ▸ hs.start i⟩
  have hi := (number X e).isLt
  change (number X e).val < TerminalPrefix.arcCount X at hi
  have hFit := hl.inverseFit
  have hTotal := hl.totalApart
  have hStarts := hl.startsApart
  rw [hs.outside _ (by omega) (by omega)]
  have hcol := congrArg Fin.val (hc.actualIn e)
  have ht := (number X (X.slots.actualGraph.target.symm e)).isLt
  change (number X (X.slots.actualGraph.target.symm e)).val < TerminalPrefix.arcCount X at ht
  rw [TerminalPrefix.actualPort_eq X e, TerminalPrefix.actualPort_eq X (X.slots.actualGraph.target.symm e)] at hcol
  simp only [Fin.val_add, Fin.val_natCast] at hcol
  rw [← hl.incoming, Nat.mod_eq_of_lt (by omega : (number X e).val < 2 ^ w),
    Nat.mod_eq_of_lt (by omega : L.incomingHead + (number X e).val < 2 ^ w),
    Nat.mod_eq_of_lt (by omega : (number X (X.slots.actualGraph.target.symm e)).val < 2 ^ w)] at hcol
  exact hcol

/-- Arbitrary intervening work can transfer these facts by preserving the
three arrays at their live ordinals. -/
theorem Rows.transfer {before after : Memory w} (h : Rows X L before)
    (keep : ∀ head ∈ [L.incomingHead,L.widthHead,L.prefixHead],
      ∀ i : Fin (TerminalPrefix.arcCount X), after (head + i.val) = before (head + i.val)) :
    Rows X L after := by
  refine ⟨fun e ↦ ?_, fun i ↦ ?_, fun i ↦ ?_⟩
  · rw [keep _ (by simp), h.inverse]
  · rw [keep _ (by simp), h.widths]
  · rw [keep _ (by simp), h.starts]

theorem Rows.after_reports {before : Memory w} (h : Rows X L before)
    (f : Fin (∑ i, TerminalPrefix.width X i) → Bool) (fit : L.wires + X.totalWidth < 2 ^ w)
    (apart : ∀ head ∈ [L.incomingHead,L.widthHead,L.prefixHead],
      head + TerminalPrefix.arcCount X ≤ L.wires ∨ L.wires + X.totalWidth ≤ head) :
    Rows X L (after before (eventLog (FinalBits.reports w L.wires f))) := by
  apply h.transfer
  intro head hh i
  apply FinalBits.outside _ (by rwa [TerminalPrefix.width_sum])
  have hsep := apart head hh
  have hi := i.isLt
  rw [TerminalPrefix.width_sum]
  omega

variable {X L} {v : X.network.Site} {mem : Memory w}

theorem edge_eq (num : Numbering X L v) (rows : Rows X L mem) (dir : Bool) (j : Fin (2 ^ a)) :
    L.edge mem dir j.val = (number X (arc X v dir j)).val := by
  rw [Layout.edge, num.index]
  cases dir with
  | false => rfl
  | true => exact rows.inverse _

theorem width_eq (num : Numbering X L v) (rows : Rows X L mem) (dir : Bool) (j : Fin (2 ^ a)) :
    L.width mem dir j.val = X.halfWidth v dir j := by
  rw [Layout.width, edge_eq num rows, rows.widths, slot_width]

theorem start_eq (num : Numbering X L v) (rows : Rows X L mem) (dir : Bool) (j : Fin (2 ^ a)) :
    L.start mem dir j.val = L.wires +
      EndpointBits.offset (TerminalPrefix.width X) (number X (arc X v dir j)) := by
  rw [Layout.start, edge_eq num rows, rows.starts]

/-- All words that the native gather reads, in the root's descriptor order. -/
theorem packet_eq (num : Numbering X L v) (rows : Rows X L mem)
    (f : Fin (∑ i, TerminalPrefix.width X i) → Bool)
    (bits : ∀ i, mem (L.wires+i.val) = PrivateFields.bitValue w (f i)) :
    L.packet mem = (NodeArguments.packed X v (half X f v)).map (PrivateFields.bitValue w) := by
  have one (dir : Bool) (j : Fin (2 ^ a)) : L.field mem dir j.val =
      List.ofFn (fun i ↦ PrivateFields.bitValue w (NodeArguments.fieldBits X v (half X f v) dir j i)) := by
    apply List.ext_getElem (by rw [Layout.field_length, width_eq num rows, List.length_ofFn])
    intro k hk hk'
    have hwidth : k < X.halfWidth v dir j := by simpa only [List.length_ofFn] using hk'
    simp only [Layout.field, List.getElem_ofFn, start_eq num rows]
    let j' := Fin.cast (slot_width X v dir j).symm ⟨k,hwidth⟩
    let idx := FinalBits.index (TerminalPrefix.width X) (number X (arc X v dir j)) j'
    have hi : L.wires + EndpointBits.offset (TerminalPrefix.width X) (number X (arc X v dir j)) + k =
        L.wires + idx.val := by rw [FinalBits.index_val, Nat.add_assoc]; rfl
    rw [hi,bits]
    congr 1
    cases dir with
    | false => exact (payload_bit X f (v,j) ⟨k,hwidth⟩).symm
    | true => exact (payload_bit X f (X.slots.actualGraph.target.symm (v,j)) ⟨k,hwidth⟩).symm
  have side (dir : Bool) : L.fields mem dir =
      (NodeArguments.fields X v (half X f v) dir).map (List.map (PrivateFields.bitValue w)) := by
    simp only [Layout.fields, NodeArguments.fields, List.map_ofFn]
    apply List.ext_getElem (by simp only [List.length_ofFn]; exact num.degree)
    intro j _ hj
    have hj' : j < 2 ^ a := by simpa only [List.length_ofFn] using hj
    simp only [List.getElem_ofFn, Function.comp_apply, List.map_ofFn]
    exact one dir ⟨j,hj'⟩
  simp only [Layout.packet, NodeArguments.packed, List.map_append, List.map_flatten, side]

theorem packet_after_reports (num : Numbering X L v) {initial : Memory w}
    (rows : Rows X L initial) (f : Fin (∑ i, TerminalPrefix.width X i) → Bool)
    (fit : L.wires + X.totalWidth < 2 ^ w)
    (apart : ∀ head ∈ [L.incomingHead,L.widthHead,L.prefixHead],
      head + TerminalPrefix.arcCount X ≤ L.wires ∨ L.wires + X.totalWidth ≤ head) :
    L.packet (after initial (eventLog (FinalBits.reports w L.wires f))) =
      (NodeArguments.packed X v (half X f v)).map (PrivateFields.bitValue w) :=
  packet_eq num (rows.after_reports X L f fit apart) f
    (FinalBits.readback L.wires (by rwa [TerminalPrefix.width_sum]) f initial)

/-- The loop bounds and the exclusive source and destination cursors fit
from whole-array bounds and the size of the typed private argument. -/
theorem fits (num : Numbering X L v) (rows : Rows X L mem)
    (f : Fin (∑ i, TerminalPrefix.width X i) → Bool)
    (bits : ∀ i, mem (L.wires+i.val) = PrivateFields.bitValue w (f i))
    (countFit : TerminalPrefix.arcCount X < 2 ^ w)
    (headFit : ∀ head ∈ [L.incomingHead,L.widthHead,L.prefixHead],
      head + TerminalPrefix.arcCount X ≤ 2 ^ w)
    (sharedFit : L.wires + X.totalWidth < 2 ^ w)
    (privateFit : L.dest + (∑ dir : Bool, ∑ j, X.halfWidth v dir j) < 2 ^ w) :
    L.Fits mem := by
  have count : TerminalPrefix.arcCount X = (siteOrder X).length * 2 ^ a := rfl
  have hpos : 0 < 2 ^ a := pow_pos (by decide) _
  have hsite := ((siteOrder X).entries.symm v).isLt
  have addresses (d : Bool) (j : Fin (2 ^ a)) :
      L.edge mem d j.val < TerminalPrefix.arcCount X := by
    rw [edge_eq num rows]
    exact (number X _).isLt
  refine ⟨?_, num.slots.trans_lt countFit, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [num.sites]
    rw [count] at countFit
    exact (Nat.le_mul_of_pos_right _ hpos).trans_lt countFit
  · rw [Layout.index,num.vertex,num.degree, ← Nat.succ_mul]
    exact (Nat.mul_le_mul_right _ hsite).trans_lt (count ▸ countFit)
  · intro j hj
    rw [num.degree] at hj
    rw [num.index X L ⟨j,hj⟩]
    exact (Nat.add_lt_add_left (number X (v,⟨j,hj⟩)).isLt _).trans_le (headFit _ (by simp))
  · intro d j hj
    rw [num.degree] at hj
    exact (Nat.add_lt_add_left (addresses d ⟨j,hj⟩) _).trans_le (headFit _ (by simp))
  · intro d j hj
    rw [num.degree] at hj
    exact (Nat.add_lt_add_left (addresses d ⟨j,hj⟩) _).trans_le (headFit _ (by simp))
  · intro d j hj
    rw [num.degree] at hj
    let k : Fin (2 ^ a) := ⟨j,hj⟩
    rw [start_eq num rows d k, width_eq num rows d k, ← slot_width, Nat.add_assoc]
    have bound := EndpointBits.arc_fits (TerminalPrefix.width X) (number X (arc X v d k))
    rw [TerminalPrefix.width_sum] at bound
    exact (Nat.add_le_add_left bound _).trans_lt sharedFit
  · rwa [packet_eq num rows f bits, List.length_map, NodeArguments.packed_length]

/-- The gather's actual private writes are the semantic descriptor store,
including preservation of all words outside the root's private interval. -/
theorem placed_packet (num : Numbering X L v) (rows : Rows X L mem)
    (f : Fin (∑ i, TerminalPrefix.width X i) → Bool)
    (bits : ∀ i, mem (L.wires+i.val) = PrivateFields.bitValue w (f i))
    (fit : L.Fits mem) (old : Word w → Word w) :
    Layout.placed L.dest (L.packet mem) old =
      PrivateFields.storeBits L.dest (NodeArguments.packed X v (half X f v)) old := by
  let bs := NodeArguments.packed X v (half X f v)
  have hlen : (L.packet mem).length = bs.length := by rw [packet_eq num rows f bits, List.length_map]
  have room : L.dest + bs.length ≤ 2 ^ w := hlen ▸ fit.destEnd.le
  funext x
  by_cases hx : L.dest ≤ x.val ∧ x.val < L.dest + bs.length
  · let i : Fin bs.length := ⟨x.val-L.dest, by omega⟩
    have hv : L.dest + i.val = x.val := by dsimp [i]; omega
    have hw : Fin.ofNat (2 ^ w) (L.dest+i.val) = x := by rw [hv]; exact Fin.ofNat_val_eq_self x
    rw [← hw, Layout.placed_inside _ old ⟨i.val, i.isLt.trans_eq hlen.symm⟩ fit.destEnd.le]
    refine Eq.trans ?_ (PrivateFields.storeBits_read _ bs old room i).symm
    simp only [packet_eq num rows f bits,List.getElem_map]
    rfl
  · rw [Layout.placed_outside _ _ _ _ (by omega)]
    exact (PrivateFields.storeBits_outside L.dest bs old x room (by omega)).symm

end PairSimulation.TerminalGatherGeometry

end VPVNP
end Computability
end OAI
