import OAI.Computability.BorderVNP.PackedBankInheritedTieCount
import OAI.Computability.BorderVNP.PackedInheritedPieces
import OAI.Computability.BorderVNP.CellDirectoryRetained

/-! # Charges of the actual retained site program

The site adds one flat nine-word equality and its guard for each emitted
interval. The retained program keeps its one-copy table, factor sweeps and
expanded visits. Its work area grows by the width of the previous incoming
words, in their original site-local order.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited

open Crossing Shortening Shortening.CombiningStep CellSparse InheritedBank
open scoped Classical

/-- Static word input, public guard nodes, stored one-copy table and resolved
one-copy sweeps of the actual site-local sparse directory. -/
def Site.staticNodes (s : Site) : ℕ :=
  (Packet.fieldList Packet.record s.rows).length +
    (Packet.fieldList (Packet.fieldList Packet.factor) s.boxes).length +
    Directory.recordNodes s.rows + Directory.tableNodes s.boxes + Directory.blockNodes s.directory.blocks

/-- Private site bits and individual visits of the expanded repeated boxes. -/
def Site.expandedLoad (s : Site) : ℕ := s.work + s.directory.visitCount

/-- The retained block list is literally the old one, with no extra lookups
from the newly appended wiring equalities. -/
theorem Site.retain_blocks (s : Site) (n : ℕ) (cuts : List Slice) :
    (s.retain n cuts).directory.blocks = s.directory.blocks := by
  change Directory.resolvedRows s.boxes (s.retain n cuts).rows = Directory.resolvedRows s.boxes s.rows
  have hempty : Directory.resolvedRows s.boxes (cuts.map (Slice.record s)) = [] := by
    apply Directory.resolvedRows_wires
    intro r hr id base copies stride
    obtain ⟨c,_,rfl⟩ := List.mem_map.mp hr
    simp [Slice.record]
  rw [s.retain_rows,Directory.resolvedRows_append,hempty,List.append_nil]

private theorem tieWords (s : Site) (cuts : List Slice) :
    ((cuts.map (Slice.record s)).flatMap Packet.record).length = 9*cuts.length := by
  induction cuts with
  | nil => rfl
  | cons c cuts ih => simp [Slice.record,Packet.record,Packet.port,ih,Nat.mul_succ]

private theorem tieGuards (s : Site) (cuts : List Slice) :
    ((cuts.map (Slice.record s)).map Record.guardMassBound).sum = 1024*cuts.length := by
  induction cuts with
  | nil => rfl
  | cons c cuts ih =>
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.mul_succ,ih]
    change 1024 + 1024 * cuts.length = 1024 * cuts.length + 1024
    omega

/-- Each actual emitted tie costs nine serialized words and 1,025 guard nodes.
The original row count prefix and private table packet still occur once. -/
theorem Site.staticNodes_retain (s : Site) (n : ℕ) (cuts : List Slice) :
    (s.retain n cuts).staticNodes = s.staticNodes + 1034*cuts.length := by
  simp only [staticNodes,s.retain_blocks,s.retain_rows,Directory.recordNodes,Packet.fieldList,
    List.length_cons,List.flatMap_append,List.length_append,List.length_map,List.map_append,List.sum_append,
    tieWords,tieGuards]
  simp only [Site.retain]
  omega

/-- Carrying the old complete bank and factor observations adds exactly the
previous input width to the cumulative expanded budget. -/
theorem Site.expandedLoad_retain (s : Site) (n : ℕ) (cuts : List Slice) :
    (s.retain n cuts).expandedLoad = s.expandedLoad + s.incoming := by
  simp only [expandedLoad,Directory.visitCount_eq,s.retain_occurrences]
  change s.work + s.incoming + s.directory.occurrences.length = _
  omega

variable {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
  {ne np : ℕ} (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np) (v : N.Site)

/-- The physical incoming array has one lane for every distinct incident cable
bit and attached external bit; the virtual site's self-loops appear once. -/
theorem incoming_eq_widths :
    incoming N v = incidentWidth N v + portWidth N v := by
  let wire := (Fintype.equivFin N.Edge).toEmbedding
  let port := (Fintype.equivFin P).toEmbedding
  have h := Fintype.card_congr (sourceOrder N wire port v)
  rw [Fintype.card_fin] at h
  simpa only [InputLane,Fintype.card_sum,Fintype.card_sigma,Fintype.card_fin,incidentWidth,portWidth]
    using h.symm

variable {m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m) (p : Pack D P bits K)
  {A : Type} [Fintype A] (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
  (binName : A → ℕ) (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)

private noncomputable abbrev G := (output e p bin perm positive first q).layout

variable (old : p.layout.Site) {next : ℕ} (oldID : p.layout.Edge ↪ Fin ne)
  (newID : (G e p bin perm positive first q).Edge ↪ Fin next)

/-- The actual cut-descriptor enumeration has the cardinal charged at its
owning physical site, including the retained self-loop convention. -/
theorem layerCuts_length :
    (layerCuts e p bin perm binName positive first q old oldID newID portID).length =
      tieRows (G e p bin perm positive first q) (gathered e p bin perm positive first q (.inl old)) (.inl old) := by
  rw [old_tieRows e p bin perm positive first q old]
  simp [layerCuts,LayerRow]

/-- The actual sparse site-local program installed at this inherited site fits
the same cumulative fields that are propagated by the typed adaptive history. -/
theorem Site.retain_charged (s : Site) (prior payload : p.layout.Site → ℕ)
    (hin : s.incoming = Inherited.incoming p.layout old) (hs : s.staticNodes ≤ prior old) (he : s.expandedLoad ≤ payload old) :
    let cuts := layerCuts e p bin perm binName positive first q old oldID newID portID
    let out := s.retain (Inherited.incoming (G e p bin perm positive first q) (.inl old)) cuts
    out.staticNodes ≤ nextPrior e p bin perm positive first q prior (.inl old) ∧
      out.expandedLoad ≤ nextPayload e p bin perm positive first q payload (.inl old) := by
  dsimp only
  rw [s.staticNodes_retain,s.expandedLoad_retain,layerCuts_length,hin,incoming_eq_widths p.layout old]
  dsimp only [nextPrior,Sum.elim_inl,nextPayload]
  exact ⟨Nat.add_le_add hs (Nat.mul_le_mul_right _ (by decide)),Nat.add_le_add_right he _⟩

end Packing.Inherited

end BorderVNP
end Computability
end OAI
