import OAI.Computability.VPVNP.PairShrinkABFrameAddress
import OAI.Computability.VPVNP.PairShrinkCallFields
import OAI.Computability.VPVNP.ShrinkLocalMaps
import OAI.Computability.VPVNP.PairSimulationMapRow
import OAI.Computability.VPVNP.LiveHeaderBits

/-!
# The four demand endpoints of a resident shrinking map

The assembled AB word uses the demand-bit repartition of the old thick arcs.
The two unsplit CD endpoints remain in their old child packets. Reading these
four bit strings supplies exactly the local demand argument of the six-party
matrix; an endpoint absent at the chosen party has width zero.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkCallDemandCells

open Compression Compression.PackingData Compression.ShrinkMotif
open NetworkKernel BurstRAM MotifEntry CompressorRecords
open scoped Fin.CommRing

variable {a g w : ℕ} (X : State a (packingLaneBits a g))
/-- Classical equality of base vertices for identifying the old sites assigned to each demand
endpoint. -/
noncomputable local instance : DecidableEq X.Base := Classical.decEq _
local notation "P" => X.packingData
local notation "BW" => X.packingData.shrinkDemandWidths X.shrinkNumber X.packingWidth
local notation "hc" => State.two_le_packingColors a
local notation "hd" => Nat.two_pow_pos a

variable (layout : Bool) (m : X.packingData.Motif) (party : Fin 6)

/-- Independent old half-wire assignments for all sites placed at this motif party's resident
site in the chosen layout. -/
abbrev Old (j : Fin 6) := Placed ((P).shrinkPlace layout) ((P).oldWireNetwork X.packingWidth).Half
  ((P).shrinkPartySite layout m j)

/-- The length and bit string of the indicated demand endpoint at this party, extracted from
its placed old half-wire assignments. -/
noncomputable def endpoint (x : Old X layout m party) :=
  MapRow.endpoint demandSource demandTarget party (BW m)
    (demandBits demandSource demandTarget party
      ((P).shrinkLocalDemandArg hc hd X.shrinkNumber X.shrinkOrder X.packingWidth layout m party x))

private theorem input_bits {n : ℕ} (bits : Fin n → Bool) (i : Fin n) :
    inputBits ((RAMSerialization.wordBits n).symm bits) i = bits i := by
  rw [inputBits, LiveHeader.testBit_wordBits, Equiv.apply_symm_apply]

/-- Convert the two old network arguments to the AB copy program's input coordinates. -/
noncomputable def abHalf (dir : Bool) (x : Old X layout m (if dir then 1 else 0)) :
    (P).PlacedHalf X.packingWidth layout (ShrinkOldHalves.abSite X m dir) := by
  cases dir <;> exact (P).shrinkPlacedHalf X.packingWidth layout _ rfl x

/-- The bit value produced by the AB column program at each of its two endpoints. -/
noncomputable def abBit (dir : Bool) (x : Old X layout m (if dir then 1 else 0))
    (i : Fin ((P).abWidth X.shrinkNumber X.packingWidth m)) : Bool :=
  ShrinkAB.operand (P) X.shrinkNumber X.shrinkOrder X.packingWidth ⟨m, rfl⟩ hc hd
    (ShrinkOldHalves.abData X layout m dir (abHalf X layout m dir x)) i

variable (A : NodeArguments.Arena) (nodes : X.network.Site → ℕ)

/-- Native AB slice writes supply the staged word required by the local demand reader. -/
theorem ab_written (dir : Bool) (x : Old X layout m (if dir then 1 else 0))
    (arcFit : Fintype.card X.Base * 2 ^ packingLaneBits a g * 2 ^ a ≤ 2 ^ w)
    (bucketFit : let count := Fintype.card X.Base * (2 ^ Shrink.J a * 2 ^ g) * 2 ^ a
      count + count ≤ 2 ^ w)
    (first dest : ℕ) (old : Word w → Word w)
    (room : dest + (P).abWidth X.shrinkNumber X.packingWidth m ≤ 2 ^ w)
    (i : Fin ((P).abWidth X.shrinkNumber X.packingWidth m)) :
    let rows := fun j ↦ ShrinkAB.Physical.row X m arcFit bucketFit j A nodes layout dir
      (abHalf X layout m dir x) (first := first) (dest := dest)
    ResidentColumn.writes rows (List.finRange (2 ^ Shrink.colors a * 2 ^ a / 4)) old
        ((dest + i.val : ℕ) : Word w) = PrivateFields.bitValue w (abBit X layout m dir x i) :=
  ShrinkAB.Physical.writes_operand X m arcFit bucketFit A nodes layout dir
    (abHalf X layout m dir x) old room i

/-- Directly addressed fields at parties C and D. -/
noncomputable def cdBase (dir : Bool) := ShrinkOldHalves.address X A nodes m.1
  (if dir then !(ShrinkOldHalves.cDirection X m) else ShrinkOldHalves.cDirection X m)

/-- The original child packets survive a gather that changes only private
cells at or beyond the staging pivot. This applies to either unsplit CD end. -/
theorem placedPackets_frame {endAddr pivot : ℕ} {site}
    {x : (P).PlacedHalf X.packingWidth layout site} {old new : Word w → Word w}
    (read : ShrinkOldHalves.PlacedPackets X layout A nodes old site x endAddr)
    (ends : ∀ u, A.base (nodes u) + A.stride ≤ pivot)
    (frame : ∀ q : Word w, q.val < pivot → new q = old q) :
    ShrinkOldHalves.PlacedPackets X layout A nodes new site x endAddr := by
  intro u hu
  let v := X.packingInputIso.site u
  let z := (X.packingHalfEquiv u).symm (x u hu)
  let q : NodeArguments.Packet := ⟨nodes v, NodeArguments.packed X v z⟩
  obtain ⟨fits, stored⟩ : q.Fits A w endAddr ∧ q.Stored A (DFS.scratch endAddr old) := read u hu
  refine ⟨fits, stored.congr ?_⟩
  intro i
  let a : Word w := ((A.base q.node + i.val : ℕ) : Word w)
  have ha : a.val = A.base q.node + i.val :=
    Nat.mod_eq_of_lt ((Nat.add_lt_add_left i.isLt _).trans_le fits.2.2)
  have below : a.val < pivot := by
    rw [ha]
    exact (Nat.add_lt_add_left (i.isLt.trans_le fits.2.1) _).trans_le (ends v)
  have above : endAddr ≤ a.val := by rw [ha]; exact fits.1.trans (Nat.le_add_right ..)
  change NodeArguments.rawScratch (DFS.scratch endAddr new) a =
    NodeArguments.rawScratch (DFS.scratch endAddr old) a
  simpa only [NodeArguments.rawScratch, dite_eq_left above, DFS.scratch] using frame a below

/-- Required AB output and the independent child packets selected at C and D. -/
structure Readback (x : Old X layout m party) (priv : Word w → Word w)
    (dest endAddr : ℕ) : Prop where
  ab : ∀ (dir : Bool) (h : party = if dir then 1 else 0)
    (i : Fin ((P).abWidth X.shrinkNumber X.packingWidth m)),
    priv ((dest + i.val : ℕ) : Word w) = PrivateFields.bitValue w (abBit X layout m dir (h ▸ x) i)
  c : ∀ h : party = 2, ShrinkOldHalves.PlacedPackets X layout A nodes priv _
    ((P).shrinkPlacedHalf X.packingWidth layout _ ((P).shrinkPartySite_C layout m) (h ▸ x)) endAddr
  d : ∀ h : party = 3, ShrinkOldHalves.PlacedPackets X layout A nodes priv _
    ((P).shrinkPlacedHalf X.packingWidth layout ((P).roleD layout m) rfl
      (h ▸ x : Old X layout m 3)) endAddr

set_option maxHeartbeats 1600000 in
-- Reducing all four dependent half-wire widths uses the packing and word equivalences.
/-- Arbitrary, independently supplied old half-wires give the native demand
bits at every endpoint of the actual selected map. -/
theorem demandCells (x : Old X layout m party) (priv : Word w → Word w) (dest endAddr : ℕ)
    (h : Readback X layout m party A nodes x priv dest endAddr)
    (base : Bool × Bool → ℕ)
    (bases : ∀ dir e, party = (if dir then demandTarget e else demandSource e) →
      base (dir, e) = if e then cdBase X m A nodes dir else dest)
    (q : Bool × Bool) (i : Fin (endpoint X layout m party x q).1) :
    priv ((base q + i.val : ℕ) : Word w) =
      PrimedInputRAM.encodeBit w ((endpoint X layout m party x q).2 i) := by
  rcases q with ⟨dir, e⟩
  revert i
  cases dir <;> cases e
  · by_cases hit : party = demandSource false
    · subst party
      rw [bases false false rfl]
      change ∀ i : Fin (BW m false), _ =
        PrimedInputRAM.encodeBit w (inputBits ((RAMSerialization.wordBits _).symm _) i)
      intro i
      erw [input_bits]
      exact h.ab false rfl i
    · have empty : endpoint X layout m party x (false, false) = ⟨0, Fin.elim0⟩ := by
        simp [endpoint, MapRow.endpoint, hit]
      rw [empty]
      exact fun i ↦ i.elim0
  · by_cases hit : party = demandSource true
    · subst party
      rw [bases false true rfl]
      change ∀ i : Fin (BW m true), _ =
        PrimedInputRAM.encodeBit w (inputBits ((RAMSerialization.wordBits _).symm _) i)
      intro i
      erw [input_bits]
      exact ShrinkOldHalves.read_C X layout m (h.c rfl) i
    · have empty : endpoint X layout m party x (false, true) = ⟨0, Fin.elim0⟩ := by
        simp [endpoint, MapRow.endpoint, hit]
      rw [empty]
      exact fun i ↦ i.elim0
  · by_cases hit : party = demandTarget false
    · subst party
      rw [bases true false rfl]
      change ∀ i : Fin (BW m false), _ =
        PrimedInputRAM.encodeBit w (inputBits ((RAMSerialization.wordBits _).symm _) i)
      intro i
      erw [input_bits]
      exact h.ab true rfl i
    · have empty : endpoint X layout m party x (true, false) = ⟨0, Fin.elim0⟩ := by
        simp [endpoint, MapRow.endpoint, hit]
      rw [empty]
      exact fun i ↦ i.elim0
  · by_cases hit : party = demandTarget true
    · subst party
      rw [bases true true rfl]
      change ∀ i : Fin (BW m true), _ =
        PrimedInputRAM.encodeBit w (inputBits ((RAMSerialization.wordBits _).symm _) i)
      intro i
      erw [input_bits]
      exact ShrinkOldHalves.read_D X layout m (h.d rfl) i
    · have empty : endpoint X layout m party x (true, true) = ⟨0, Fin.elim0⟩ := by
        simp [endpoint, MapRow.endpoint, hit]
      rw [empty]
      exact fun i ↦ i.elim0

/-- Read all demand cells at the actual descriptor's field bases. Only A, B, C
and D have a nonempty demand endpoint. -/
theorem scratch_demandCells (s : ShrinkCallFields.Scratch) (ord : ℕ)
    (x : Old X layout m party) (priv : Word w → Word w) (endAddr : ℕ)
    (h : Readback X layout m party A nodes x priv s.staging endAddr)
    (q : Bool × Bool) (i : Fin (endpoint X layout m party x q).1) :
    let f := s.fieldBase ord party layout (cdBase X m A nodes) (.inl q)
    priv ((f + i.val : ℕ) : Word w) =
      PrimedInputRAM.encodeBit w ((endpoint X layout m party x q).2 i) := by
  apply demandCells X layout m party A nodes x priv s.staging endAddr h
    (fun q ↦ s.fieldBase ord party layout (cdBase X m A nodes) (.inl q)) _ q i
  intro dir e eq
  simp only [ShrinkCallFields.Scratch.fieldBase, ShrinkCallFields.demandParty, eq, ite_true]

end PairSimulation.ShrinkCallDemandCells

end VPVNP
end Computability
end OAI
