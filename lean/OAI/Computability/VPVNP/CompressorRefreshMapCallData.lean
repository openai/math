import OAI.Computability.VPVNP.CompressorRefreshMapCallWords
import OAI.Computability.VPVNP.PairSimulationMapWorkspace
import OAI.Computability.VPVNP.PairSimulationMapArgumentInput

/-!
# Physical input of the selected refresh map call

The private descriptor and the old and new node frames supply the map's register setup.
Demand reads use their two independent halves. The agreement scan reads each full
supply, including its selector suffix. The private directory follows the complete input
interval, so the directory initializer preserves those data cells.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.RefreshMapOperands

open Compression PairSimulation.NodeArguments BurstRAM

/-- Writes outside a packed node's interval preserve all independent half-wire bits
in its argument bank. -/
theorem NodeFields.transfer {a g w : ℕ} {A : Arena} {node : ℕ} {X : State a g} {v : X.network.Site}
    {z : X.network.Half v} {before after : Word w → Word w} (fields : NodeFields A node X v z before)
    (frame : ∀ addr, A.base node ≤ addr → addr < A.base node + (packed X v z).length →
      after (Fin.ofNat (2^w) addr) = before (Fin.ofNat (2^w) addr)) : NodeFields A node X v z after := by
  intro dir j i
  have lo : A.base node ≤ A.fieldAddress X v node dir j := Nat.le_add_right ..
  have endLe := field_end_le X v z A node dir j
  have hold := frame (A.fieldAddress X v node dir j+i.val) (by omega) (by have := i.isLt; omega)
  exact hold.trans (fields dir j i)

end CompressorRecords.RefreshMapOperands

namespace CompressorRecords.PortRefresh.MapCallData

open BurstRAM BurstRAM.PrivateRAM Compression Compression.Refresh Compression.DegreeRefresh NewSlots
open PairSimulation PairSimulation.LocalHistory PairSimulation.NodeArguments RefreshMapOperands MotifConversion MotifSelector
open MapEntryTable MapPortAgreement MapResidentAgreement MapLookup MotifEntry
open scoped Fin.CommRing

variable {bits g t histCount pcs regs params : ℕ} {k : Type} [_root_.Field k] {S : BlockSchedule k}
  (B : S.Templates) (X : State S.portExponent (S.portExponent+g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (p : (X.Base × BitWord g) × Fin (2^S.portExponent)) (A : Arena) (child parent : ℕ)
  (old : X.network.Half (oldSite X p))
  (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order))
    B.refresh S.port_order S.degree_bounds.2 choice).network.Half (promotedSites p))
  (grid : B.refresh.grid.demands) (L : MapEntryTable.Allocation B.refresh grid p.2 regs params) (loc : L.Address → Fin pcs)
  (ties : Fin t ≃ Tie (2^S.portExponent)) (start stride : ℕ) (m : Memory bits)

local notation "D" => 2^S.portExponent
local notation "H" => 2^S.expanderExponent
local notation "P" => S.graph.toSlotGraph
local notation "hD" => S.port_order
local notation "hd" => And.right S.degree_bounds
local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "internal" => blockSupplyWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) S.graph (Nat.two_pow_pos _) hc B.refresh choice
local notation "Y" => dyadicRefreshNext X S.graph (Nat.two_pow_pos _) hc B.refresh hD hd choice
local notation "I" => entryInput B X choice p old new
local notation "u" => repetitions B.refresh (EntryInput.demand I)
local notation "d" => demandBits tieSource tieTarget (Prod.snd p) (EntryInput.demandBits I)
local notation "x" => mapHalf S.portSupply (fun _ => inputBits) (EntryInput.supplyBits I)
local notation "N" => Fintype.card X.Base*D*2^g*D
local notation "base" => operandBase X p P hD hd internal A child parent
local notation "pb" => supplyPortBase B X choice p A child parent
local notation "Raw" => MapWorkspace.rawWidth (EntryInput.demand I) (EntryInput.payload I) B.refresh.selectorBits u

variable (priv : W bits → W bits)

private def segmentData (priv : W bits → W bits) (start : ℕ) (f : (n : ℕ) × (Fin n → Bool)) : Prop :=
  ∀ i : Fin f.1, priv ((start+i.val : ℕ) : W bits) = PrimedInputRAM.encodeBit bits (f.2 i)

private theorem demand_data (oldData : NodeFields A child X (oldSite X p) old priv)
    (newData : NodeFields A parent Y (promotedSites p) new priv) (q : Bool × Tie D) :
    ∀ l : Fin (MapRow.endpoint tieSource tieTarget p.2 (I).demand d q).1,
      priv ((base (.inl q)+l.val : ℕ) : W bits) =
        PrimedInputRAM.encodeBit bits ((MapRow.endpoint tieSource tieTarget p.2 (I).demand d q).2 l) := by
  change segmentData priv (base (.inl q)) (MapRow.endpoint tieSource tieTarget p.2 (I).demand d q)
  obtain ⟨b,e⟩ := q
  cases b <;> rw [MapRow.endpoint]
  · split
    · rename_i he; exact demand_out_read X p P hD hd internal A child parent old new priv oldData e he
    · intro i; exact i.elim0
  · split
    · rename_i he; exact demand_in_read X p P hD hd internal A child parent old new priv newData e he
    · intro i; exact i.elim0

private theorem demand_len (q : Bool × Tie D) :
    (MapRow.endpoint tieSource tieTarget p.2 (I).demand d q).1 ≤ (I).demand q.2 := by
  obtain ⟨b,e⟩ := q
  cases b <;> rw [MapRow.endpoint] <;> split <;> simp

/-- The raw data of the selected refresh, before the writer publishes the private
descriptor. Every live cell precedes both the directory and the descriptor. -/
theorem resident {fit : N ≤ 2^bits} (Wk : MapCallWords.Workspace B X choice p old new grid L loc histCount bits)
    (addr : W bits) (stored : Build.Stored X S.graph (Nat.two_pow_pos _) hc B.refresh choice ties start stride fit m)
    (oldData : NodeFields A child X (oldSite X p) old priv)
    (newData : NodeFields A parent Y (promotedSites p) new priv)
    (bases : Wk.base = base) (portBases : Wk.portBase = pb)
    (fieldEnd : ∀ f, Wk.base f + Raw f ≤ Wk.directory.val)
    (directoryRoom : Wk.directory.val + (ports S.portSupply p.2 L.edgeOrder).length ≤ 2^bits)
    (beforeDescriptor : Wk.directory.val ≤ addr.val) :
    MapArgumentWriter.ResidentFields L loc Wk addr priv := by
  have portEq (t : Port S.portSupply p.2) :
      Wk.portBase t = (Wk.base (MapDirectoryInit.portField t) : W bits) := by
    rw [portBases,bases]; cases t <;> rfl
  have separated (cell : W bits) (hcell : cell.val < Wk.directory.val) :
      MapArgumentWriter.separated L loc Wk addr cell := by
    refine ⟨Or.inl (hcell.trans_le beforeDescriptor),fun a => ?_⟩
    have hi : a.val < (ports S.portSupply p.2 L.edgeOrder).length := a.isLt
    apply Fin.ne_of_val_ne
    rw [Fin.val_add,Fin.val_natCast,Nat.mod_eq_of_lt (show a.val < 2^bits by omega),Nat.mod_eq_of_lt (by omega)]
    omega
  refine ⟨?_,portEq,?_,?_⟩
  · intro e
    have h := (stored.readback p.1).2.2 (finProdFinEquiv e)
    rw [Equiv.symm_apply_apply] at h
    change (choice p.1).val e < 2^bits
    rw [← h]; exact Fin.isLt _
  · intro t l
    constructor
    · rw [portBases]
      exact selectorCells B X choice p old new A child parent priv newData t l
    · apply separated
      have hlen : Raw (MapDirectoryInit.portField t) = (I).payload (edge t) + u*B.refresh.selectorBits := by
        cases t <;> rfl
      have lo := fieldEnd (MapDirectoryInit.portField t)
      rw [hlen] at lo
      rw [portEq,← Nat.cast_add]
      exact (Nat.mod_le ..).trans_lt ((Nat.add_lt_add_left l.isLt _).trans_le lo)
  · intro q l
    constructor
    · rw [bases]
      exact demand_data B X choice p A child parent old new priv oldData newData q l
    · apply separated
      have hl := l.isLt.trans_le (demand_len B X choice p old new q)
      have bound := fieldEnd (.inl q)
      change Wk.base (.inl q)+(I).demand q.2 ≤ Wk.directory.val at bound
      exact (Nat.mod_le ..).trans_lt ((Nat.add_lt_add_left hl _).trans_le bound)

/-- Specialize the resident data contract to the packed workspace. The ordering of
its scratch and operand regions supplies all bit/descriptor and bit/directory separation. -/
theorem resident_packed {fit : N ≤ 2^bits} {limit n : ℕ}
    (R : MapWorkspace.Regions (Tie D) (Fin D × Fin H))
    (C : MapWorkspace.Capacity B.refresh bits n limit) (hu : u ≤ n)
    (ordered : MapWorkspace.Ordered (L.program loc) (I).demand (I).payload R u histCount limit)
    (addr : W bits) (beforeDescriptor : R.directory ≤ addr.val)
    (stored : Build.Stored X S.graph (Nat.two_pow_pos _) hc B.refresh choice ties start stride fit m)
    (oldData : NodeFields A child X (oldSite X p) old priv)
    (newData : NodeFields A parent Y (promotedSites p) new priv) (bases : R.base = base) :
    let Wk := MapWorkspace.workspace (L.program loc) R d x C hu ordered
    MapArgumentWriter.ResidentFields L loc Wk addr priv := by
  let Wk := MapWorkspace.workspace (L.program loc) R d x C hu ordered
  have hdir : R.directory + (ports S.portSupply p.2 L.edgeOrder).length ≤ 2^bits :=
    ordered.directoryEnd.trans ((Nat.le_add_right ..).trans (ordered.selectorEnd.trans
      ((Nat.le_add_right ..).trans (ordered.labelEnd.trans C.room.le))))
  have hdr : Wk.directory.val = R.directory :=
    Nat.mod_eq_of_lt (show R.directory < 2^bits by
      have := ordered.directoryEnd; have := ordered.selectorEnd; have := ordered.labelEnd; have := C.room; omega)
  apply resident B X choice p A child parent old new grid L loc ties start stride m priv Wk addr stored oldData newData bases
  · funext t
    change (R.base (MapDirectoryInit.portField t) : W bits) = _
    rw [bases]; cases t <;> rfl
  · intro f; rw [hdr]; exact ordered.inputEnd f
  · rw [hdr]; exact hdir
  · rw [hdr]; exact beforeDescriptor

variable (args : MapCallSetup.Arg (Tie (2^S.portExponent)) (Fin (2^S.portExponent) × Fin (2^S.expanderExponent)) ≃
    Fin (Fintype.card (MapCallSetup.Arg (Tie (2^S.portExponent)) (Fin (2^S.portExponent) × Fin (2^S.expanderExponent)))))
  (ptr : Fin regs) (c : Config bits pcs regs)

/-- If the descriptor has already been written, resident fields at the same config
give the ordinary initializer input directly. -/
theorem input {addr : W bits} (Wk : MapCallWords.Workspace B X choice p old new grid L loc histCount bits)
    (descriptor : ∀ a, c.privateMem (c.reg ptr + ((args a).val : W bits)) = MapCallSetup.values L loc Wk a)
    (cells : MapArgumentWriter.ResidentFields L loc Wk addr c.privateMem) :
    MapCallSetup.Input L args loc Wk ptr c :=
  ⟨descriptor,cells.payloadFit,cells.supplyBase,fun t i => (cells.supply t i).1,
    fun q i => (cells.demandCells q i).1,fun t i => (cells.supply t i).2.2,
    fun q i => (cells.demandCells q i).2.2⟩

end CompressorRecords.PortRefresh.MapCallData

end VPVNP
end Computability
end OAI
