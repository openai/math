import OAI.Computability.VPVNP.CompressorRefreshMapCallWords
import OAI.Computability.VPVNP.PairSimulationMapWorkspace
import OAI.Computability.VPVNP.PairSimulationNodeFieldSpace

/-!
# Uniform private workspace bounds for the actual refresh operand slices

All four kinds of physical operand start lie at most one maximum wire width beyond
the larger of the two node-buffer ends. Adding their raw width, including the full
selector suffix, needs at most one more wire width. The resulting bound also covers
absent endpoints, whose starts are nevertheless installed in the native descriptor.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.MapCallWords

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh NewSlots
open PairSimulation NodeArguments RefreshMapOperands MotifConversion MotifSelector PhaseRecipe OperandInputs
open scoped Fin.CommRing
open private copies_eq from OAI.Computability.VPVNP.CompressorRefreshMapCallWords

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} {g : ℕ} (B : S.Templates)
  (X : State S.portExponent (S.portExponent+g))
  (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)
  (p : (X.Base × BitWord g) × Fin (2^S.portExponent)) (A : Arena) (child parent : ℕ)
  (old : X.network.Half (oldSite X p))
  (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order))
    B.refresh S.port_order S.degree_bounds.2 choice).network.Half (promotedSites p))

local notation "D" => 2^S.portExponent
local notation "H" => 2^S.expanderExponent
local notation "P" => S.graph.toSlotGraph
local notation "hD" => S.port_order
local notation "hd" => And.right S.degree_bounds
local notation "hc" => And.left (S.port_bound.connected_and_pos S.port_order)
local notation "internal" => blockSupplyWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) S.graph (Nat.two_pow_pos _) hc B.refresh choice
local notation "Y" => dyadicRefreshNext X S.graph (Nat.two_pow_pos _) hc B.refresh hD hd choice
local notation "E₀" => entryInput B X choice p old new
local notation "base" => operandBase X p P hD hd internal A child parent

private theorem end_of_field {a l : ℕ} (Z : State a l) (u : Z.network.Site) (v : Z.network.Half u)
    (A : Arena) (n : ℕ) (dir : Bool) (j : Fin (2^a)) :
    A.fieldAddress Z u n dir j ≤ A.base n + (packed Z u v).length :=
  (Nat.le_add_right ..).trans (field_end_le Z u v A n dir j)

private theorem selected_widths (b : (X.Base × BitWord g) × Fin D) :
    (∑ j, bundleWidths (bitWordFinEquiv _) (splitWidths X) b j) ≤ (Y).maxWireWidth ∧
      ∀ h : Fin H, internal b.1 (b.2,h) ≤ (Y).maxWireWidth := by
  have bound (slot : RefreshSlot H S.baseDegree) := (Y).width_le_maxWireWidth
    (refreshedCoordinates.symm (b,refreshSlots hd slot))
  change ∀ slot, newWidths hd _ internal (refreshedCoordinates (refreshedCoordinates.symm _)).1
    (refreshedCoordinates (refreshedCoordinates.symm (b,refreshSlots hd slot))).2 ≤ (Y).maxWireWidth at bound
  simp only [Equiv.apply_symm_apply,newWidths,Equiv.symm_apply_apply] at bound
  exact ⟨bound (.inl 0),fun h => bound (.inr (.inl h))⟩

private theorem external_offset_le (dir : Bool) (j : Fin D) :
    externalOffset X p dir j ≤ (Y).maxWireWidth := by
  let G := splitSlots X
  let port := bitWordFinEquiv S.portExponent
  have h (e : Arc (X.Base × BitWord g) D) : (outgoingRecord G port (splitWidths X) e).offset ≤ (Y).maxWireWidth :=
    (Nat.le_add_right ..).trans ((segment_fits G port (splitWidths X) e).trans (selected_widths B X choice e.1).1)
  cases dir
  · exact h (p,j)
  · change (incomingRecord G port (splitWidths X) (p,j)).offset ≤ _
    rw [incomingRecord_matching]
    exact h _

set_option maxHeartbeats 1200000 in
/-- A single numerical address bound suffices for all raw fields, independent of their
presence at the local port and the values of the two private half-wires. -/
theorem operand_input_end (top maxWidth : ℕ) (oldEnd : A.base child + (packed X (oldSite X p) old).length ≤ top)
    (newEnd : A.base parent + (packed Y (promotedSites p) new).length ≤ top)
    (oldWidth : X.maxWireWidth ≤ maxWidth) (newWidth : (Y).maxWireWidth ≤ maxWidth) :
    ∀ f, base f + MapWorkspace.rawWidth (E₀).demand (E₀).payload B.refresh.selectorBits
      (repetitions B.refresh (E₀).demand) f ≤ top+2*maxWidth := by
  have oldAt (dir) (j) := (end_of_field X (oldSite X p) old A child dir j).trans oldEnd
  have newAt (dir) (j) := (end_of_field Y (promotedSites p) new A parent dir j).trans newEnd
  have dw (e : Tie D) : (E₀).demand e ≤ maxWidth := by
    change internalWidth _ _ p.1 e ≤ _
    unfold internalWidth
    split <;> exact (X.width_le_maxWireWidth _).trans oldWidth
  have sw (e : Fin D × Fin H) : (E₀).payload e + repetitions B.refresh (E₀).demand * B.refresh.selectorBits ≤ maxWidth :=
    ((selected_widths B X choice (p.1,e.1)).2 e.2).trans newWidth
  rintro (⟨dir,e⟩ | ⟨dir,e⟩)
  · have hw := dw e
    cases dir
    · have ha := oldAt (!e.1) (tieTarget e)
      change A.fieldAddress X (oldSite X p) child (!e.1) (tieTarget e) + (E₀).demand e ≤ _; omega
    · have ha := newAt (!e.1) (refreshSlots hd (.inl 0))
      have ho := (external_offset_le B X choice p (!e.1) (tieSource e)).trans newWidth
      change A.fieldAddress Y (promotedSites p) parent (!e.1) (refreshSlots hd (.inl 0)) +
        externalOffset X p (!e.1) (tieSource e) + (E₀).demand e ≤ _; omega
  · have hw := sw e
    cases dir
    · have ha := newAt false (refreshSlots hd (.inr (.inl e.2)))
      change A.fieldAddress Y (promotedSites p) parent false (refreshSlots hd (.inr (.inl e.2))) +
        ((E₀).payload e + repetitions B.refresh (E₀).demand*B.refresh.selectorBits) ≤ _; omega
    · have ha := newAt true (refreshSlots hd (.inr (.inl ((P).target e).2)))
      change A.fieldAddress Y (promotedSites p) parent true (refreshSlots hd (.inr (.inl ((P).target e).2))) +
        ((E₀).payload e + repetitions B.refresh (E₀).demand*B.refresh.selectorBits) ≤ _; omega

/-- Reserve the complete private descriptor or the expander pointer directory, whichever
needs more words. Both are consumed before the selector and label arrays. -/
noncomputable def headCapacity (degree expander : ℕ) := max (2*(degree*expander))
  (Fintype.card (MapCallSetup.Arg (Tie degree) (Fin degree × Fin expander)))

/-- Concrete scratch heads for a single refresh map. The histogram has its own
previously allocated range and may be shared across successive map calls. -/
noncomputable def regions (directory hist : ℕ) : MapWorkspace.Regions (Tie D) (Fin D × Fin H) :=
  let source := directory + headCapacity D H
  ⟨base,directory,source,source+repetitions B.refresh (E₀).demand,hist⟩

/-- Every array in the selected workspace meets its concrete address constraints.
The four scalar capacity bounds suffice for all selector choices and port incidences. -/
theorem regions_ordered {pcs regs params histCount : ℕ} (grid : B.refresh.grid.demands)
    (L : MapEntryTable.Allocation B.refresh grid p.2 regs params) (loc : L.Address → Fin pcs)
    (top maxWidth directory hist limit : ℕ)
    (oldEnd : A.base child + (packed X (oldSite X p) old).length ≤ top)
    (newEnd : A.base parent + (packed Y (promotedSites p) new).length ≤ top)
    (oldWidth : X.maxWireWidth ≤ maxWidth) (newWidth : (Y).maxWireWidth ≤ maxWidth)
    (inputsEnd : top+2*maxWidth ≤ directory)
    (histEnd : hist+histCount ≤ directory)
    (workEnd : directory+headCapacity D H+2*repetitions B.refresh (E₀).demand ≤ limit) :
    let R := regions B X choice p A child parent old new directory hist
    MapWorkspace.Ordered (L.program loc) (E₀).demand (E₀).payload R (repetitions B.refresh (E₀).demand) histCount limit := by
  have ports := MapPortAgreement.ports_length_le S.portSupply p.2 L.edgeOrder
  rw [Fintype.card_prod,Fintype.card_fin,Fintype.card_fin] at ports
  have cap := le_max_left (2*(D*H)) (Fintype.card (MapCallSetup.Arg (Tie D) (Fin D × Fin H)))
  change 2*(D*H) ≤ headCapacity D H at cap
  have inputEnd := operand_input_end B X choice p A child parent old new top maxWidth oldEnd newEnd oldWidth newWidth
  constructor
  · exact fun f => (inputEnd f).trans inputsEnd
  · exact Nat.add_le_add_left (ports.trans cap) directory
  · exact le_rfl
  · change directory+headCapacity D H + repetitions B.refresh (E₀).demand + repetitions B.refresh (E₀).demand ≤ limit
    omega
  · change hist+histCount ≤ limit; omega
  · exact Or.inr histEnd

/-- Online evaluation of the source and target heads uses the same stored repetition
word that the raw descriptor publishes. Only the reserved directory and histogram bases
come from the outer private allocation. -/
noncomputable def plannedHeads (degree expander stride : ℕ) (I : Input) (directory hist : Expr) : WorkHeads :=
  let source := directory.add (.lit (headCapacity degree expander))
  ⟨directory,source,source.add (copies degree stride I),hist⟩

variable {bits t : ℕ} (oldDir newDir : IncidenceDirectory bits) (ties : Fin t ≃ Tie (2^S.portExponent)) (start stride : ℕ)
  (pub : Fin 5 → W bits) (state : W bits) (m : Memory bits) (I : Input)

local notation "Pₗ" => Allocation.plan X (S.degreeExponent 0) H t stride start
local notation "Q" => Allocation.Plan.scratch Pₗ bits
local notation "src" => word (bits := bits) (Allocation.Plan.demand Pₗ)
local notation "term" => word (bits := bits) (Allocation.Plan.term Pₗ)
local notation "N" => Fintype.card X.Base*D*2^g*D

theorem plannedHeads_eval {fit : N ≤ 2^bits} (directory histogram : Expr) (dir hist : ℕ)
    (hdir : directory.eval pub state m = word dir) (hhist : histogram.eval pub state m = word hist)
    (args : Describes I pub state m X p P hD hd internal A child parent oldDir newDir Q src term)
    (stored : Build.Stored X S.graph (Nat.two_pow_pos _) hc B.refresh choice ties start stride fit m) (wide : D < 2^bits) :
    let J := plannedHeads D H stride I directory histogram
    let R := regions B X choice p A child parent old new dir hist
    J.directory.eval pub state m = word R.directory ∧ J.source.eval pub state m = word R.source ∧
      J.target.eval pub state m = word R.target ∧ J.hist.eval pub state m = word R.hist := by
  have count := copies_eq B X choice p A child parent oldDir newDir ties start stride pub state m I args stored wide
  have srcEq : (directory.add (.lit (headCapacity D H))).eval pub state m = word (dir + headCapacity D H) := by
    change directory.eval pub state m + (headCapacity D H : W bits) = _
    rw [hdir]; exact (Nat.cast_add ..).symm
  refine ⟨hdir,srcEq,?_,hhist⟩
  change (directory.add (.lit (headCapacity D H))).eval pub state m + (copies D stride I).eval pub state m = _
  rw [srcEq,count]; exact (Nat.cast_add ..).symm

end CompressorRecords.PortRefresh.MapCallWords

end VPVNP
end Computability
end OAI
