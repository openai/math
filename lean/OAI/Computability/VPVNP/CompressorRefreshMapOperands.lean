import OAI.Computability.VPVNP.PairSimulationRecordedMapCalls
import OAI.Computability.VPVNP.PairNodeArguments
import OAI.Computability.VPVNP.CompressorRecordRefresh
import OAI.Computability.VPVNP.PairSimulationMapRowLoop
import OAI.Computability.VPVNP.PairSimulationMapResidentAgreement

/-!
# Operand slices of the degree-refresh map

The two old half-wires are stored independently at the child node. The
two external payloads and the internal expander halves belong to its parent
node. Both ends of an external segment use the prefix offset in the original
outgoing bundle, even when port translation permutes the incoming slots.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.RefreshMapOperands

open Compression Compression.Refresh Compression.DegreeRefresh NetworkKernel
open PairSimulation PairSimulation.NodeArguments PairSimulation.LocalHistory
open scoped Fin.CommRing

variable {a b l w : ℕ}

/-- The independent slot vectors in the private argument buffer of a node. -/
def NodeFields (A : Arena) (node : ℕ) (X : State a l) (v : X.network.Site)
    (z : X.network.Half v) (mem : BurstRAM.Word w → BurstRAM.Word w) : Prop :=
  ∀ dir j (i : Fin (X.halfWidth v dir j)),
    mem ((A.fieldAddress X v node dir j+i.val : ℕ) : BurstRAM.Word w) =
      PrimedInputRAM.encodeBit w (fieldBits X v z dir j i)

theorem nodeFields_store (A : Arena) (node : ℕ) (X : State a l) (v : X.network.Site)
    (z : X.network.Half v) (mem : BurstRAM.Word w → BurstRAM.Word w)
    (fit : A.base node+(packed X v z).length ≤ 2^w) :
    NodeFields A node X v z (PrivateFields.storeBits (A.base node) (packed X v z) mem) :=
  stored_member X v A node z mem fit

private theorem read_word {A : Arena} {node : ℕ} {X : State a l} {v : X.network.Site}
    {z : X.network.Half v} {mem : BurstRAM.Word w → BurstRAM.Word w}
    (rep : NodeFields A node X v z mem) (dir : Bool) (j : Fin (2^a)) {n : ℕ}
    (word : Word n) (same : List.ofFn (fieldBits X v z dir j) = List.ofFn word)
    (i : Fin n) : mem ((A.fieldAddress X v node dir j+i.val : ℕ) : BurstRAM.Word w) =
      PrimedInputRAM.encodeBit w (word i) := by
  have hlen : X.halfWidth v dir j = n := by simpa only [List.length_ofFn] using congrArg List.length same
  subst n
  have h : fieldBits X v z dir j = word := List.ofFn_injective same
  rw [← h]
  exact rep dir j i

private theorem incoming_congr {X : State a l} {u : X.network.Site} (z : X.network.Half u)
    {e e' : X.network.Edge} (he : e = e') (h : u = X.network.dst e) (h' : u = X.network.dst e') :
    List.ofFn (z.2 e h) = List.ofFn (z.2 e' h') := by cases he; rfl

/-- The original site whose lanes are promoted to this port. -/
def oldSite (X : State a (a+l)) (p : (X.Base × BitWord l) × Fin (2^a)) : X.network.Site :=
  (p.1.1,(splitBitWord a l).symm ((bitWordFinEquiv a).symm p.2,p.1.2))

/-- Pulls the incoming half-wire assignment back to the port-split coordinates of the selected
site. -/
noncomputable abbrev oldHalf (X : State a (a+l)) (p : (X.Base × BitWord l) × Fin (2^a))
    (z : X.network.Half (oldSite X p)) :=
  (originalIso (splitSlots X) (bitWordFinEquiv a) (splitWidths X)).pullHalf p
    ((relaneIso X.slots (splitBitWord a l) X.width).pullHalf (originalSites (bitWordFinEquiv a) p) z)

variable (X : State a (a+l)) (p : (X.Base × BitWord l) × Fin (2^a))
local notation "G" => splitSlots X
local notation "port" => bitWordFinEquiv a
local notation "widths" => groupedWidths port (splitWidths X)
local notation "matchOld" => oldPortMatching G port

theorem old_out_read (A : Arena) (node : ℕ) (z : X.network.Half (oldSite X p))
    (mem : BurstRAM.Word w → BurstRAM.Word w) (rep : NodeFields A node X _ z mem)
    (j : Fin (2^a)) (i : Fin (widths ((p.1,j),p.2))) :
    mem ((A.fieldAddress X (oldSite X p) node false j+i.val : ℕ) : BurstRAM.Word w) =
      PrimedInputRAM.encodeBit w ((oldHalf X p z).1 ((p.1,j),p.2) rfl i) := by
  exact read_word rep false j _ rfl i

private theorem oldIncoming_edge (j : Fin (2^a)) :
    let e := (matchOld).symm ((p.1,j),p.2)
    let old := originalIso G port (splitWidths X)
    let split := relaneIso X.slots (splitBitWord a l) X.width
    ((incomingOrder X (oldSite X p)).entries j).val = split.edge (old.edge e) := by
  intro e old split
  change X.slots.actualGraph.target.symm (oldSite X p, j) = _
  apply X.slots.actualGraph.target.injective
  rw [Equiv.apply_symm_apply]
  apply Prod.ext
  · have h := (congrArg source ((matchOld).apply_symm_apply ((p.1,j),p.2))).symm
    exact (congrArg split.site ((congrArg old.site h).trans (old.dst e))).trans (split.dst (old.edge e))
  · exact (congrArg (fun a : Arc (X.Base × BitWord l) (2^a) ↦ a.1.2)
      ((matchOld).apply_symm_apply ((p.1,j),p.2))).symm

theorem old_in_read (A : Arena) (node : ℕ) (z : X.network.Half (oldSite X p))
    (mem : BurstRAM.Word w → BurstRAM.Word w) (rep : NodeFields A node X _ z mem)
    (j : Fin (2^a)) (i : Fin (widths ((matchOld).symm ((p.1,j),p.2)))) :
    mem ((A.fieldAddress X (oldSite X p) node true j+i.val : ℕ) : BurstRAM.Word w) =
      PrimedInputRAM.encodeBit w (incomingHalf (R := ℤ) matchOld widths p.1 p.2 j (oldHalf X p z) i) := by
  apply read_word rep true j _ _ i
  exact incoming_congr z (oldIncoming_edge X p j) _ _

variable {dH : ℕ} (P : SlotGraph (Fin (2^a)) dH) (hD : 1 < 2^a) (hd : dH+1 ≤ 2^b)
  (internal : X.Base × BitWord l → Fin (2^a) × Fin dH → ℕ)

/-- The graph whose independent new halves the selected kernel receives. Taking
the selected block supply widths gives exactly the dyadic refresh output state. -/
noncomputable def newState : State b l where
  Base := X.Base × Fin (2^a)
  baseFintype := inferInstance
  baseNonempty := inferInstance
  baseIndex := State.productIndex X.baseIndex (Equiv.refl (Fin (2^a)))
  slots := degreeRefresh G P hD hd
  width := actualWidths hd port (splitWidths X) internal

local notation "Y" => newState X P hD hd internal

/-- Identifies the promoted network with its refreshed wire coordinates, including the binary
encoding of each internal payload. -/
noncomputable abbrev newIso := promotedIso G port (splitWidths X) P hD hd
  (fun s e ↦ Fin (2^internal s e)) internal (fun s e ↦ (wordIndex (internal s e)).symm)

/-- Pulls the output half-wire assignment at a promoted site back along the promotion
isomorphism. -/
noncomputable abbrev newHalf (z : (Y).network.Half (promotedSites p)) :=
  (newIso X P hD hd internal).pullHalf p z

/-- The outgoing external bundle of the promoted site's half-wire assignment. -/
noncomputable abbrev externalOut (z : (Y).network.Half (promotedSites p)) :=
  (newHalf X p P hD hd internal z).1 (.inl p) rfl

/-- The incoming external bundle indexed by the inverse bundle target at the promoted site. -/
noncomputable abbrev externalIn (z : (Y).network.Half (promotedSites p)) :=
  (newHalf X p P hD hd internal z).2 (.inl ((bundleTarget G).symm p))
    ((bundleTarget G).apply_symm_apply p).symm

/-- Splits the incoming and outgoing external bundles into the incident old-port segments of
this site. -/
noncomputable abbrev segments (z : (Y).network.Half (promotedSites p)) :=
  incidentPortSegments (matchOld) (bundleTarget G) (oldPortMatching_bundle G port) widths p
    (externalOut X p P hD hd internal z) (externalIn X p P hD hd internal z)

private theorem cast_payload {A : Type} {m n : ℕ} (eqw : m = n) (f : A ≃ Word n)
    (h : (A ≃ Word m) = (A ≃ Word n)) (v : A) :
    List.ofFn ((h.mpr f) v) = List.ofFn (f v) := by subst m; rfl

private theorem external_payload (e : (X.Base × BitWord l) × Fin (2^a))
    (v : Word (∑ j, widths (e,j))) :
    List.ofFn ((newIso X P hD hd internal).payload (.inl e) v) = List.ofFn v := by
  simp only [newIso, promotedIso]
  apply cast_payload _ (Equiv.refl _)
  change DegreeRefresh.newWidths hd (bundleWidths port (splitWidths X)) internal e (refreshSlots hd (.inl 0)) = _
  simp [DegreeRefresh.newWidths]

private theorem incoming_external_edge :
    ((incomingOrder Y (promotedSites p)).entries (refreshSlots hd (.inl 0))).val =
      (newIso X P hD hd internal).edge (.inl ((bundleTarget G).symm p)) := by
  let I := newIso X P hD hd internal
  let e := (bundleTarget G).symm p
  change (degreeRefresh G P hD hd).actualGraph.target.symm (promotedSites p, _) =
    (promotedSites e,refreshSlots hd (.inl 0))
  apply (degreeRefresh G P hD hd).actualGraph.target.injective
  rw [Equiv.apply_symm_apply, degreeRefresh_external]
  exact Prod.ext (congrArg promotedSites ((bundleTarget G).apply_symm_apply p).symm) rfl

theorem external_out_read (A : Arena) (node : ℕ) (z : (Y).network.Half (promotedSites p))
    (mem : BurstRAM.Word w → BurstRAM.Word w) (rep : NodeFields A node Y _ z mem)
    (j : Fin (2^a)) (i : Fin (widths (p,j))) :
    mem ((A.fieldAddress Y (promotedSites p) node false (refreshSlots hd (.inl 0)) +
      (PortRefresh.outgoingRecord G port (splitWidths X) (p,j)).offset + i.val : ℕ) : BurstRAM.Word w) =
      PrimedInputRAM.encodeBit w ((segments X p P hD hd internal z).1 j i) := by
  let val := z.1 ((newIso X P hD hd internal).edge (.inl p)) rfl
  let arg := externalOut X p P hD hd internal z
  have e := external_payload X P hD hd internal p arg
  change List.ofFn ((newIso X P hD hd internal).payload (.inl p)
    (((newIso X P hD hd internal).payload (.inl p)).symm val)) = List.ofFn arg at e
  have ev : List.ofFn val = List.ofFn arg :=
    (congrArg List.ofFn (((newIso X P hD hd internal).payload (.inl p)).apply_symm_apply val)).symm.trans e
  obtain ⟨k,hk,hb⟩ := (PortRefresh.local_bit_reads G port (splitWidths X) p j arg
    (externalIn X p P hD hd internal z)).1 i
  rw [Nat.add_assoc, ← hk]
  exact (read_word rep false _ arg ev k).trans (congrArg _ hb.symm)

theorem external_in_read (A : Arena) (node : ℕ) (z : (Y).network.Half (promotedSites p))
    (mem : BurstRAM.Word w → BurstRAM.Word w) (rep : NodeFields A node Y _ z mem)
    (j : Fin (2^a)) (i : Fin (widths ((matchOld).symm (p,j)))) :
    mem ((A.fieldAddress Y (promotedSites p) node true (refreshSlots hd (.inl 0)) +
      (PortRefresh.incomingRecord G port (splitWidths X) (p,j)).offset + i.val : ℕ) : BurstRAM.Word w) =
      PrimedInputRAM.encodeBit w ((segments X p P hD hd internal z).2 j i) := by
  let I := newIso X P hD hd internal
  let edge : OutputEdge (X.Base × BitWord l) (Fin (2^a) × Fin dH) (2^a) (2^b-(dH+1)) := Sum.inl ((bundleTarget G).symm p)
  have he : promotedSites p = (Y).network.dst (I.edge edge) :=
    (congrArg I.site ((bundleTarget G).apply_symm_apply p).symm).trans (I.dst edge)
  let val := z.2 (I.edge edge) he
  let arg := externalIn X p P hD hd internal z
  have e := external_payload X P hD hd internal ((bundleTarget G).symm p) arg
  change List.ofFn (I.payload edge ((I.payload edge).symm val)) = List.ofFn arg at e
  have ev : List.ofFn val = List.ofFn arg :=
    (congrArg List.ofFn ((I.payload edge).apply_symm_apply val)).symm.trans e
  obtain ⟨k,hk,hb⟩ := (PortRefresh.local_bit_reads G port (splitWidths X) p j
    (externalOut X p P hD hd internal z) arg).2 i
  rw [Nat.add_assoc, ← hk]
  exact (read_word rep true _ arg ((incoming_congr z
    (incoming_external_edge X p P hD hd internal) _ he).trans ev) k).trans (congrArg _ hb.symm)

private theorem inputBits_eq {n : ℕ} (x : Fin (2^n)) :
    MotifEntry.inputBits x = (wordIndex n).symm x := by
  funext i
  exact (CursorNetwork.addressWord_bit x i).symm

theorem inputBits_wordIndex {n : ℕ} (x : Word n) :
    MotifEntry.inputBits (wordIndex n x) = x := (inputBits_eq _).trans (Equiv.symm_apply_apply ..)

/-- Extracts the selected port's expander supply half from the refreshed half-wire assignment. -/
noncomputable abbrev supplyArg (z : (Y).network.Half (promotedSites p)) :=
  supplyHalf (R := ℤ) (bundleTarget G) widths Prod.fst (fun e ↦ (P.target e).1)
    (fun s e ↦ Fin (2^internal s e)) (2^b-(dH+1)) p (newHalf X p P hD hd internal z)

private theorem internal_payload (s : X.Base × BitWord l) (e : Fin (2^a) × Fin dH)
    (x : Fin (2^internal s e)) :
    List.ofFn ((newIso X P hD hd internal).payload (.inr (.inl (s,e))) x) =
      List.ofFn (MotifEntry.inputBits x) := by
  rw [inputBits_eq]
  simp only [newIso, promotedIso]
  apply cast_payload _ (wordIndex _).symm
  change DegreeRefresh.newWidths hd (bundleWidths port (splitWidths X)) internal (s,e.1)
    (refreshSlots hd (.inr (.inl e.2))) = _
  simp [DegreeRefresh.newWidths]

theorem supply_out_read (A : Arena) (node : ℕ) (z : (Y).network.Half (promotedSites p))
    (mem : BurstRAM.Word w → BurstRAM.Word w) (rep : NodeFields A node Y _ z mem)
    (e : Fin (2^a) × Fin dH) (he : p.2 = e.1) (i : Fin (internal p.1 e)) :
    mem ((A.fieldAddress Y (promotedSites p) node false (refreshSlots hd (.inr (.inl e.2))) +
      i.val : ℕ) : BurstRAM.Word w) =
      PrimedInputRAM.encodeBit w (MotifEntry.inputBits ((supplyArg X p P hD hd internal z).1 e he) i) := by
  rcases p with ⟨s,j⟩
  rcases e with ⟨j',t⟩
  change j = j' at he
  subst j'
  let I := newIso X P hD hd internal
  let edge : OutputEdge (X.Base × BitWord l) (Fin (2^a) × Fin dH) (2^a) (2^b-(dH+1)) :=
    .inr (.inl (s,j,t))
  let val := z.1 (I.edge edge) rfl
  let arg := (supplyArg X (s,j) P hD hd internal z).1 (j,t) rfl
  have e := internal_payload X P hD hd internal s (j,t) arg
  exact read_word rep false _ _ ((congrArg List.ofFn ((I.payload edge).apply_symm_apply val)).symm.trans e) i

theorem supply_in_read (A : Arena) (node : ℕ) (z : (Y).network.Half (promotedSites p))
    (mem : BurstRAM.Word w → BurstRAM.Word w) (rep : NodeFields A node Y _ z mem)
    (e : Fin (2^a) × Fin dH) (he : p.2 = (P.target e).1) (i : Fin (internal p.1 e)) :
    mem ((A.fieldAddress Y (promotedSites p) node true (refreshSlots hd (.inr (.inl (P.target e).2))) +
      i.val : ℕ) : BurstRAM.Word w) =
      PrimedInputRAM.encodeBit w (MotifEntry.inputBits ((supplyArg X p P hD hd internal z).2 e he) i) := by
  let I := newIso X P hD hd internal
  let edge : OutputEdge (X.Base × BitWord l) (Fin (2^a) × Fin dH) (2^a) (2^b-(dH+1)) :=
    .inr (.inl (p.1,e))
  have hat : p = (p.1,(P.target e).1) := Prod.ext rfl he
  have hh : promotedSites p = (Y).network.dst (I.edge edge) :=
    (congrArg I.site hat).trans (I.dst edge)
  let val := z.2 (I.edge edge) hh
  let arg := (supplyArg X p P hD hd internal z).2 e he
  have hp := internal_payload X P hD hd internal p.1 e arg
  have ev : List.ofFn val = List.ofFn (MotifEntry.inputBits arg) :=
    (congrArg List.ofFn ((I.payload edge).apply_symm_apply val)).symm.trans hp
  let slot := refreshSlots hd (.inr (.inl (P.target e).2))
  have eqEdge : ((incomingOrder Y (promotedSites p)).entries slot).val = I.edge edge := by
    change (degreeRefresh G P hD hd).actualGraph.target.symm (promotedSites p,slot) = _
    apply (degreeRefresh G P hD hd).actualGraph.target.injective
    rw [Equiv.apply_symm_apply]
    change (promotedSites p,slot) = (degreeRefresh G P hD hd).actualGraph.target
      (((p.1.1,e.1),p.1.2),refreshSlots hd (.inr (.inl e.2)))
    rw [degreeRefresh_internal]
    exact Prod.ext (congrArg promotedSites hat) rfl
  exact read_word rep true slot _ ((incoming_congr z eqEdge _ hh).trans ev) i

/-- Builds the selected port's demand input from the incoming half-wire assignment and the
external segments of the refreshed assignment. -/
noncomputable abbrev demandArg (old : X.network.Half (oldSite X p))
    (new : (newState X P hD hd internal).network.Half (promotedSites p)) :=
  portInput (R := ℤ) (matchOld) widths p.1 p.2 (oldHalf X p old)
    (segments X p P hD hd internal new)

/-- The offset of port j's segment in the site's incoming or outgoing external bundle,
according to the direction bit. -/
def externalOffset (dir : Bool) (j : Fin (2^a)) : ℕ :=
  if dir then (PortRefresh.incomingRecord G port (splitWidths X) (p,j)).offset
  else (PortRefresh.outgoingRecord G port (splitWidths X) (p,j)).offset

/-- Every endpoint has its own physical operand pointer. The old half of a
tie uses its destination slot. The new external half uses its source port as
the segment index. Incoming expander halves use the reverse edge's port. -/
noncomputable def operandBase (A : Arena) (oldNode newNode : ℕ) :
    MapLookup.LabelField (Tie (2^a)) (Fin (2^a) × Fin dH) → ℕ
  | .inl (false,e) => A.fieldAddress X (oldSite X p) oldNode (!e.1) (tieTarget e)
  | .inl (true,e) => A.fieldAddress Y (promotedSites p) newNode (!e.1) (refreshSlots hd (.inl 0))
      + externalOffset X p (!e.1) (tieSource e)
  | .inr (false,e) => A.fieldAddress Y (promotedSites p) newNode false (refreshSlots hd (.inr (.inl e.2)))
  | .inr (true,e) => A.fieldAddress Y (promotedSites p) newNode true
      (refreshSlots hd (.inr (.inl (P.target e).2)))

variable (A : Arena) (oldNode newNode : ℕ)
  (old : X.network.Half (oldSite X p)) (new : (newState X P hD hd internal).network.Half (promotedSites p))
  (mem : BurstRAM.Word w → BurstRAM.Word w)
  (oldData : NodeFields A oldNode X (oldSite X p) old mem)
  (newData : NodeFields A newNode (newState X P hD hd internal) (promotedSites p) new mem)

local notation "dArg" => demandArg X p P hD hd internal old new
local notation "base" => operandBase X p P hD hd internal A oldNode newNode

private theorem encoded {n : ℕ} (x : Word n) (i : Fin n) :
    PrimedInputRAM.encodeBit w (x i) = PrimedInputRAM.encodeBit w (MotifEntry.inputBits (wordIndex n x) i) :=
  congrArg _ (congrFun (inputBits_wordIndex x).symm i)

include oldData in
theorem demand_out_read (e : Tie (2^a)) (he : p.2 = tieSource e)
    (i : Fin (internalWidth (matchOld) widths p.1 e)) :
    mem ((base (.inl (false,e))+i.val : ℕ) : BurstRAM.Word w) =
      PrimedInputRAM.encodeBit w (MotifEntry.inputBits ((dArg).1 e he) i) := by
  rcases p with ⟨s,j⟩
  rcases e with ⟨dir,⟨⟨source,target⟩,ne⟩⟩
  change j = source at he
  subst source
  cases dir
  · exact (old_in_read X (s,j) A oldNode old mem oldData target i).trans (encoded _ i)
  · exact (old_out_read X (s,j) A oldNode old mem oldData target i).trans (encoded _ i)

include newData in
theorem demand_in_read (e : Tie (2^a)) (he : p.2 = tieTarget e)
    (i : Fin (internalWidth (matchOld) widths p.1 e)) :
    mem ((base (.inl (true,e))+i.val : ℕ) : BurstRAM.Word w) =
      PrimedInputRAM.encodeBit w (MotifEntry.inputBits ((dArg).2 e he) i) := by
  rcases p with ⟨s,j⟩
  rcases e with ⟨dir,⟨⟨source,target⟩,ne⟩⟩
  change j = target at he
  subst target
  cases dir
  · exact (external_in_read X (s,j) P hD hd internal A newNode new mem newData source i).trans (encoded _ i)
  · exact (external_out_read X (s,j) P hD hd internal A newNode new mem newData source i).trans (encoded _ i)

end CompressorRecords.RefreshMapOperands

namespace CompressorRecords.RefreshMapOperands

open Compression Compression.Refresh Compression.DegreeRefresh PairSimulation PairSimulation.NodeArguments
open PairSimulation.LocalHistory MapLookup MotifSelector MotifEntry MotifConversion MapPortAgreement
open scoped Fin.CommRing

private def AtSlice {w : ℕ} (mem : BurstRAM.Word w → BurstRAM.Word w) (addr : ℕ)
    (s : (n : ℕ) × (Fin n → Bool)) : Prop :=
  ∀ i : Fin s.1, mem ((addr+i.val : ℕ) : BurstRAM.Word w) = PrimedInputRAM.encodeBit w (s.2 i)

private theorem at_endpoint {I J : Type} [DecidableEq J] {w : ℕ}
    (mem : BurstRAM.Word w → BurstRAM.Word w) (addr : Bool × I → ℕ) (src dst : I → J)
    (party : J) (len : I → ℕ) (bits : DemandBits src dst len party)
    (out : ∀ (e : I) h (i : Fin (len e)), mem ((addr (false,e)+i.val : ℕ) : BurstRAM.Word w) = PrimedInputRAM.encodeBit w (bits.1 e h i))
    (inc : ∀ (e : I) h (i : Fin (len e)), mem ((addr (true,e)+i.val : ℕ) : BurstRAM.Word w) = PrimedInputRAM.encodeBit w (bits.2 e h i))
    (f : Bool × I) : AtSlice mem (addr f) (MapRow.endpoint src dst party len bits f) := by
  rcases f with ⟨dir,e⟩
  cases dir <;> rw [MapRow.endpoint]
  · split
    · exact out _ _
    · intro i; exact i.elim0
  · split
    · exact inc _ _
    · intro i; exact i.elim0

section Selected
set_option maxHeartbeats 1000000

variable {k : Type} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates) {g w : ℕ}
variable (X : State S.portExponent (S.portExponent+g))
variable (choice : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _)
  (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh)

local notation "P" => S.graph.toSlotGraph
local notation "hD" => S.port_order
local notation "hd" => And.right S.degree_bounds
local notation "internal" => blockSupplyWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X)
  S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh choice
local notation "Y" => dyadicRefreshNext X S.graph (Nat.two_pow_pos _)
  (And.left (S.port_bound.connected_and_pos S.port_order)) B.refresh hD hd choice

variable (p : (X.Base × BitWord g) × Fin (2^S.portExponent))
  (old : X.network.Half (oldSite X p))
  (new : (dyadicRefreshNext X S.graph (Nat.two_pow_pos _) (And.left (S.port_bound.connected_and_pos S.port_order))
    B.refresh S.port_order S.degree_bounds.2 choice).network.Half (promotedSites p))

/-- The exact input of the single motif map at the refreshed port, from the
independent old and new node halves. -/
noncomputable def entryInput : EntryInput B.refresh :=
  ⟨blockDemandWidths (splitSlots X) (bitWordFinEquiv _) (splitWidths X) p.1,
    (choice p.1).val, p.2, demandArg X p P hD hd internal old new,
    supplyArg X p P hD hd internal new⟩

theorem recorded_call {R : Type*} [CommRing R] (f : B.Entry → R) (hf : B.IsSolution f) :
    let I := entryInput B X choice p old new
    recordedRefreshCall B X f hf choice (promotedSites p) 0 I.demandBits I.supplyBits =
      .refresh I le_rfl := by
  simp [recordedRefreshCall, entryInput]
  rfl

variable (A : Arena) (oldNode newNode : ℕ)

/-- The resident row buffer of the selected refresh invocation. Its supply
ranges stop at the payload ends while the full words (including their tag
suffixes) are separately available at the same bases. -/
noncomputable abbrev buffers (z : B.refresh.grid.demands)
    (θ : Fin (repetitions B.refresh (entryInput B X choice p old new).demand) → Selector B.refresh) (n : ℕ) :=
  let I := entryInput B X choice p old new
  MapRowLoop.buffers B.refresh z p.2 I.demand I.payload
    (MotifEntry.demandBits tieSource tieTarget p.2 I.demandBits)
    (mapHalf S.portSupply (fun _ ↦ MotifEntry.inputBits) I.supplyBits)
    (operandBase X p P hD hd internal A oldNode newNode) θ n

/-- Each present demand and supply bit in the actual interpreter is recovered
from its physical node address. A nonincident endpoint has no readable bit. -/
theorem operandData (z : B.refresh.grid.demands)
    (θ : Fin (repetitions B.refresh (entryInput B X choice p old new).demand) → Selector B.refresh)
    (n : ℕ) (mem : BurstRAM.Word w → BurstRAM.Word w)
    (oldData : NodeFields A oldNode X (oldSite X p) old mem)
    (newData : NodeFields A newNode Y (promotedSites p) new mem) :
    let x := buffers B X choice p old new A oldNode newNode z θ n
    ∀ f (i : Fin (x.len f)), mem ((x.base f+i.val : ℕ) : BurstRAM.Word w) =
      PrimedInputRAM.encodeBit w (x.bits f i) := by
  intro x f
  let addr := operandBase X p P hD hd internal A oldNode newNode
  let I := entryInput B X choice p old new
  cases f with
  | inl h =>
    apply at_endpoint mem (addr ∘ Sum.inl) tieSource tieTarget p.2 I.demand
      (MotifEntry.demandBits tieSource tieTarget p.2 I.demandBits) _ _ h
    · exact demand_out_read X p P hD hd internal A oldNode newNode old new mem oldData
    · exact demand_in_read X p P hD hd internal A oldNode newNode old new mem newData
  | inr h =>
    apply at_endpoint mem (addr ∘ Sum.inr) S.portSupply.src S.portSupply.dst p.2 I.payload
      (mapHalf S.portSupply (fun _ ↦ payloadBits)
        (mapHalf S.portSupply (fun _ ↦ MotifEntry.inputBits) I.supplyBits)) _ _ h
    · intro e he i
      exact supply_out_read X p P hD hd internal A newNode new mem newData e he
        (Fin.castLE (Nat.le_add_right _ _) i)
    · intro e he i
      exact supply_in_read X p P hD hd internal A newNode new mem newData e he
        (Fin.castLE (Nat.le_add_right _ _) i)

/-- Full supply fields include selector bits above the payload. The pointers
used by the agreement scan refer to the same two physical halves used by
the map row, including different slot ordinals at opposite endpoints. -/
noncomputable def supplyPortBase (t : Port S.portSupply p.2) : BurstRAM.Word w :=
  let addr := operandBase X p P hD hd internal A oldNode newNode
  match t with
  | .inl e => (addr (.inr (false,e.val)) : BurstRAM.Word w)
  | .inr e => (addr (.inr (true,e.val)) : BurstRAM.Word w)

theorem selectorCells (mem : BurstRAM.Word w → BurstRAM.Word w)
    (newData : NodeFields A newNode Y (promotedSites p) new mem) :
    let I := entryInput B X choice p old new
    let full := mapHalf S.portSupply (fun _ ↦ MotifEntry.inputBits) I.supplyBits
    ∀ (t : Port S.portSupply p.2) (i : Fin (I.payload (MapResidentAgreement.edge t) +
        repetitions B.refresh I.demand * B.refresh.selectorBits)),
      mem (supplyPortBase B X choice p A oldNode newNode t + (i.val : BurstRAM.Word w)) =
        PrimedInputRAM.encodeBit w (MapResidentAgreement.field full t i) := by
  intro I full t i
  rcases t with ⟨e,h⟩ | ⟨e,h⟩
  · have v := supply_out_read X p P hD hd internal A newNode new mem newData e h i
    rw [Nat.cast_add] at v
    exact v
  · have v := supply_in_read X p P hD hd internal A newNode new mem newData e h i
    rw [Nat.cast_add] at v
    exact v

end Selected

end CompressorRecords.RefreshMapOperands

end VPVNP
end Computability
end OAI
