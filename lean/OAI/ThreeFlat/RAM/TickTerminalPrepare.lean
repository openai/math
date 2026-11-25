import OAI.ThreeFlat.RAM.TickTerminalRootGeometry
import OAI.ThreeFlat.RAM.TickTerminalForest
import OAI.ThreeFlat.RAM.TickTerminalRoot
import OAI.ThreeFlat.RAM.TickTerminalRecords
import OAI.ThreeFlat.RAM.TracePrototypeBoot
import OAI.ThreeFlat.RAM.TickRootScanInit
import OAI.ThreeFlat.RAM.HistoryStageBody
import OAI.ThreeFlat.RAM.HistoryStageResources

namespace OAI
/-! # The selected-history preparation procedure in the real tick operand banks -/

noncomputable section
namespace ThreeFlat.RAM.TickTerminalRoot

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure Diagonal.TickWorkspace
open HistoryStageBody.Physical
open scoped Fin.CommRing

def rootLookup (u : ℕ) : TickRootScanInit.Layout := ⟨base u 1,base u 6,base u 17,base u 18⟩

def finish {F : Type*} [Field F] [Fintype F] {W : ℕ} (code : FieldCode F W)
    (u p H J wireStart wirePrefix : ℕ) : Procedure W :=
  let a := mounted u p wireStart wirePrefix
  let scan := TickRootScanInit.procedure W (rootLookup u)
  let pad := TickTerminalPadding.procedure code a.control (base u 18+48) a.metadata (base u 10) p H J
  (scan.seq (many W a)).seq pad

/-- The whole selected slot procedure follows the real interior stage generator with a native
scan of S6's owner table, source-address translation, and fixed field LUT/padding. -/
def prepare {F : Type*} [Field F] [Fintype F] {W : ℕ} (code : FieldCode F W)
    (u p H J wireStart wirePrefix : ℕ) (archive : Archive) (shape : TraceBucketAtom.Layout)
    (pub : Fin TraceEndpointROM.params→Word W) (families : List Family) (startup : TracePrototypeBoot.Args W) : Procedure W :=
  ((startup.procedure u).seq (selected W u archive shape pub families)).seq (finish code u p H J wireStart wirePrefix)

open Diagonal.HistoryTerminalJoin Diagonal.TraceCircuit BitLayout Contraction

/-- Physical root lookup uses the actual root count in S6 and the [group,slot] rows
published in the second subarray of S11. -/
def directoryInput {W : ℕ} (u : ℕ) (head : TickPhysicalABI.NavigationHeader)
    (own : TickSlotLookup.Owner W) (m : Memory W) :=
  head.stored u m ∧ ∀ j<head.roots,m (TickPhysicalABI.directory u 1+2*j)=(own j).1 ∧
    m (TickPhysicalABI.directory u 1+2*j+1)=(own j).2

def rootIds {W : ℕ} (u : ℕ) (head : TickPhysicalABI.NavigationHeader)
    (own : TickSlotLookup.Owner W) (m : Memory W) :=
  TickRootScanInit.chosen (rootLookup u) own head.roots m

def rootStart {W : ℕ} (u : ℕ) (head : TickPhysicalABI.NavigationHeader)
    (own : TickSlotLookup.Owner W) (m : Memory W) :=
  TickRootScanInit.output (rootLookup u) (rootIds u head own m) m

theorem rootStart_spec (u : ℕ) (age : 1≤u) (space : 52≤ stride u)
    (head : TickPhysicalABI.NavigationHeader) (own : TickSlotLookup.Owner (16*u^10))
    (ownerSpace : 2*head.roots≤ stride u/4) :
    (TickRootScanInit.procedure (16*u^10) (rootLookup u)).Spec (directoryInput u head own)
      (fun m o=>o=rootStart u head own m) (24+11*head.roots) := by
  have addr (s : ℕ) (hs : s<52) := word_space (i:=s) age (by omega)
  have roots : head.roots≤ stride u := by omega
  have endOwners : TickPhysicalABI.directory u 1+2*head.roots≤base u 11+stride u := by
    change base u 11+1*(stride u/4)+2*head.roots≤base u 11+stride u
    omega
  have disjoint := apart (u:=u) (by decide : 11<17)
  intro p regs words machine
  refine Procedure.Spec.mono (A:=TickRootScanInit.procedure (16*u^10) (rootLookup u))
    (pre':=directoryInput u head own)
    (TickRootScanInit.procedure_spec (rootLookup u) own head.roots (TickPhysicalABI.directory u 1)
      (by change base u 1+3<_; have := addr 1 (by decide); omega)
      (by change base u 6+4<_; have := addr 6 (by decide); omega)
      (by change base u 18+4<_; have := addr 18 (by decide); omega)
      (by have := addr 17 (by decide); omega)
      (endOwners.trans_lt (addr 11 (by decide)))
      (by change base u 17+head.roots<_; have := addr 17 (by decide); omega)
      (Or.inr (endOwners.trans disjoint))) ?_ (fun _ _ h=>h) le_rfl machine
  rintro m ⟨header,owners⟩
  exact ⟨header 1,header 4,owners⟩

theorem rootStart_count (u : ℕ) (age : 1≤u) (space : 52≤ stride u)
    (head : TickPhysicalABI.NavigationHeader) (own : TickSlotLookup.Owner (16*u^10))
    (ownerSpace : 2*head.roots≤ stride u/4) (m : Memory (16*u^10)) (p wireStart wirePrefix : ℕ) :
    ((rootStart u head own m) (countdown (W:=16*u^10) (mounted u p wireStart wirePrefix)).val).val=
      (rootIds u head own m).length := by
  let ids := rootIds u head own m
  have short : ids.length≤head.roots := (List.length_filter_le ..).trans_eq (List.length_range ..)
  have bound := word_space (i:=18) age (by omega)
  have eq := (TickRootScanInit.output_controls (rootLookup u) ids m).2.2.2.2
  change ((rootStart u head own m) ((base u 18+4:ℕ):Word (16*u^10)).val).val=ids.length
  rw [Fin.val_cast_of_lt (by omega),show rootStart u head own m (base u 18+4)=(ids.length:Word _) from eq,
    Fin.val_cast_of_lt (by omega)]

/-- The padding bank, four-word header, input cells and shared table bank fit in the
actual S9/S10/S18 partition. This uses only total allocation and native word size. -/
theorem pad_mounted {F : Type*} [Field F] [Fintype F] {u p H J : ℕ}
    (N : BitNetwork F p) (pin : Fin p→Bool) (fit : Fits (TickWeightedBank.shape F p H J) (16*u^10))
    (age : 1≤u) (space : 52≤ stride u) (capBits : N.internal≤H) (capRows : N.cells+(H-N.internal)≤J)
    (low : cellsBase p H≤ stride u) (rows : 4*J≤ stride u)
    (tables : 8*(TickTerminalPadding.tables F+2)≤ stride u) :
    let b := H-N.internal
    let v := J-(N.cells+b)
    let code := codec (TickWeightedBank.shape F p H J) fit
    (TickTerminalPadding.procedure code (base u 18) (base u 18+48) (base u 9) (base u 10) p H J).Spec
      (TickTerminalPadding.recorded (H:=H) N pin (base u 18) (base u 9))
      (fun _ out=>TickWeightedBank.Ready fit (addPadding N b v) ((HistoryCompiledRows.library N).padded b v)
        pin (base u 9) (base u 10) out) (TickTerminalPadding.budget F b v) := by
  intro b v code programs registers slots machine
  have room := word_space (i:=18) age (by omega)
  exact TickTerminalPadding.ready N pin fit (base u 18) (base u 18+48) (base u 9) (base u 10) capBits capRows
    (low.trans (lower u 9)) (by have := apart (u:=u) (by decide : 9<10); omega)
    (by have := apart (u:=u) (by decide : 10<18); omega) (by omega) (by omega) (Or.inl (by omega)) machine


end ThreeFlat.RAM.TickTerminalRoot


namespace ThreeFlat.RAM.TickTerminalRoot

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure Diagonal.TickWorkspace Diagonal
open HistoryStageBody.Physical Diagonal.HistoryTerminalJoin Diagonal.TraceCircuit BitLayout Contraction
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] {u p H J n : ℕ} {arity : Fin n→ℕ}
variable (N : ∀ i,BitNetwork F (arity i)) (pins : ∀ i,Fin (arity i)→Fin p) (pin : Fin p→Bool)
variable (wireStart wirePrefix : ℕ)

local notation "W" => 16*u^10
local notation "A" => mounted u p wireStart wirePrefix
local notation "G" => TickSlotForest.network (projected N pins)
local notation "b" => H - BitNetwork.internal G
local notation "v" => J - (BitNetwork.cells G + b)

def finishCost (head : TickPhysicalABI.NavigationHeader) (own : TickSlotLookup.Owner W) (m : Memory W) :=
  let init := rootStart u head own m
  (24+11*head.roots)+(4+7*n+∑ j ∈ Finset.range n,iterationCost A init (n-(j+1)))+
    TickTerminalPadding.budget F b v

/-- The frame at the boundary between selected interior production and terminal row
concatenation consists of the compact directory and local typed streams. -/
def terminalInput (head : TickPhysicalABI.NavigationHeader) (own : TickSlotLookup.Owner W)
    (allowance : ℕ) (m : Memory W) :=
  directoryInput u head own m ∧
  Nonempty (ForestRows A N pins pin H (rootStart u head own m)) ∧
  finishCost (H:=H) (J:=J) N pins wireStart wirePrefix head own m≤allowance

variable (fit : Fits (TickWeightedBank.shape F p H J) (16*u^10))
local notation "field" => codec (TickWeightedBank.shape F p H J) fit

theorem finish_spec (head : TickPhysicalABI.NavigationHeader) (own : TickSlotLookup.Owner W)
    (allowance : ℕ) (age : 1≤u) (space : 52≤ stride u) (ownerSpace : 2*head.roots≤ stride u/4)
    (hidden : (G).internal≤H) (room : (G).cells+(H-(G).internal)≤J) (low : cellsBase p H≤ stride u)
    (storage : 4*J≤ stride u) (lut : 8*(TickTerminalPadding.tables F+2)≤ stride u) :
    (finish field u p H J wireStart wirePrefix).Spec
      (terminalInput (H:=H) (J:=J) N pins pin wireStart wirePrefix head own allowance)
      (fun _ out=>TickWeightedBank.Ready fit (addPadding G b v) ((HistoryCompiledRows.library G).padded b v)
        pin (base u 9) (base u 10) out) allowance := by
  intro P R K M pc reg pub exit installed data cfg m entry h
  obtain ⟨nav,⟨chart⟩,time⟩ := h
  let init := rootStart u head own m
  let scan := TickRootScanInit.procedure W (rootLookup u)
  let pad := TickTerminalPadding.procedure field (base u 18) (base u 18+48)
    (base u 9) (base u 10) p H J
  have s₀ : scan.Spec (fun μ => μ = m) (fun _ out => out = init) (24+11*head.roots) :=
    Procedure.Spec.atMemory («A»:=scan) (rootStart_spec u age space head own ownerSpace) m nav
  have input := forest_countdown A N pins pin init chart
  have first : (scan.seq (many W A)).Spec (fun μ => μ = m) _ _ :=
    Procedure.Spec.seq («A»:=scan) (B:=many W A) s₀
      (many_spec A init n input.1 (forest_bounds A N pins pin init chart) input.2)
      (fun _ _ h => h)
  have all : ((scan.seq (many W A)).seq pad).Spec (fun μ => μ = m) _ _ :=
    Procedure.Spec.seq («A»:=scan.seq (many W A)) (B:=pad) first
      (pad_mounted G pin fit age space hidden room low storage lut) (by
        rintro _ _ ⟨_, _, rfl⟩
        exact forest_recorded A N pins pin init chart)
  exact Procedure.Spec.mono («A»:=finish field u p H J wireStart wirePrefix)
    (pre':=fun μ => μ = m) all (fun _ h => h) (fun _ _ h => h.choose_spec.2)
    time M pc reg pub exit installed data cfg m entry rfl

/-- The concrete selected-node code can discharge the remaining preparation interface by
publishing its S12 record streams and S13 headers. All terminal work, including padding
and actual coefficient ROM initialization, is executed by the procedure. -/
theorem prepare_compiled (head : TickPhysicalABI.NavigationHeader) (own : TickSlotLookup.Owner W)
    (archive : Archive) (shape : TraceBucketAtom.Layout) (publicWords : Fin TraceEndpointROM.params→Word W)
    (families : List Family) (startup : TracePrototypeBoot.Args W) (pre : Memory W→Prop) (inside tail : ℕ)
    (generated : ((startup.procedure u).seq (selected W u archive shape publicWords families)).Spec pre
      (fun _ m=>terminalInput (H:=H) (J:=J) N pins pin wireStart wirePrefix head own tail m) inside)
    (age : 1≤u) (space : 52≤ stride u) (ownerSpace : 2*head.roots≤ stride u/4)
    (hidden : (G).internal≤H) (room : (G).cells+(H-(G).internal)≤J) (low : cellsBase p H≤ stride u)
    (storage : 4*J≤ stride u) (lut : 8*(TickTerminalPadding.tables F+2)≤ stride u) :
    let actual := prepare field u p H J wireStart wirePrefix archive shape publicWords families startup
    TickStageSpec.Prepare actual.block actual.publicData pre
      (fun _ out=>TickWeightedBank.Ready fit (addPadding G b v) ((HistoryCompiledRows.library G).padded b v)
        pin (base u 9) (base u 10) out) (inside+tail) := by
  intro actual
  apply TickStageSpec.prepare_of_spec actual
  refine Procedure.Spec.mono («A»:=actual) (Procedure.Spec.seq
    («A»:=(startup.procedure u).seq (selected W u archive shape publicWords families))
    (B:=finish field u p H J wireStart wirePrefix) generated
    (finish_spec N pins pin wireStart wirePrefix fit head own tail age space ownerSpace hidden room
      low storage lut) (fun _ _ h => h)) (fun _ h => h) (fun _ _ h => h.choose_spec.2) le_rfl


end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.RAM.TickTerminalRoot

open Computability.VPVNP.BurstRAM PrivateRAM HistoryTerminalTape
open Diagonal.TickWorkspace

/-- An immutable read interval is below the first mutable root bank or above the last one.
Both S11–13 compact data and S38–51 navigation/archive data obey this separation. -/
def ImmutableBank (u start count : ℕ) := (start+count≤base u 14 ∨ base u 18+stride u≤ start) ∧
  start+count≤2^(16*u^10)

/-- Sizes and pointer ranges of one selected compact root. These are the locations of its
directory entries, generated rows and per-port offsets in the actual S9/S12–18 banks. -/
structure CompactRoot {u : ℕ} (p wireStart wirePrefix : ℕ) (m : Memory (16*u^10)) : Prop where
  space : 65≤ stride u
  publicWords : p<2^(16*u^10) ∧ wireStart<2^(16*u^10) ∧ wirePrefix<2^(16*u^10)
  selected : natMemory m (base u 18)<stride u
  resultWords : let A:=mounted u p wireStart wirePrefix
    A.results+8*rootId A (natMemory m)+6≤A.seed
  halfPointer : let A:=mounted u p wireStart wirePrefix
    ImmutableBank u (natMemory m (A.rootHeader+1)+8*rootId A (natMemory m)+6) 1
  halfHeader : let A:=mounted u p wireStart wirePrefix
    ImmutableBank u (natMemory m (natMemory m (A.rootHeader+1)+8*rootId A (natMemory m)+6)) 2
  halfData : let T:=terminal (mounted u p wireStart wirePrefix) (natMemory m)
    ImmutableBank u T.halfData (4*T.halves)
  «prefix» : let T:=terminal (mounted u p wireStart wirePrefix) (natMemory m)
    ∀ i<T.halves,ImmutableBank u (wirePrefix+(HistoryTerminalTape.half T (natMemory m) i).edge) 1
  tableWords : let T:=terminal (mounted u p wireStart wirePrefix) (natMemory m)
    7*(T.halves+2)≤ stride u
  mapWords : let T:=terminal (mounted u p wireStart wirePrefix) (natMemory m)
    64+T.localPins≤ stride u
  span : PinSpan (terminal (mounted u p wireStart wirePrefix) (natMemory m)) (natMemory m)
  endpoints : let T:=terminal (mounted u p wireStart wirePrefix) (natMemory m)
    T.endpoints+T.ext≤base u 14
  metadata : let T:=terminal (mounted u p wireStart wirePrefix) (natMemory m)
    T.meta+4*T.rows≤base u 9+stride u
  stream : let T:=terminal (mounted u p wireStart wirePrefix) (natMemory m)
    base u 10≤T.stream ∧ T.stream+4*T.rows≤base u 14

theorem mounted_root_bounds {u p wireStart wirePrefix : ℕ} (age : 1≤u)
    (m : Memory (16*u^10)) (compact : CompactRoot p wireStart wirePrefix m) :
    RootBounds (mounted u p wireStart wirePrefix) m := by
  have room : base u 18+stride u<2^(16*u^10) :=
    word_space age (show 18<stride u by have := compact.space; omega)
  apply CompactRootAt.bounds room
  refine ⟨compact.space, compact.publicWords, compact.selected, compact.resultWords,
    compact.halfPointer, compact.halfHeader, ?_, compact.prefix, compact.tableWords,
    compact.mapWords, compact.span, compact.endpoints, compact.metadata, compact.stream⟩
  let T:=terminal (mounted u p wireStart wirePrefix) (natMemory m)
  change ∀ j<4*T.halves,ImmutableBankAt _ u (T.halfData+j) 1
  intro j hj
  have allWords : ImmutableBank u T.halfData (4*T.halves) := compact.halfData
  obtain ⟨sep,cap⟩:=allWords
  dsimp only [ImmutableBankAt]
  rcases sep with low|high
  · exact ⟨Or.inl (by omega),by omega⟩
  · exact ⟨Or.inr (by omega),by omega⟩


end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.RAM.TickTerminalRoot

open Computability.VPVNP.BurstRAM PrivateRAM PhysicalProcedure

def finishLabels (F : Type*) [Fintype F] :=
  34+rootLabels+((SelectedPadHeader.program 1 0 0 0 0 0 0).labels+
    (TickPaddedROM.labels (TickTerminalPadding.tables F+2)+96))
def finishRegisters (F : Type*) [Fintype F] :=
  9+rootRegisters+((SelectedPadHeader.program 1 0 0 0 0 0 0).registers+
    max (4+TickPaddedROM.binds (TickTerminalPadding.tables F+2)) 33)
def finishSlots := 0+rootSlots+(0+1)

open private SelectedPadHeader.term SelectedPadHeader.col from
  OAI.ThreeFlat.RAM.SelectedPadHeader

private theorem header_binds (w ctl pad metaBase p H tag : ℕ) :
    (SelectedPadHeader.term (w:=w) ctl pad metaBase p H tag).binds=26 := by
  rw [SelectedPadHeader.term,DescriptorExpr.Term.binds_instantiate,Fin.sum_univ_one]
  simp [LiteralTable.dispatch,SelectedPadHeader.col,DescriptorExpr.Term.select,
    DescriptorExpr.Term.binary,DescriptorExpr.Term.load,DescriptorExpr.Term.literal,
    DescriptorExpr.Term.binds_letThen,DescriptorExpr.Term.binds_rename,DescriptorExpr.Term.binds]

set_option maxRecDepth 8192 in
set_option maxHeartbeats 1000000 in
theorem finish_shape {F : Type*} [Field F] [Fintype F] {W : ℕ} (field : FieldCode F W)
    (u p H J wireStart wirePrefix : ℕ) :
    let actual := finish field u p H J wireStart wirePrefix
    actual.labels=finishLabels F ∧ actual.registers=finishRegisters F ∧ actual.slots=finishSlots := by
  let A := mounted u p wireStart wirePrefix
  let h := many_shape W A
  let hdr := SelectedPadHeader.program W A.control (Diagonal.TickWorkspace.base u 18+48) A.metadata p H
    (TickTerminalPadding.tables F)
  have header : hdr.labels=(SelectedPadHeader.program 1 0 0 0 0 0 0).labels ∧
      hdr.registers=(SelectedPadHeader.program 1 0 0 0 0 0 0).registers := by
    simp only [hdr,SelectedPadHeader.program,PhysicalInputPhases.writing,
      DescriptorExpr.Term.labels_eq,header_binds,and_self]
  intro actual
  change 34+(many W A).labels+(hdr.labels+_)=_ ∧
    9+(many W A).registers+(hdr.registers+_)=_ ∧ 0+(many W A).slots+(0+1)=_
  rw [h.1,h.2.1,h.2.2,header.1,header.2]
  exact ⟨rfl,rfl,rfl⟩


end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.RAM.TickTerminalRoot

open Computability.VPVNP.BurstRAM HistoryTerminalTape Diagonal Diagonal.HistoryTerminalJoin
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] {u p H J n : ℕ} {arity : Fin n→ℕ}

omit [Field F] in
/-- The scheduled terminal work pays exactly one count per visit, one count per incident
half, and one count per actually written local pin or trivalent character. -/
theorem finishCost_le (N : ∀ i,BitNetwork F (arity i)) (pins : ∀ i,Fin (arity i)→Fin p)
    (wireStart wirePrefix : ℕ) (head : TickPhysicalABI.NavigationHeader) (own : TickSlotLookup.Owner (16*u^10))
    (m : Memory (16*u^10)) (charge : ℕ→ℕ) (selected : ℕ)
    (perRoot : ∀ i<n,let A := mounted u p wireStart wirePrefix
      let init := rootStart u head own m
      let raw := natMemory (decrease A (images A init i))
      let T := terminal A raw
      1+T.halves+TickTerminalPrimitive.words T raw≤charge i)
    (assigned : ∑ j ∈ Finset.range n,charge j≤ selected) :
    let G := TickSlotForest.network (projected N pins)
    let b := H-G.internal
    let q := J-(G.cells+b)
    finishCost (H:=H) (J:=J) N pins wireStart wirePrefix head own m≤
      28+11*head.roots+7*n+rootFactor*selected+TickTerminalPadding.budget F b q := by
  intro G b q
  let A := mounted u p wireStart wirePrefix
  let init := rootStart u head own m
  have each (j : ℕ) (hj : j<n) : iterationCost A init j≤rootFactor*charge j :=
    (work_bound _ A _ _).trans (Nat.mul_le_mul_left _ (perRoot j hj))
  have reflection : (∑ j ∈ Finset.range n,iterationCost A init (n-(j+1)))=
      ∑ j ∈ Finset.range n,iterationCost A init j := by
    simpa only [Nat.sub_sub,Nat.add_comm] using Finset.sum_range_reflect (iterationCost A init) n
  have total : (∑ j ∈ Finset.range n,iterationCost A init j)≤rootFactor*selected :=
    calc
      _ ≤ ∑ j ∈ Finset.range n,rootFactor*charge j := Finset.sum_le_sum fun j h=>each j (Finset.mem_range.mp h)
      _ = rootFactor*(∑ j ∈ Finset.range n,charge j) := (Finset.mul_sum ..).symm
      _ ≤ _ := Nat.mul_le_mul_left _ assigned
  change (24+11*head.roots)+(4+7*n+∑ j ∈ Finset.range n,iterationCost A init (n-(j+1)))+
    TickTerminalPadding.budget F b q≤_
  rw [reflection]
  omega


end ThreeFlat.RAM.TickTerminalRoot



namespace ThreeFlat.RAM.TickTerminalRoot

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickWorkspace HistoryCompiledRows HistoryTerminalTape
open scoped BigOperators Fin.CommRing

/-- S10–13 retain the local records, endpoints and root-header directory. S17 retains
the selected id list. The chronological node, half-incidence and final width arrays live
in the upper immutable archive. -/
def immutable (u z : ℕ) :=
  (base u 10≤z ∧ z<base u 14) ∨ (base u 17≤z ∧ z<base u 18) ∨ base u 18+stride u≤z

variable {F : Type*} [Field F] [Fintype F] {u p n : ℕ} {arity : Fin n→ℕ}
variable (N : ∀ i,BitNetwork F (arity i)) (pins : ∀ i,Fin (arity i)→Fin p)
variable (wireStart wirePrefix : ℕ)
local notation "W" => 16*u^10
local notation "A" => mounted u p wireStart wirePrefix

omit [Field F] in
/-- The genuine directory and input streams suffice for a forest-root witness. All
scratch exclusion and padding bounds follow from their physical regions. -/
theorem physical_root (i : Fin n) (m : Memory W) (age : 1≤u)
    (chart : CompactRoot p wireStart wirePrefix m)
    (port : (terminal A (natMemory m)).localPins=arity i)
    (rows : (terminal A (natMemory m)).rows=(N i).cells)
    (bits : (HistoryStageRoot.atResult (natMemory m) ((A).results+8*rootId A (natMemory m))).bits=(N i).internal)
    (inputs : Records tag (N i) (terminal A (natMemory m)).stream m)
    (ports : Incidences (terminal A (natMemory m)) (natMemory m) m (pins i))
    (small : ∀ r j,metadata tag (N i) r j<2^W) :
    ForestRoot A N pins (immutable u) i m := by
  let T := terminal A (natMemory m)
  let c : Word W := (((A).seed+5:ℕ):Word W)
  have w := chart.space
  have space := word_space (i:=18) age (by omega)
  have s9 := apart (u:=u) (by decide : 9<10)
  have s10 := apart (u:=u) (by decide : 10<14)
  have s14 := apart (u:=u) (by decide : 14<15)
  have s15 := apart (u:=u) (by decide : 15<16)
  have s16 := apart (u:=u) (by decide : 16<17)
  have s17 := apart (u:=u) (by decide : 17<18)
  have C : c.val=base u 14+5 := Fin.val_cast_of_lt (by omega : base u 14+5<2^W)
  have mp : T.map=base u 14+64 := rfl
  have arg : T.arguments=base u 16 := rfl
  have tab : 7*(T.halves+2)≤ stride u := chart.tableWords
  have map : 64+T.localPins≤ stride u := chart.mapWords
  have stream : base u 10≤T.stream ∧ T.stream+4*T.rows≤base u 14 := chart.stream
  have «meta» : T.meta+4*T.rows≤base u 9+stride u := chart.metadata
  have sep : PinBanks T c := by
    constructor <;> first | omega
  refine ⟨mounted_root_bounds age m chart,chart.span,sep,ports,port,rows,bits,inputs,stream.2,chart.endpoints,
    by change T.map+T.localPins≤_; omega,by change 2+T.localPins<_; omega,small,?_,?_⟩
  · intro z hz
    change free A T z ∧ (z<T.meta ∨ T.meta+4*T.rows≤z)
    rcases hz with ⟨zl,zh⟩|⟨zl,zh⟩|zl <;> simp only [free,mounted,mp] <;> omega
  · change ((base u 18+4<base u 14 ∨ base u 14+26≤base u 18+4) ∧
      (base u 18+4<base u 15 ∨ base u 15+7*(T.halves+2)≤base u 18+4) ∧
      (base u 18+4<base u 16 ∨ base u 16+7*(T.halves+2)≤base u 18+4) ∧
      (base u 18+4<T.map ∨ T.map+T.localPins≤base u 18+4))
    omega


end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.RAM.TickTerminalRoot

open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickWorkspace Diagonal.HistoryTerminalJoin BitLayout
open scoped BigOperators

variable {F : Type*} [Field F] [Fintype F] {u p n H : ℕ} {arity : Fin n→ℕ}
variable (N : ∀ i,BitNetwork F (arity i)) (pins : ∀ i,Fin (arity i)→Fin p) (pin : Fin p→Bool)
variable (wireStart wirePrefix : ℕ)
local notation "W" => 16*u^10
local notation "A" => mounted u p wireStart wirePrefix

/-- The native filtering initialization itself supplies all five loop control words and
preserves every raw input and low mutable word. Local typed stream publication is the
only per-root input needed by the final forest pass. -/
def physical_forest (age : 1≤u) (space : 65≤ stride u)
    (head : TickPhysicalABI.NavigationHeader) (own : TickSlotLookup.Owner W) (m : Memory W)
    (number : (rootIds u head own m).length=n) (rootRoom : 2*head.roots≤ stride u/4)
    (rowRoom : 4*(forest N pins).cells≤ stride u) (bitRoom : (forest N pins).internal≤ stride u)
    (low : cellsBase p H≤ stride u) (physical : ∀ z<cellsBase p H,m z=TickMountedPins.memory pin z)
    (nodes : ∀ (i : Fin n) (mem : Memory W),
      (∀ z,immutable u z → mem z=rootStart u head own m z) →
      natMemory mem (A).control=i.val → natMemory mem ((A).control+1)=n →
      natMemory mem ((A).control+2)=rowStart N i → natMemory mem ((A).control+3)=bitStart N i →
      ForestRoot A N pins (immutable u) i mem) :
    ForestRows A N pins pin H (rootStart u head own m) := by
  have rsum : rootSum (fun i=>(N i).cells) n=(forest N pins).cells := rootSum_all _
  have bsum : rootSum (fun i=>(N i).internal) n=(forest N pins).internal := by
    rw [rootSum_all,forest,Diagonal.TickSlotForest.internal]; rfl
  have w := word_space (i:=18) age (by omega)
  have d9 := apart (u:=u) (by decide : 9<14)
  have d14 := apart (u:=u) (by decide : 14<17)
  have d17 := apart (u:=u) (by decide : 17<18)
  have s9 := lower u 9
  have s17 := lower u 17
  have nbound : n≤head.roots := by
    rw [←number]
    simpa only [rootIds,TickRootScanInit.chosen,List.length_range] using
      (List.length_filter_le
        (TickSlotLookup.matchesOwner own (m (rootLookup u).s1) (m ((rootLookup u).s1+3)))
        (List.range head.roots))
  have controls := TickRootScanInit.output_controls (rootLookup u) (rootIds u head own m) m
  refine ⟨immutable u,?_,?_,?_,by omega,by change base u 18+4<_; omega,rfl,low.trans s9,?_,?_,
    by change base u 14+26≤base u 14+64; omega,by omega,?_,?_,nodes⟩
  · rintro z (⟨_,h⟩|⟨_,h⟩|h) <;> change z≠base u 18+4 <;> omega
  · rw [rsum]; omega
  · rw [bsum]; omega
  · change base u 9+4*_≤base u 14
    rw [rsum]
    omega
  · change base u 9+4*_≤base u 18
    rw [rsum]
    omega
  · rw [←number]
    exact controls
  · intro z hz
    apply Eq.trans (TickRootScanInit.output_outside (rootLookup u) (rootIds u head own m) m z
      (Or.inl (by change z<base u 18; omega))
      (Or.inl (by change z<base u 17; omega)))
    exact physical z hz

end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.RAM.TickTerminalRoot
open Computability.VPVNP.BurstRAM PhysicalProcedure HistoryStageBody.Physical

/-- All opcode, scratch-register, and public-ROM counts for the concrete preparation
procedure are bounded before the age is selected. Its directory and coefficient image
are data and may grow with the age. -/
theorem block_prepare_resources {F : Type} [Field F] [Fintype F] (B : Diagonal.PhysicalStage.Block F) :
    ∃ cut,∀ (start height K W u p H J wireStart wirePrefix : ℕ) (field : FieldCode F W)
      (shape : TraceBucketAtom.Layout) (publicWords : Fin TraceEndpointROM.params→Word W) (startup : TracePrototypeBoot.Args W),
      let a := prepare field u p H J wireStart wirePrefix (archive B start height K) shape publicWords
        (families B start height) startup
      a.labels+a.registers+a.slots≤cut := by
  obtain ⟨inner,cover⟩ := block_selected_resources B
  refine ⟨400+inner+finishLabels F+finishRegisters F+finishSlots,?_⟩
  intro start height K W u p H J wireStart wirePrefix field shape publicWords startup
  have startSize:=startup.resources u
  let source := selected W u (archive B start height K) shape publicWords (families B start height)
  let last := finish field u p H J wireStart wirePrefix
  have c : source.labels+source.registers+source.slots≤ inner := cover start height K W u shape publicWords
  obtain ⟨labels,registers,slots⟩ := finish_shape field u p H J wireStart wirePrefix
  change (startup.procedure u).labels+source.labels+last.labels+((startup.procedure u).registers+source.registers+last.registers)+((startup.procedure u).slots+source.slots+last.slots)≤_
  change last.labels=finishLabels F at labels
  change last.registers=finishRegisters F at registers
  change last.slots=finishSlots at slots
  omega


end ThreeFlat.RAM.TickTerminalRoot

namespace ThreeFlat.RAM.TickTerminalRoot
open Computability.VPVNP.BurstRAM HistoryTerminalTape
open scoped BigOperators

/-- One real S17 root iteration and its previously selected interior subtree
fit the same S43 work word, including the root's private trivalent rows. -/
theorem iteration_share {W : ℕ} (A : Arena) (init : Memory W) (i : ℕ)
    (inside amount previousRate unitWork degreeCap rowRate pairs : ℕ)
    (previous : inside≤previousRate*amount)
    (tariff : previousRate+rootFactor*(degreeCap+4*rowRate+3)≤unitWork)
    (degree : let raw:=natMemory (decrease A (images A init i));(terminal A raw).halves≤degreeCap)
    (endpoints : let raw:=natMemory (decrease A (images A init i));(terminal A raw).ext≤2*pairs)
    (volume : let raw:=natMemory (decrease A (images A init i));let T:=terminal A raw
      1+(∑ j : Fin T.halves,(half T raw j.val).width)+pairs≤amount)
    (rows : let raw:=natMemory (decrease A (images A init i));(terminal A raw).rows≤rowRate*amount) :
    inside+iterationCost A init i≤unitWork*amount := by
  let raw:=natMemory (decrease A (images A init i))
  let T:=terminal A raw
  have covers:=charge_covers T raw degree endpoints volume rows
  have terminalPrice:= (work_bound W A T raw).trans (Nat.mul_le_mul_left _ covers)
  change inside+oneCost W A T raw≤_
  calc
    _ ≤ previousRate*amount+rootFactor*((degreeCap+4*rowRate+3)*amount) := Nat.add_le_add previous terminalPrice
    _ = (previousRate+rootFactor*(degreeCap+4*rowRate+3))*amount := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ tariff


end ThreeFlat.RAM.TickTerminalRoot

end
end OAI
