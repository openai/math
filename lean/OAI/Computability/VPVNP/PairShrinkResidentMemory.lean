import OAI.Computability.VPVNP.PairShrinkJobPrepared
import OAI.Computability.VPVNP.PairSimulationResidentMapLoop

/-!
# Child and hidden operands across the resident map loop

Every selected map reads its input packets below the histogram and its
shared hidden fields above it. Its writes affect the histogram, its own
operand staging and its grouped-map workspace. The two input regions thus
agree with the memory at the start of the loop after every successful map.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PairSimulation.ShrinkResidentMemory

open BurstRAM BurstRAM.PrivateRAM ShrinkCallFields
open scoped Fin.CommRing

variable {w p r : ℕ}

/-- The two scratch memories agree below the histogram base and from the hidden base up to the
staging base. -/
structure Preserved (s : Scratch) (initial current : Word w → Word w) : Prop where
  low : ∀ q : Word w, q.val < s.hist → current q = initial q
  shared : ∀ q : Word w, s.hidden ≤ q.val → q.val < s.staging → current q = initial q

theorem Preserved.refl (s : Scratch) (m : Word w → Word w) : Preserved s m m :=
  ⟨fun _ _ ↦ rfl, fun _ _ _ ↦ rfl⟩

theorem Preserved.trans {s : Scratch} {a b c : Word w → Word w}
    (ab : Preserved s a b) (bc : Preserved s b c) : Preserved s a c :=
  ⟨fun q h ↦ (bc.low q h).trans (ab.low q h),
    fun q lo hi ↦ (bc.shared q lo hi).trans (ab.shared q lo hi)⟩

theorem Preserved.stable (P : ResidentMapLoop.Program p r) (s : Scratch)
    (initial : Word w → Word w) : P.Stable (fun c ↦ Preserved s initial c.privateMem) := by
  intro c d old _ mem _
  rw [mem]
  exact old

/-- Loop inputs include the live register words supplied by the locator and
the resident operand cells carried across previous calls. -/
structure Invariant (s : Scratch) (initial : Word w → Word w)
    (live : Fin r → Prop) (expected : Fin r → Word w) (c : Config w p r) : Prop where
  registers : ∀ j, live j → c.reg j = expected j
  memory : Preserved s initial c.privateMem

theorem Invariant.start (s : Scratch) (c : Config w p r) (live : Fin r → Prop) :
    Invariant s c.privateMem live c.reg c :=
  ⟨fun _ _ ↦ rfl, Preserved.refl s c.privateMem⟩

theorem Invariant.stable (P : ResidentMapLoop.Program p r) (s : Scratch)
    (initial : Word w → Word w) (live : Fin r → Prop) (expected : Fin r → Word w)
    (away : ∀ j, live j → j ≠ P.cursor) : P.Stable (Invariant s initial live expected) := by
  intro c d old frozen mem _
  refine ⟨fun j hj ↦ (frozen j (away j hj)).trans (old.registers j hj), ?_⟩
  rw [mem]
  exact old.memory

theorem Invariant.next {s : Scratch} {initial : Word w → Word w}
    {live : Fin r → Prop} {expected : Fin r → Word w} {c d : Config w p r}
    (old : Invariant s initial live expected c)
    (frozen : ∀ j, live j → d.reg j = c.reg j) (mem : Preserved s initial d.privateMem) :
    Invariant s initial live expected d :=
  ⟨fun j hj ↦ (frozen j hj).trans (old.registers j hj), mem⟩

/-- The histogram block of the terminal allocation precedes the first
shared shrinking word. -/
theorem histogram_before_hidden (R : LeafArena.Regions) (n t : ℕ) (ht : t ≤ R.histWords) :
    R.histBase + t ≤ ShrinkCallABI.hiddenBase R n := by
  change R.histBase + t ≤ R.cacheBase + 38 + _
  exact ((Nat.add_le_add_left ht _).trans R.hist_before).trans
    ((Nat.le_add_right ..).trans (Nat.le_add_right ..))

end PairSimulation.ShrinkResidentMemory

namespace PairSimulation.ShrinkCallFields

open BurstRAM Compression Compression.ShrinkMotif MotifEntry MotifGrid MotifBlocks MotifConversion
open ShrinkResidentMemory
open scoped Fin.CommRing

variable {K : Type} [_root_.Field K] {factor : ℝ} {w p r k t u n limit : ℕ}
variable (F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor)
variable {grid : F.grid.demands} {j : Fin 6} (A : MapEntryTable.Allocation F grid j r k)
variable (loc : A.Address → Fin p) (demand : Bool → ℕ) (payload : Bool × Fin 4 → ℕ)
variable (d : DemandBits demandSource demandTarget demand j)
variable (x : MotifSelector.Half supply (fun e ↦ Fin (payload e + u * F.selectorBits) → Bool) j)
variable (s : Scratch) (ord : ℕ) (side : Bool) (cd : Bool → ℕ)
variable (ok : Fits (w := w) (n := n) (limit := limit) (u := u) (t := t) F demand payload s ord cd)
local notation "W" => workspace F (A.program loc) demand payload d x s ord side cd ok

/-- Every word preceding operand staging and outside the actual histogram
survives a successful resident gather and grouped-map execution. -/
theorem resident_exterior {before after : Word w → Word w}
    (histEnd : s.hist + t ≤ s.hidden)
    {ptr : Word w} (address : ptr = (s.descriptor : Word w))
    (memory : ∀ q : Word w, q.val < s.staging →
      q.val < ptr.val ∨ ptr.val + Fintype.card Arg ≤ q.val →
      MapCallSetup.Outside A loc W q → after q = before q) :
    ∀ q : Word w, q.val < s.staging →
      (q.val < s.hist ∨ s.hist + t ≤ q.val) → after q = before q := by
  have room := ok.room.trans_lt ok.capacity.room
  have dirFit : s.directory + 16 < 2 ^ w := by
    unfold Scratch.target Scratch.source Scratch.descriptor at room
    omega
  have ptrVal : ptr.val = s.descriptor := by
    rw [address]
    exact Nat.mod_eq_of_lt dirFit
  have stageDir : s.staging ≤ s.directory := Nat.le_add_right ..
  have hiddenStage : s.hidden ≤ s.staging := Nat.le_add_right ..
  have histRoom : s.hist + t < 2 ^ w :=
    ((histEnd.trans hiddenStage).trans stageDir).trans_lt (by omega)
  have sc := workspace_source F (A.program loc) demand payload d x s ord side cd ok
  have ta := workspace_target F (A.program loc) demand payload d x s ord side cd ok
  have srcStart : s.directory ≤ s.source := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have tgtStart : s.source ≤ s.target u := Nat.le_add_right ..
  have keep (q : Word w) (hq : q.val < s.staging) (hh : q.val < s.hist ∨ s.hist + t ≤ q.val) :
      after q = before q := by
    apply memory q hq (.inl (ptrVal ▸ (hq.trans_le (stageDir.trans (Nat.le_add_right ..)))))
    constructor
    · refine ⟨.inl (sc ▸ hq.trans_le (stageDir.trans srcStart)),
        .inl (ta ▸ hq.trans_le (stageDir.trans (srcStart.trans tgtStart))), ?_⟩
      intro l eqn
      have hv := congrArg Fin.val eqn
      change q.val = ((s.hist + l.val : ℕ) : Word w).val at hv
      rw [show ((s.hist + l.val : ℕ) : Word w).val = s.hist + l.val from
        Nat.mod_eq_of_lt ((Nat.add_lt_add_left l.isLt _).trans histRoom)] at hv
      rcases hh with lo | hi <;> have := l.isLt <;> omega
    · intro a eqn
      have len := MapPortAgreement.ports_length_le supply j A.edgeOrder
      have card : 2 * Fintype.card (Bool × Fin 4) = 16 := by simp
      rw [card] at len
      have valid : s.directory + a.val < 2 ^ w :=
        ((Nat.add_lt_add_left (a.isLt.trans_le len) _).trans dirFit)
      have hv := congrArg Fin.val eqn
      change q.val = ((s.directory : Word w) + (a.val : Word w)).val at hv
      rw [← Nat.cast_add, show ((s.directory + a.val : ℕ) : Word w).val = s.directory + a.val
        from Nat.mod_eq_of_lt valid] at hv
      omega
  exact keep

/-- Apply the exterior frame returned by the installed gather and grouped
matrix to both resident input regions. Each valid call preserves every
other resident's child and shared words, regardless of its own motif or
party. -/
theorem resident_preserved {initial before after : Word w → Word w}
    (previous : Preserved s initial before) (histEnd : s.hist + t ≤ s.hidden)
    {ptr : Word w} (address : ptr = (s.descriptor : Word w))
    (memory : ∀ q : Word w, q.val < s.staging →
      q.val < ptr.val ∨ ptr.val + Fintype.card Arg ≤ q.val →
      MapCallSetup.Outside A loc W q → after q = before q) :
    Preserved s initial after := by
  have keep := resident_exterior F A loc demand payload d x s ord side cd ok histEnd address memory
  have hiddenStage : s.hidden ≤ s.staging := Nat.le_add_right ..
  exact previous.trans ⟨fun q lo ↦ keep q (lo.trans_le
    ((Nat.le_add_right s.hist t).trans (histEnd.trans hiddenStage))) (.inl lo),
    fun q lo hi ↦ keep q hi (.inr (histEnd.trans lo))⟩

end PairSimulation.ShrinkCallFields

namespace PairSimulation.ShrinkPartyNative

open BurstRAM Compression Compression.PackingData Compression.ShrinkMotif
open MotifBlocks MotifGrid MotifConversion NetworkKernel
open CompressorRecords CompressorRecords.ShrinkSlots NodeArguments ShrinkResidentMemory
open scoped Fin.CommRing

variable {a b g w endAddr : ℕ} {K : Type} [_root_.Field K] {factor δ : ℝ}
variable {X : State a (packingLaneBits a g)}
variable {F : FixedBlock K demandSource demandTarget supply
  (realWidths demandMass) (realWidths supplyMass) (31 / 16) factor}
variable {ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ} {sel : X.ShrinkSelection F}
variable {m : X.packingData.Motif} {party : Fin 6} (J : Job X F ready sel m party w)
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _
variable {before after : Word w → Word w}
local notation "side" => selectedLayout X F sel
local notation "widths" => ShrinkPreparedCall.width F X sel
local notation "Idx" => Fin.val (ShrinkMotifOrder.stateNumber X m)

/-- The lower arena still holds every independently chosen old half after a
previous map has updated its own selector, labels and histogram. -/
theorem Job.childWords_preserved (frame : Preserved J.scratch before after)
    (child : J.ChildWords before endAddr)
    (low : ∀ u, J.arena.base (J.nodes u) + J.arena.stride ≤ J.scratch.hist) :
    J.ChildWords after endAddr := by
  intro site atSite
  exact ShrinkCallDemandCells.placedPackets_frame X side J.arena J.nodes
    (child site atSite) low frame.low

/-- All child and parent packet premises used by the actual party gather
survive in the common input region. -/
theorem Job.packets_preserved (frame : Preserved J.scratch before after)
    (p : J.Packets endAddr before)
    (childLow : ∀ u, J.arena.base (J.nodes u) + J.arena.stride ≤ J.scratch.hist)
    (parentLow : J.arena.base J.node + J.arena.stride ≤ J.scratch.hist) :
    J.Packets endAddr after := by
  refine ⟨fun dir hit ↦ ShrinkCallDemandCells.placedPackets_frame X side J.arena J.nodes
    (p.old dir hit) childLow frame.low, p.oldEnd, p.parentFit, ?_, p.parentEnd,
    p.abStride, p.abRoom, p.supplyStride, p.supplyRoom⟩
  apply p.parentStored.congr
  intro i
  let a : Word w := ((J.arena.base J.node + i.val : ℕ) : Word w)
  have val : a.val = J.arena.base J.node + i.val := Nat.mod_eq_of_lt
    ((Nat.add_lt_add_left i.isLt _).trans_le p.parentFit.2.2)
  have lo : endAddr ≤ a.val := val ▸ p.parentFit.1.trans (Nat.le_add_right ..)
  have hi : a.val < J.scratch.hist := val ▸
    (Nat.add_lt_add_left (i.isLt.trans_le p.parentFit.2.1) _).trans_le parentLow
  change rawScratch (DFS.scratch endAddr after) a = rawScratch (DFS.scratch endAddr before) a
  simpa only [rawScratch, dite_eq_left lo, DFS.scratch] using frame.low a hi

/-- Hidden fields belonging to the current motif survive calls for any
earlier resident, including a different party at the same packed site. -/
theorem Job.absorbed_preserved
    (hidden : Placed (X.packingData.shrinkInternalOwner side) (internalLabel widths side)
      (X.packingData.shrinkPartySite side m party))
    (frame : Preserved J.scratch before after)
    (h : ShrinkCallSupplyCells.Absorbed X side widths m party J.scratch hidden before)
    (ordinal : Idx < J.scratch.motifs)
    (bound : ∀ t, widths m (!side, t) ≤ J.scratch.stride) (room : J.scratch.staging ≤ 2 ^ w) :
    ShrinkCallSupplyCells.Absorbed X side widths m party J.scratch hidden after := by
  intro t own i
  let a := J.scratch.shared Idx t + i.val
  have hi : a < J.scratch.staging :=
    (Nat.add_lt_add_left (i.isLt.trans_le (bound t)) _).trans_le (J.scratch.shared_end ordinal t)
  have low : J.scratch.hidden ≤ a := (Nat.le_add_right ..).trans (Nat.le_add_right ..)
  have val : (a : Word w).val = a := Nat.mod_eq_of_lt (hi.trans_le room)
  exact (frame.shared (a : Word w) (by rw [val]; exact low) (by rw [val]; exact hi)).trans
    (h t own i)

end PairSimulation.ShrinkPartyNative

namespace PairSimulation.ShrinkPartyNative

open BurstRAM BurstRAM.PrivateRAM Compression Compression.PackingData Compression.ShrinkMotif
open MotifBlocks MotifGrid MotifConversion MotifEntry NetworkKernel
open CompressorRecords CompressorRecords.ShrinkSlots ShrinkResidentMemory
open scoped Fin.CommRing

variable {a b g w t n limit : ℕ} {K : Type} [_root_.Field K] {S : BlockSchedule K}
variable (B : S.Templates) (degree : ℕ) (ord : B.Entry → Fin t) {δ : ℝ}
variable (X : State a (packingLaneBits a g))
variable (ready : Ready (2 ^ a) (2 * 2 ^ a + 1) (2 ^ b) δ) (sel : X.ShrinkSelection B.shrink)
variable (m : X.packingData.Motif) (j : Fin 6) (J : Job X B.shrink ready sel m j w)
private noncomputable local instance : DecidableEq X.Base := Classical.decEq _
local notation "side" => selectedLayout X B.shrink sel
local notation "BW" => ShrinkPreparedCall.widthsDemand X m
local notation "idx" => Fin.val (ShrinkMotifOrder.stateNumber X m)
local notation "cd" => ShrinkCallDemandCells.cdBase X m J.arena J.nodes
variable (hidden : Placed (X.packingData.shrinkInternalOwner (selectedLayout X B.shrink sel))
  (internalLabel (ShrinkPreparedCall.width B.shrink X sel) (selectedLayout X B.shrink sel))
  (X.packingData.shrinkPartySite (selectedLayout X B.shrink sel) m j))
local notation "call" => Job.entryInput B X ready sel m j J hidden
local notation "L" =>
  MapHandlerOperand.layout (ShrinkCallABI.family B degree a ord) demandMass_pos call
variable (ok : ShrinkCallFields.Fits (w := w) (n := n) (limit := limit) (t := t)
  (u := repetitions B.shrink (ShrinkPreparedCall.widthsDemand X m)) B.shrink
  (ShrinkPreparedCall.widthsDemand X m) (sel m).val J.scratch (ShrinkMotifOrder.stateNumber X m).val
  (ShrinkCallDemandCells.cdBase X m J.arena J.nodes))
local notation "W" => Job.mapWorkspace B degree ord X ready sel m j J hidden ok

/-- The private-memory conclusion of the scheduled row interpreter maintains
the resident loop's invariant for the actual selected map workspace. -/
theorem Job.resident_preserved {initial before after : Word w → Word w}
    (prior : Preserved J.scratch initial before) (histEnd : J.scratch.hist + t ≤ J.scratch.hidden)
    {ptr : Word w} (address : ptr = (J.scratch.descriptor : Word w))
    (frame : ∀ q : Word w, q.val < J.scratch.staging →
      q.val < ptr.val ∨ ptr.val + Fintype.card ShrinkCallFields.Arg ≤ q.val →
      MapCallSetup.Outside (L).core ((L).corePC (L).locations) W q → after q = before q) :
    Preserved J.scratch initial after :=
  ShrinkCallFields.resident_preserved B.shrink (L).core ((L).corePC (L).locations) BW (sel m).val
    (demandBits demandSource demandTarget j (LocalHistory.EntryInput.demandBits call))
    (MotifSelector.mapHalf supply (fun _ ↦ inputBits) (LocalHistory.EntryInput.supplyBits call))
    J.scratch idx side cd ok prior histEnd address frame

/-- The job header places the map descriptor sixteen words after its
private pointer directory. This recovers the pointer in the exterior frame
from the actual level fields and the live register bank. -/
theorem Job.descriptor_address (pub : Fin 5 → Word w) (st : Word w) (mem : Memory w)
    {level : Word w} {T : IncidenceDirectory w} {origin : ℕ}
    (old : J.OldPublished (ShrinkCallABI.operands degree) pub st mem level T origin) :
    (((ShrinkCallABI.operands degree).inputs a).descriptor).eval pub st mem =
      (J.scratch.descriptor : Word w) := by
  let O := ShrinkCallABI.operands degree
  have h := ShrinkCallHeader.heads X B.shrink sel m O pub st level mem J.arena T origin
    J.older J.pitch J.first J.scratch.hidden J.scratch.stride J.scratch.hist old.levelData old.live
  change O.hidden.eval pub st mem + 4 * (O.count a).eval pub st mem * O.slotStride.eval pub st mem
    + 9 * O.slotStride.eval pub st mem + 16 = _
  rw [old.live.hiddenBase, old.live.stride, h.motifs, ← old.motifCount]
  simp only [ShrinkCallFields.Scratch.descriptor, ShrinkCallFields.Scratch.directory,
    ShrinkCallFields.Scratch.staging, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat]

/-- Maintain the full loop invariant using the frozen live registers and
the exterior memory clause of a successful selected resident map. -/
theorem Job.keepsInputs {p r : ℕ} {initial : Word w → Word w}
    {live : Fin r → Prop} {expected : Fin r → Word w} {c out : Config w p r}
    (prior : Invariant J.scratch initial live expected c)
    (frozen : ∀ a, live a → out.reg a = c.reg a)
    (histEnd : J.scratch.hist + t ≤ J.scratch.hidden)
    (pub : Fin 5 → Word w) (st : Word w) (mem : Memory w)
    {level : Word w} {T : IncidenceDirectory w} {origin : ℕ}
    (old : J.OldPublished (ShrinkCallABI.operands degree) pub st mem level T origin)
    (frame : let ptr := (((ShrinkCallABI.operands degree).inputs a).descriptor).eval pub st mem
      ∀ q : Word w, q.val < J.scratch.staging →
        q.val < ptr.val ∨ ptr.val + Fintype.card ShrinkCallFields.Arg ≤ q.val →
        MapCallSetup.Outside (L).core ((L).corePC (L).locations) W q →
        out.privateMem q = c.privateMem q) :
    Invariant J.scratch initial live expected out :=
  prior.next frozen (Job.resident_preserved B degree ord X ready sel m j J hidden ok prior.memory
    histEnd (Job.descriptor_address B degree X ready sel m j J pub st mem old) frame)

end PairSimulation.ShrinkPartyNative

end VPVNP
end Computability
end OAI
