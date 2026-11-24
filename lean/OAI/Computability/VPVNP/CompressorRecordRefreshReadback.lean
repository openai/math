import OAI.Computability.VPVNP.CompressorRecordRefreshBuild
import OAI.Computability.VPVNP.DegreeRefreshEntries

/-!
# Reading the port-local coefficient from a constructed refresh

At the local port, both segment lookups use the same site/port index. The incoming table
already contains the source ordering's offset. Reading the two independent half-words at
these stored intervals supplies the diagonal tests and all external halves of the two
ordered families of ties. The dense demand and selected payload rows determine the
arguments of the scalar-index map for the actual kernel.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace CompressorRecords.PortRefresh.Readback

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh SpectralGeometry
open NetworkKernel WireTensor MotifConversion NewSlots RefreshRAM

variable {bits a a₀ g dH t : ℕ} {k : Type*} [_root_.Field k] {K K' : ℝ}
variable (X : State a (a+g)) (q : Fin 8 → W bits) (m : Memory bits)

local notation "O" => sites (D := 2^a) X.baseIndex (bitWordFinEquiv g)
local notation "D" => 2^a
local notation "S" => Fintype.card X.Base * D * 2^g * D
local notation "G" => splitSlots X
local notation "port" => bitWordFinEquiv a
local notation "w₀" => splitWidths X
local notation "ws" => groupedWidths port w₀
local notation "perm" => oldPortMatching G port
local notation "dst" => bundleTarget G

/-- Numerical width and offset of one incident external segment. The direction is local
to the port, so the incoming read needs no inverse translation. -/
def interval (fit : S ≤ 2^bits) (outgoing : Bool) (e : DyadicArc X.Base (BitWord g) a) : ℕ × ℕ :=
  let i := idWord O fit e
  if outgoing then ((cell q m 1 i).val,(cell q m 5 i).val)
  else ((cell q m 7 i).val,(cell q m 6 i).val)

/-- The width and offset in each physical half of the table describe the corresponding
source-ordered segment of the incident external word. -/
theorem interval_spec {fit : S ≤ 2^bits} (data : SegmentFields X q fit m) (e : DyadicArc X.Base (BitWord g) a) :
    interval X q m fit true e = (ws e,(outgoingRecord G port w₀ e).offset) ∧
    interval X q m fit false e = (ws ((perm).symm e),(incomingRecord G port w₀ e).offset) := by
  obtain ⟨width,offset,_⟩ := data.segments e
  have dest := (data.segments ((perm).symm e)).2.2
  simp only [Equiv.apply_symm_apply] at dest
  exact ⟨Prod.ext width offset,Prod.ext dest.2 (dest.1.trans (congrArg SegmentRecord.offset
    (incomingRecord_matching G port w₀ e).symm))⟩

/-- Read one bit using the stored length and offset. Empty segments have no readable bits. -/
def bit {n : ℕ} (field : ℕ × ℕ) (wire : Refresh.Word n) (i : ℕ) : Option Bool :=
  if i < field.1 then if h : field.2+i < n then some (wire ⟨field.2+i,h⟩) else none else none

private theorem bit_eq {n : ℕ} {field : ℕ × ℕ} (wire : Refresh.Word n) (i : Fin field.1) (j : Fin n)
    (pos : j.val = field.2+i.val) : bit field wire i.val = some (wire j) := by
  simp only [bit,ite_eq_left i.isLt,dite_eq_left (pos ▸ j.isLt)]
  exact congrArg (fun v => some (wire v)) (Fin.ext pos.symm)

/-- The two lists of segment words produced from physical endpoint records. -/
def segments (fit : S ≤ 2^bits) (p : (X.Base × BitWord g) × Fin D)
    (outWord : Refresh.Word (∑ j, ws (p,j))) (inWord : Refresh.Word (∑ j, ws ((dst).symm p,j))) :
    PortSegments perm ws p.1 p.2 :=
  (fun j i => (bit (interval X q m fit true (p,j)) outWord i.val).getD false,
   fun j i => (bit (interval X q m fit false (p,j)) inWord i.val).getD false)

/-- Physical offsets and widths recover the same bit lists as the exact kernel for
arbitrary independently chosen incoming and outgoing payloads. -/
theorem segments_eq {fit : S ≤ 2^bits} (data : SegmentFields X q fit m) (p : (X.Base × BitWord g) × Fin D)
    (outWord : Refresh.Word (∑ j, ws (p,j))) (inWord : Refresh.Word (∑ j, ws ((dst).symm p,j))) :
    segments X q m fit p outWord inWord = incidentPortSegments perm dst (oldPortMatching_bundle G port) ws p outWord inWord := by
  apply Prod.ext
  · funext j i
    obtain ⟨u,pos,h⟩ := (local_bit_reads G port w₀ p j outWord inWord).1 i
    change (bit (interval X q m fit true (p,j)) outWord i.val).getD false = _
    rw [(interval_spec X q m data (p,j)).1,bit_eq (field := (ws (p,j),(outgoingRecord G port w₀ (p,j)).offset)) outWord i u pos,h]
    rfl
  · funext j i
    obtain ⟨u,pos,h⟩ := (local_bit_reads G port w₀ p j outWord inWord).2 i
    change (bit (interval X q m fit false (p,j)) inWord i.val).getD false = _
    rw [(interval_spec X q m data (p,j)).2,bit_eq (field := (ws ((perm).symm (p,j)),(incomingRecord G port w₀ (p,j)).offset)) inWord i u pos,h]
    rfl

variable (E : RegularArcGraph (Fin (2^a)) dH) (hdH : 0 < dH) (conn : (arcSupportGraph E.multiplicity).Connected)
  (F : RefreshBlock k (expanderSupply E hdH conn) (2^a₀) K K') (hD : 1 < 2^a) (hd : dH+1 ≤ 2^a₀)
  (choice : DyadicRefreshChoice X E hdH conn F) (ties : Fin t ≃ Tie (2^a)) (start stride : ℕ)

local notation "P" => Allocation.plan X a₀ dH t stride start
local notation "Q" => Allocation.Plan.scratch P bits
local notation "demand" => blockDemandWidths G port w₀
local notation "Y" => expanderBranchGraph G port w₀ E hdH conn F hD hd choice
local notation "outBase" => word (bits := bits) (Allocation.Plan.term P)
local notation "inBase" => word (bits := bits) (Allocation.Plan.demand P)

/-- Read the selected payload vector without any search through a finite enumeration. -/
def payload (base : W bits) (s : X.Base × BitWord g) (e : Fin D × Fin dH) : ℕ :=
  (m ((SupplyScan.recordBase X base stride s).val + 2 + (finProdFinEquiv e).val)).val

theorem payload_eq {fit : S ≤ 2^bits} (stored : Build.Stored X E hdH conn F choice ties start stride fit m)
    (s : X.Base × BitWord g) : payload X m stride outBase s = (choice s).val := by
  funext e
  simpa only [payload,Equiv.symm_apply_apply] using (stored.readback s).2.2 (finProdFinEquiv e)

private noncomputable def loadedEntry (d d' : Tie D → ℕ) (v v' : Fin D × Fin dH → ℕ)
    (hd : d' = d) (hv : v' = v) (j : Fin D) (x : MotifDemandPadding.HalfBits tieSource tieTarget d j)
    (y : MotifSelector.Half (expanderSupply E hdH conn) (fun e => Fin (2^(supplyWidths F d v e))) j) :
    Option (Fin (repetitions F d) → (parameterData F).Entry) :=
  let x' : MotifDemandPadding.HalfBits tieSource tieTarget d' j := hd.symm ▸ x
  let y' : MotifSelector.Half (expanderSupply E hdH conn) (fun e => Fin (2^(supplyWidths F d' v' e))) j :=
    hd.symm ▸ hv.symm ▸ y
  hd ▸ entry F (fun _ => zero_lt_one) d' v' j x' y'

private theorem loadedEntry_eq (d d' : Tie D → ℕ) (v v' : Fin D × Fin dH → ℕ)
    (hw : d' = d) (hv : v' = v) (j x y) :
    loadedEntry E hdH conn F d d' v v' hw hv j x y = entry F (fun _ => zero_lt_one) d v j x y := by
  subst d' v'; rfl

/-- Port-local scalar indices using the constructed records for segment reads, demand
widths and the admitted supply profile. The ordinary incident half-wires remain inputs. -/
noncomputable def indices {fit : S ≤ 2^bits} (stored : Build.Stored X E hdH conn F choice ties start stride fit m)
    (p : (X.Base × BitWord g) × Fin D)
    (before : Placed (refreshPositions port) (actualWireGraph G w₀).Half (promotedSites p))
    (after : (Y).Half (promotedSites p)) :
    Option (Fin (repetitions F (demand p.1)) → (parameterData F).Entry) := by
  classical
  let n := blockSupplyWidths G port w₀ E hdH conn F choice
  let A := fun s e => Fin (2^n s e)
  let x := (originalIso G port w₀).pullHalf p (before (originalSites port p) (by simp [promotedSites,originalSites,refreshPositions]))
  let u := (promotedIso G port w₀ E.toSlotGraph hD hd A n (fun s e => (wordIndex (n s e)).symm)).pullHalf p after
  let z := segments X Q m fit p (u.1 (.inl p) rfl) (u.2 (.inl ((dst).symm p)) ((dst).apply_symm_apply p).symm)
  let y := supplyHalf (R := ℤ) dst ws Prod.fst (fun e => (E.reverse e).1) A (2^a₀-(dH+1)) p u
  exact if x.1 ((p.1,p.2),p.2) rfl = z.1 p.2 ∧ z.2 p.2 = incomingHalf (R := ℤ) perm ws p.1 p.2 p.2 x then
    loadedEntry E hdH conn F (demand p.1) (DemandPreparation.demandAt ties (DemandScan.rowBase X t inBase p.1) m)
      (choice p.1).val (payload X m stride outBase p.1) (stored.demands p.1)
      (payload_eq X m E hdH conn F choice ties start stride stored p.1) p.2 (portInput (R := ℤ) perm ws p.1 p.2 x z) y
  else none

/-- The labels obtained from the physical records are exactly the common parameter
indices of the port kernel, including the failure cases of its diagonal and selector tests. -/
theorem indices_eq {fit : S ≤ 2^bits} (stored : Build.Stored X E hdH conn F choice ties start stride fit m)
    (p : (X.Base × BitWord g) × Fin D)
    (before : Placed (refreshPositions port) (actualWireGraph G w₀).Half (promotedSites p))
    (after : (Y).Half (promotedSites p)) :
    indices X m E hdH conn F hD hd choice ties start stride stored p before after =
      refreshEntryIndices G port w₀ E hdH conn F hD hd choice p before after := by
  unfold indices refreshEntryIndices
  dsimp only
  erw [segments_eq X Q m stored.segments,loadedEntry_eq]

end CompressorRecords.PortRefresh.Readback

end VPVNP
end Computability
end OAI
