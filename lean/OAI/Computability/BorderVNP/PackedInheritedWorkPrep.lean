import OAI.Computability.BorderVNP.PackedInheritedWorkPrepFrame
import OAI.Computability.BorderVNP.PackedInheritedWorkPrepTransport
import OAI.Computability.BorderVNP.PackedBankPublicSubdivisionEpoch
import OAI.Computability.BorderVNP.PackedBankInheritedScalarCapacity

/-! # The work and extent computed at every true leaf of an outer compilation -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary.Compilation

open Cover Crossing BorderVNP.Epoch BorderVNP.Epoch.Round Shortening Shortening.Adaptive Shortening.PublicCapacity
open Packing Packing.PhysicalEpochs Packing.Inherited Packing.Inherited.WorkWords Diagonal.ExternalSew Diagonal.ExternalSew.FieldExport
open VPVNP.VerifierNetwork (Frame)
open scoped Classical BorderVNP.Epoch.Cube
attribute [local instance] portFintype
set_option maxHeartbeats 1800000
set_option maxRecDepth 2200
set_option backward.isDefEq.respectTransparency false

variable {D m : ℕ} [NeZero D] {K P : Type} [Field K] [Fintype P] {bits : P → ℕ}
    {e : PaidIdentity K D m} {S : SiteSchedule e} {shape : ℕ → Shape}
    {start T t w : ℕ} {budget V E cap : ℕ → ℕ}
    {deep : S.floor+1+S.drop*T ≤ start} {ht : t<T} {endShape : shape (t+1) = ⟨V S.rounds,E S.rounds⟩}
    {nodes : ∀ i : Fin S.rounds, S.source.Node S.last (S.high (offset S start t)) V E w S.fanIn i}
    (A : Compilation (bits := bits) deep ht budget V E cap w endShape nodes)

local notation "stagePins" => S.source.StatePins S.last (S.high (offset S start t)) V E w
local notation "outer" => Pins S start shape w
local notation "child" => WithWidths (outer t) (Shape.sites (shape t)) w
local notation "leafPins" => WithWidths (stagePins 0) (V 0) w
local notation3 "leafData" => Cover.AddressCircuit.ProductSlots (Fintype.card (Cube D)) (S.level (offset S start t) 0+1) ⊕ ↥(S.source.catalog 0)

variable (hv : V 0 = ((shape t).subdivide ⌈S.budget/S.radius⌉₊).sites) {n : ℕ} (p : WorkWords.Ports n) (fit : V 0 ≤ 2^w)

/-- The true batched subdivision, with the inherited work and its updated extent at each
scheduled site. The two static port arrays are shared by all children. -/
noncomputable def widthPre : Frame (Fin (fan S) × child) (Fin (fan S) × leafPins) :=
  Prep.batch (s := shape t) (V := V 0) (E := E 0) (w := w) (k := fan S) (Old := outer t)
    (B := leafData) ⌈S.budget/S.radius⌉₊ hv p fit A.pre

theorem widthPre_size : (A.widthPre hv p fit).size ≤ A.pre.size + 1 + fan S*Prep.charge (V 0) (E 0) n w :=
  Prep.batch_size (s := shape t) (V := V 0) (E := E 0) (w := w) (k := fan S) (Old := outer t)
    (B := leafData) ⌈S.budget/S.radius⌉₊ hv p fit A.pre

variable (y : Fin (fan S) → WithWidths (Pins S start shape w t) (shape t).sites w → Bool)

/-- Geometric pins from this common pass are the previously compiled subdivision pins. -/
theorem widthPre_geo (i : Fin (fan S)) (j : stagePins 0) :
    (A.widthPre hv p fit).eval (Function.uncurry y) (i,.inl j) = A.pre.eval (fun z => y z.1 (.inl z.2)) (i,j) :=
  Prep.batch_geo (s := shape t) (V := V 0) (E := E 0) (w := w) (k := fan S) (Old := outer t)
    (B := leafData) ⌈S.budget/S.radius⌉₊ hv p fit A.pre (Function.uncurry y) i j

variable (rows : A.epoch.F.SiteRows)
variable (c : Fin (fan S) → Admissible (Good (S := S) (start := start) (bits := bits) (shape := shape) (w := w) budget) t)
variable (old : ∀ i, Site.Programs (c i).val.pack.layout)
variable (port : WorkWords.Ports (rows.nPort 0))
local notation3 (prettyPrint := false) "a" => (A.epoch.run c).flat

/-- Attached exterior arguments have the same integer site address after the actual
subdivision. Their constant widths and zero padding also carry into its named leaves. -/
theorem widthPre_ports
    (portOK : ∀ i, port.Reads (c i).val.pack.layout (c i).val.rows.site (rows.ports 0))
    (i : Fin (fan S)) :
    port.Reads (a i).val.placed.pack.layout (a i).val.names.sites (rows.ports 0) := by
  have loc (z : Port (fan S) P t) :
      ((a i).val.names.sites ((a i).val.placed.pack.layout.attach z)).val =
        ((c i).val.rows.site ((c i).val.pack.layout.attach z)).val := by
    let atRow (u : Inner S start t V E cap w P bits 0) := (u.val.names.sites (u.val.placed.pack.layout.attach z)).val
    exact (congrArg atRow (congrFun (A.returned c).leaves i)).trans ((A.input c).originalSiteRow i z)
  exact ⟨fun z => ((portOK i).attach z).trans (loc z).symm,(portOK i).size,(portOK i).hole⟩

/-- The complete geometric result on the real named child. -/
theorem widthPre_assigned (geo : ∀ i, y i ∘ Sum.inl = (c i).val.words) (i : Fin (fan S)) :
    (fun j => (A.widthPre hv p fit).eval (Function.uncurry y) (i,.inl j)) = (a i).val.words := by
  have hc : (fun z : Fin (fan S) × outer t => y z.1 (.inl z.2)) = childWords c := by
    funext z
    exact congrFun (geo z.1) z.2
  funext j
  rw [A.widthPre_geo hv p fit y i j,hc]
  exact congrFun (A.epoch.initial c i) j

/-- Physical readback of both augmented pre-frame columns on every child of the actual
compiled epoch. The same bound and same fixed gate program handle all admissible tuples. -/
theorem widthPre_covers (geo : ∀ i, y i ∘ Sum.inl = (c i).val.words)
    (previous : ∀ i, WorkWords.Covers (c i).val.rows.site (fun v => (old i v).program.size) (assignedColumn true) (y i))
    (portOK : ∀ i, port.Reads (c i).val.pack.layout (c i).val.rows.site (rows.ports 0))
    (width : ∀ j, port.width j < 2^w)
    (room : ∀ i v, (A.epoch.installedPrivatePrograms rows c old i v).program.size < 2^w)
    (i : Fin (fan S)) (b : Bool) :
    WorkWords.Covers (a i).val.names.sites
      (fun v => let s := (A.epoch.installedPrivatePrograms rows c old i v).program; if b then s.size else s.work)
      (assignedColumn b) (fun j => (A.widthPre hv port fit).eval (Function.uncurry y) (i,j)) := by
  let g := A.pre.eval (fun z => y z.1 (.inl z.2))
  let x := Sum.elim (Function.uncurry y) g
  let readOld := Prep.prevPin (Old := outer t) (s := shape t) (V := V 0) (E := E 0) (w := w)
    (B := leafData) i
  let ep := Prep.endPin (s := shape t) (Old := outer t) (V := V 0) (E := E 0) (w := w)
    (B := leafData) i
  let prev := Frame.initial (Sum.inl (β := Bool) ∘ readOld)
  let aug := (constants _).eval x
  have oldRead : WorkWords.Covers (c i).val.rows.site (fun v => (old i v).program.size) prev aug :=
    (previous i).of_bits (fun r j => by
      rw [show prev.eval aug (r,j) = aug (.inl (readOld (r,j))) from Frame.initial_eval ..]
      rw [show aug = Sum.elim x id from constants_eval x]
      exact (Frame.initial_eval (fun z : Fin (shape t).sites × Fin w => (Sum.inr (z.1,true,z.2) : child))
        (y i) (r,j)).symm)
  have sub := A.installedWork_covers rows c old i hv prev aug oldRead
  have hc : (fun z : Fin (fan S) × outer t => y z.1 (.inl z.2)) = childWords c := by
    funext z
    exact congrFun (geo z.1) z.2
  have saved : (fun j => g (i,j)) = (a i).val.words := by
    dsimp only [g]
    rw [hc]
    exact A.epoch.initial c i
  let placed := (a i).val.placed
  let dir := (a i).val.names
  have ready : Shortening.PublicEndpoints.Represents placed.pack.layout dir.sites dir.cables dir.dummy (x ∘ ep) := by
    have eq : x ∘ ep = ((a i).val.words ∘ Sum.inr) ∘ Sum.inr := by
      funext j
      exact congrFun saved (.inr (.inr j))
    rw [eq]
    exact (a i).property.reads.geometry.names
  have hp := A.widthPre_ports rows c port portOK i
  have out := Prep.cell_covers ⌈S.budget/S.radius⌉₊ hv readOld ep port fit placed.pack.layout dir.sites dir.cables dir.dummy
    (rows.ports 0) x (A.epoch.installedPrivatePrograms rows c old i) sub ready hp width (room i) b
  apply out.of_bits
  intro r j
  simp only [assignedColumn,Frame.initial_eval,column,Frame.select_eval]
  exact Prep.batch_width (s := shape t) (B := leafData) ⌈S.budget/S.radius⌉₊ hv port fit A.pre
    (Function.uncurry y) i b r j

/-- The actual per-tile bank budget before subdivision pays for the extent of every
new leaf, including the previous tape and all of its new incident wires. -/
theorem widthPre_room {B : ℕ}
    (within : ∀ i, SiteCap (c i).val.route (Subdivision.publicProgramData (old i)) true B)
    (bound : 1040*(1+3*Fintype.card (Option (allowedMoves (Cube D) S.budget) ×
      Fin (hopCount S.budget S.radius)))*B < 2^w) (i : Fin (fan S)) (v) :
    (A.epoch.installedPrivatePrograms rows c old i v).program.size < 2^w := by
  let leaf := A.epoch.view 0 ((A.epoch.run c).flat i)
  let pr := A.epoch.installedPrivatePrograms rows c old i
  let data := Subdivision.publicProgramData pr
  let tile := fun u => productAddress (S.level (offset S start t) 0) (leaf.site u)
  have cap := A.epoch.installedPrivatePrograms_bank_within rows c old true B within i (tile v)
  have loaded := InheritedBank.payload_incoming_le leaf.pack.layout data.prior data.payload v (fun u => tile u = tile v) rfl
  have size : (pr v).program.size ≤ data.payload v+incoming leaf.pack.layout v :=
    Nat.add_le_add (Nat.le_add_right _ _) (pr v).size.le
  exact size.trans_lt ((loaded.trans ((Nat.le_add_left _ 1).trans cap)).trans_lt bound)

end PackedHistoryCircuit.Normalized.EnrichedOuter.Boundary.Compilation

end BorderVNP
end Computability
end OAI
