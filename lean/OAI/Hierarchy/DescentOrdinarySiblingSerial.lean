import OAI.Hierarchy.DescentSharedCableSiblings
import OAI.Hierarchy.DescentOrdinaryDonorOrder
import OAI.Hierarchy.DescentRankedWorld

namespace OAI
/-! # Ordinary normalized sibling serials in the physical next-stage cable order -/
namespace Hierarchy.DescentOrdinarySiblingSerial
open Computability.BorderVNP.Crossing DescentSixParty DescentSixParty.MarkedWorld DescentPhysicalOrder
open DescentHostDirectory DescentColonies DescentStageEdgeReceipt DescentPacking DescentCableDonorNames
open DescentSharedCableNames DescentSharedCableNames.Siblings
open scoped Classical BigOperators
noncomputable section
set_option maxHeartbeats 4000000
set_option Elab.async false

private theorem positive_source_number {E U : Type} [Fintype E] (t : Tape E) (src : E → U)
    (site : U ↪ ℕ) (width : E → ℕ) (e : E) (pos : 0 < width e) :
    t.sourceKey src site width e = site (src e) * pitch t.ancestry + t.ancestry e := by
  simp only [Tape.sourceKey, Function.Embedding.coeFn_mk, ite_eq_left pos, Tape.grouped, grouped_val]

private def worldKey {F P : Type} {d : ℕ} {bits : P → ℕ}
    (B : MarkedWorld F d P bits) (t : @Tape B.graph.Edge B.graph.finiteEdge)
    (siteKey : B.graph.Site ↪ ℕ) : B.graph.Edge ↪ ℕ :=
  @Tape.sourceKey B.graph.Edge B.graph.Site B.graph.finiteEdge t B.graph.src siteKey B.graph.width

private theorem consecutive_code {D P C : ℕ} (x y : Ticket D P C)
    (donor : y.donor = x.donor) (old : y.old = x.old) (role : y.rawRole = x.rawRole)
    (child : y.child.val = x.child.val + 1) : (code y).val = (code x).val + 1 := by
  simp only [DescentCableDonorNames.code_val, donor, old, role, child, Nat.add_assoc]

private def successorAt {F P : Type} {d : ℕ} {bits : P → ℕ}
    (B : MarkedWorld F d P bits) (raw : B.graph.Edge ↪ ℕ) (x y : B.graph.Edge) : Prop :=
  raw y = raw x + 1

private theorem adjacentKeys {F P : Type} {d : ℕ} {bits : P → ℕ}
    (B : MarkedWorld F d P bits) (t : @Tape B.graph.Edge B.graph.finiteEdge)
    (siteKey : B.graph.Site ↪ ℕ) (x y : B.graph.Edge)
    (xp : 0 < B.graph.width x) (yp : 0 < B.graph.width y)
    (same : B.graph.src y = B.graph.src x) (next : t.ancestry y = t.ancestry x + 1) :
    successorAt B (worldKey B t siteKey) x y := by
  unfold successorAt worldKey
  rw [@positive_source_number B.graph.Edge B.graph.Site B.graph.finiteEdge t B.graph.src siteKey B.graph.width y yp,
    @positive_source_number B.graph.Edge B.graph.Site B.graph.finiteEdge t B.graph.src siteKey B.graph.width x xp, same, next, Nat.add_assoc]

private def namedCoreAt {F P : Type} [Field F] {d : ℕ} {bits : P → ℕ}
    (B : MarkedWorld F d P bits) (siteKey : B.graph.Site ↪ ℕ)
    (raw : B.graph.Edge ↪ ℕ) (x : B.graph.Edge) : Prop :=
  @rename B.graph.Edge B.graph.finiteEdge raw x ∈ (PhysicalRename.rankedWorld B siteKey raw).core

private theorem namedCoreAt_of_mem {F P : Type} [Field F] {d : ℕ} {bits : P → ℕ}
    (B : MarkedWorld F d P bits) (siteKey : B.graph.Site ↪ ℕ)
    (raw : B.graph.Edge ↪ ℕ) (x : B.graph.Edge) (h : x ∈ B.core) :
    namedCoreAt B siteKey raw x :=
  (PhysicalRename.core_mem B (@rename B.graph.Site B.graph.finiteSite siteKey) (@rename B.graph.Edge B.graph.finiteEdge raw) x).2 h


private def physicalBase {F P I C H : Type} [Field F] [Fintype I] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
    (W : MarkedWorld F d P bits) (G : PoweredGadget F)
    (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
    (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
    (key : (W.selected G pick z hz fit pack p).graph.Site↪Key H) (flag : H→Bool) (k g q : ℕ)
    (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (affected : ∀i,q∣z i) : MarkedWorld F d P bits :=
  (coalesced (W.selected G pick z hz fit pack p) key flag k g).pieces q (repetitions W G pick z hz fit pack p key flag k g q)
    (repetition_width W G pick z hz fit pack p key flag k g q old picked affected)

private def physicalKey {F P I C H : Type} [Field F] [Fintype I] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
    (W : MarkedWorld F d P bits) (G : PoweredGadget F)
    (edge : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I))
    (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
    (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
    (key : (W.selected G pick z hz fit pack p).graph.Site↪Key H) (flag : H→Bool) (k g q : ℕ)
    (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (affected : ∀i,q∣z i)
    (site : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Site ↪ ℕ) : (physicalBase W G pick z hz fit pack p key flag k g q old picked affected).graph.Edge ↪ ℕ :=
  worldKey (physicalBase W G pick z hz fit pack p key flag k g q old picked affected)
    (ordinary W G edge pair pick z hz fit pack p key flag k g q old picked affected) site

/-- The genuine split child before physical renumbering. -/
def piece {F P I C H : Type} [Field F] [Fintype I] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
    (W : MarkedWorld F d P bits) (G : PoweredGadget F)
    (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
    (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
    (key : (W.selected G pick z hz fit pack p).graph.Site↪Key H) (flag : H→Bool) (k g q : ℕ)
    (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (affected : ∀i,q∣z i)
    (u : {a : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Edge // a ∈ (coalesced (W.selected G pick z hz fit pack p) key flag k g).core})
    (j : Fin ((repetitions W G pick z hz fit pack p key flag k g q) u.val)) : (physicalBase W G pick z hz fit pack p key flag k g q old picked affected).graph.Edge :=
  Sum.inr ⟨u, j⟩

/-- Successive offsets on one parent have consecutive global source keys. -/
theorem key_next {F P I C H : Type} [Field F] [Fintype I] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
    (W : MarkedWorld F d P bits) (G : PoweredGadget F)
    (edge : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I))
    (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
    (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
    (key : (W.selected G pick z hz fit pack p).graph.Site↪Key H) (flag : H→Bool) (k g q : ℕ)
    (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (affected : ∀i,q∣z i)
    (site : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Site ↪ ℕ) (positive : 0 < q)
    (u : {a : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Edge // a ∈ (coalesced (W.selected G pick z hz fit pack p) key flag k g).core})
    (a b : Fin ((repetitions W G pick z hz fit pack p key flag k g q) u.val)) (step : b.val = a.val + 1) :
    successorAt (physicalBase W G pick z hz fit pack p key flag k g q old picked affected)
      (physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site)
      (piece W G pick z hz fit pack p key flag k g q old picked affected u a) (piece W G pick z hz fit pack p key flag k g q old picked affected u b) := by
  let x := (piece W G pick z hz fit pack p key flag k g q old picked affected u a)
  let y := (piece W G pick z hz fit pack p key flag k g q old picked affected u b)
  let ticket := ancestryTicket W G edge pick z hz fit pack p key flag k g q old picked affected
  exact adjacentKeys (physicalBase W G pick z hz fit pack p key flag k g q old picked affected)
    (ordinary W G edge pair pick z hz fit pack p key flag k g q old picked affected) site x y positive positive rfl
    (consecutive_code (ticket x) (ticket y) rfl rfl rfl step)

/-- The physical rename carries this actual split child into the marked core. -/
theorem core_piece {F P I C H : Type} [Field F] [Fintype I] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
    (W : MarkedWorld F d P bits) (G : PoweredGadget F)
    (edge : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I))
    (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
    (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
    (key : (W.selected G pick z hz fit pack p).graph.Site↪Key H) (flag : H→Bool) (k g q : ℕ)
    (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (affected : ∀i,q∣z i)
    (site : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Site ↪ ℕ)
    (u : {a : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Edge // a ∈ (coalesced (W.selected G pick z hz fit pack p) key flag k g).core})
    (j : Fin ((repetitions W G pick z hz fit pack p key flag k g q) u.val)) :
    namedCoreAt (physicalBase W G pick z hz fit pack p key flag k g q old picked affected) site
      (physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site)
      (piece W G pick z hz fit pack p key flag k g q old picked affected u j) :=
  namedCoreAt_of_mem (physicalBase W G pick z hz fit pack p key flag k g q old picked affected) site
    (physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site)
    (piece W G pick z hz fit pack p key flag k g q old picked affected u j)
    ((DescentCableUnbundling.mem_nextCore (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph (coalesced (W.selected G pick z hz fit pack p) key flag k g).core
      (repetitions W G pick z hz fit pack p key flag k g q) q (Sum.inr ⟨u, j⟩)).2 u.property)

variable {F P I C H : Type} [Field F] [Fintype I] [DecidableEq H] {d : ℕ} {bits : P→ℕ}
variable (W : MarkedWorld F d P bits) (G : PoweredGadget F)
variable (edge : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (pair : I≃Fin (Fintype.card I))
variable (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
variable (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C)
variable (key : (W.selected G pick z hz fit pack p).graph.Site↪Key H) (flag : H→Bool) (k g q : ℕ)
variable (old : ∀e∈W.core,q∣W.graph.width e) (picked : ∀j,pick j∈W.core) (affected : ∀i,q∣z i)
variable (site : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Site ↪ ℕ)
variable {J V : Type} [Fintype J] [DecidableEq J] [Fintype V] [DecidableEq V] {age i : ℕ} {price ε : ℝ}

private def rawSerial {B : MarkedWorld F d P bits} {gadget : PoweredGadget F}
    (X : GroupStage B gadget price ε J V age) (rank : B.graph.Edge ↪ ℕ)
    (e : B.graph.Edge) (he : e ∈ B.core) : ℕ :=
  Siblings.shared X rank ⟨e, ⟨0, X.quantum_positive e he⟩⟩

private def rawLiveWire {B : MarkedWorld F d P bits} {gadget : PoweredGadget F}
    (X : GroupStage B gadget price ε J V age) (rank : B.graph.Edge ↪ ℕ)
    (S : DescentCompiler.AtomSchedule) (ready : X.StateBounds S i) (names : Stage.Host J V age ↪ ℕ)
    (e : B.graph.Edge) (he : e ∈ B.core) : ℕ :=
  (Stage.live X rank S ready names (Stage.home X (B.graph.src e))
    (.inl ⟨⟨e, rfl, rfl⟩, ⟨0, X.quantum_positive e he⟩⟩)).wire.val

private theorem rawLiveWire_eq {B : MarkedWorld F d P bits} {gadget : PoweredGadget F}
    (X : GroupStage B gadget price ε J V age) (rank : B.graph.Edge ↪ ℕ)
    (S : DescentCompiler.AtomSchedule) (ready : X.StateBounds S i) (names : Stage.Host J V age ↪ ℕ)
    (e : B.graph.Edge) (he : e ∈ B.core) :
    rawLiveWire X rank S ready names e he = rawSerial X rank e he :=
  Siblings.live_serial X rank S ready names ⟨e, ⟨0, X.quantum_positive e he⟩⟩

-- The permutation acts on the actual old edge. Its target retains the same edge
-- type and Fintype (PhysicalRename.graph). Read the ordinal of the renamed edge.
private def readNamedEdge (B : MarkedWorld F d P bits) (s : B.graph.Site ↪ ℕ)
    (r : B.graph.Edge ↪ ℕ)
    (f : ∀ e : (PhysicalRename.rankedWorld B s r).graph.Edge,
      e ∈ (PhysicalRename.rankedWorld B s r).core → ℕ)
    (e : B.graph.Edge) (he : namedCoreAt B s r e) : ℕ :=
  f (@rename B.graph.Edge B.graph.finiteEdge r e) he

private theorem readNamedEdge_congr (B : MarkedWorld F d P bits) (s : B.graph.Site ↪ ℕ)
    (r : B.graph.Edge ↪ ℕ)
    (f g : ∀ e : (PhysicalRename.rankedWorld B s r).graph.Edge,
      e ∈ (PhysicalRename.rankedWorld B s r).core → ℕ)
    (agree : ∀ e he, f e he = g e he)
    (e : B.graph.Edge) (he : namedCoreAt B s r e) :
    readNamedEdge B s r f e he = readNamedEdge B s r g e he :=
  agree (@rename B.graph.Edge B.graph.finiteEdge r e) he

private def namedSerial (B : MarkedWorld F d P bits) (s : B.graph.Site ↪ ℕ)
    (r : B.graph.Edge ↪ ℕ) {gadget : PoweredGadget F}
    (X : GroupStage (PhysicalRename.rankedWorld B s r) gadget price ε J V age) :
    ∀ e : B.graph.Edge, namedCoreAt B s r e → ℕ :=
  readNamedEdge B s r (rawSerial (B := PhysicalRename.rankedWorld B s r) X
    (@originalId B.graph.Edge B.graph.finiteEdge))

private def namedLiveWire (B : MarkedWorld F d P bits) (s : B.graph.Site ↪ ℕ)
    (r : B.graph.Edge ↪ ℕ) {gadget : PoweredGadget F}
    (X : GroupStage (PhysicalRename.rankedWorld B s r) gadget price ε J V age)
    (S : DescentCompiler.AtomSchedule) (ready : X.StateBounds S i)
    (names : Stage.Host J V age ↪ ℕ) :
    ∀ e : B.graph.Edge, namedCoreAt B s r e → ℕ :=
  readNamedEdge B s r (rawLiveWire (B := PhysicalRename.rankedWorld B s r) X
    (@originalId B.graph.Edge B.graph.finiteEdge) S ready names)

private theorem namedLiveWire_eq (B : MarkedWorld F d P bits) (s : B.graph.Site ↪ ℕ)
    (r : B.graph.Edge ↪ ℕ) {gadget : PoweredGadget F}
    (X : GroupStage (PhysicalRename.rankedWorld B s r) gadget price ε J V age)
    (S : DescentCompiler.AtomSchedule) (ready : X.StateBounds S i)
    (names : Stage.Host J V age ↪ ℕ) (e : B.graph.Edge) (he : namedCoreAt B s r e) :
    namedLiveWire B s r X S ready names e he = namedSerial B s r X e he :=
  readNamedEdge_congr B s r
    (rawLiveWire (B := PhysicalRename.rankedWorld B s r) X
      (@originalId B.graph.Edge B.graph.finiteEdge) S ready names)
    (rawSerial (B := PhysicalRename.rankedWorld B s r) X
      (@originalId B.graph.Edge B.graph.finiteEdge))
    (rawLiveWire_eq (B := PhysicalRename.rankedWorld B s r) X
      (@originalId B.graph.Edge B.graph.finiteEdge) S ready names) e he

private theorem renamedNext (B : MarkedWorld F d P bits) (s : Equiv.Perm B.graph.Site)
    (raw : B.graph.Edge ↪ ℕ) {gadget : PoweredGadget F}
    (X : GroupStage (PhysicalRename.world B s (rename raw)) gadget price ε J V age)
    (x y : B.graph.Edge)
    (hx : rename raw x ∈ (PhysicalRename.world B s (rename raw)).core)
    (hy : rename raw y ∈ (PhysicalRename.world B s (rename raw)).core)
    (src : B.graph.src x = B.graph.src y) (dst : B.graph.dst x = B.graph.dst y)
    (step : raw y = raw x + 1) :
    rawSerial X (originalId B.graph.Edge) (rename raw y) hy =
      rawSerial X (originalId B.graph.Edge) (rename raw x) hx + 1 := by
  have agrees (a b : B.graph.Edge) :
      originalId B.graph.Edge (rename raw a) < originalId B.graph.Edge (rename raw b) ↔
        raw a < raw b := by
    change (Fintype.equivFin B.graph.Edge (rename raw a)).val <
      (Fintype.equivFin B.graph.Edge (rename raw b)).val ↔ _
    rw [code_rename, code_rename]
    exact physical_lt_iff raw a b
  apply Siblings.consecutive X (originalId B.graph.Edge) (rename raw x) (rename raw y)
    (Siblings.paid_one X _ hx) (X.quantum_positive _ hy)
  · exact ⟨(PhysicalRename.src B.graph s (rename raw) x).trans
        ((congrArg s src).trans (PhysicalRename.src B.graph s (rename raw) y).symm),
      (PhysicalRename.dst B.graph s (rename raw) x).trans
        ((congrArg s dst).trans (PhysicalRename.dst B.graph s (rename raw) y).symm)⟩
  · exact Siblings.before (rename raw) raw (originalId B.graph.Edge) agrees step

private theorem fromFirst {n : ℕ} (row : Fin n → ℕ)
    (step : ∀ a b : Fin n, b.val = a.val + 1 → row b = row a + 1) (j : Fin n) :
    row j = row ⟨0, Nat.zero_lt_of_lt j.isLt⟩ + j.val := by
  obtain ⟨t, bound⟩ := j
  induction t with
  | zero => simp
  | succ t ih =>
    have ht : t < n := Nat.lt_of_succ_lt bound
    exact (step ⟨t, ht⟩ ⟨t+1, bound⟩ rfl).trans (congrArg Nat.succ (ih ht))

private theorem namedSerial_add (B : MarkedWorld F d P bits) (s : B.graph.Site ↪ ℕ)
    (r : B.graph.Edge ↪ ℕ) {gadget : PoweredGadget F}
    (X : GroupStage (PhysicalRename.rankedWorld B s r) gadget price ε J V age)
    {n : ℕ} (row : Fin n → B.graph.Edge) (marked : ∀ t, namedCoreAt B s r (row t))
    (sameSrc : ∀ a b, B.graph.src (row a) = B.graph.src (row b))
    (sameDst : ∀ a b, B.graph.dst (row a) = B.graph.dst (row b))
    (gap : ∀ a b : Fin n, b.val = a.val + 1 → successorAt B r (row a) (row b))
    (j : Fin n) :
    namedSerial B s r X (row j) (marked j) =
      namedSerial B s r X (row ⟨0, Nat.zero_lt_of_lt j.isLt⟩)
        (marked ⟨0, Nat.zero_lt_of_lt j.isLt⟩) + j.val := by
  refine fromFirst (fun t => namedSerial B s r X (row t) (marked t)) ?_ j
  intro a b h
  exact renamedNext B (rename s) r X (row a) (row b) (marked a) (marked b)
    (sameSrc a b) (sameDst a b) (gap a b h)

def serial (A : GroupStage (PhysicalRename.rankedWorld
      (physicalBase W G pick z hz fit pack p key flag k g q old picked affected) site
      (physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site)) G price ε J V age)
    (u : {a : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Edge // a ∈ (coalesced (W.selected G pick z hz fit pack p) key flag k g).core}) (j : Fin ((repetitions W G pick z hz fit pack p key flag k g q) u.val)) : ℕ :=
  namedSerial (physicalBase W G pick z hz fit pack p key flag k g q old picked affected) site
    (physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site) A
    (piece W G pick z hz fit pack p key flag k g q old picked affected u j)
    (core_piece W G edge pair pick z hz fit pack p key flag k g q old picked affected site u j)

theorem add (A : GroupStage (PhysicalRename.rankedWorld
      (physicalBase W G pick z hz fit pack p key flag k g q old picked affected) site
      (physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site)) G price ε J V age) (qpos : 0 < q)
    (u : {a : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Edge // a ∈ (coalesced (W.selected G pick z hz fit pack p) key flag k g).core}) (j : Fin ((repetitions W G pick z hz fit pack p key flag k g q) u.val)) :
    serial W G edge pair pick z hz fit pack p key flag k g q old picked affected site A u j =
      serial W G edge pair pick z hz fit pack p key flag k g q old picked affected site A u ⟨0, Nat.zero_lt_of_lt j.isLt⟩ + j.val :=
  namedSerial_add (physicalBase W G pick z hz fit pack p key flag k g q old picked affected) site
    (physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site) A
    (n := (repetitions W G pick z hz fit pack p key flag k g q) u.val)
    (fun (t : Fin ((repetitions W G pick z hz fit pack p key flag k g q) u.val)) => piece W G pick z hz fit pack p key flag k g q old picked affected u t)
    (fun (t : Fin ((repetitions W G pick z hz fit pack p key flag k g q) u.val)) => core_piece W G edge pair pick z hz fit pack p key flag k g q old picked affected site u t)
    (fun _ _ => rfl) (fun _ _ => rfl)
    (fun a b h => key_next W G edge pair pick z hz fit pack p key flag k g q old picked affected site qpos u a b h) j

/-- The first physical cable grain at its source has the initial sibling's
shared serial plus the actual child offset. -/
theorem live_add (A : GroupStage (PhysicalRename.rankedWorld
      (physicalBase W G pick z hz fit pack p key flag k g q old picked affected) site
      (physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site)) G price ε J V age) (qpos : 0 < q)
    (S : DescentCompiler.AtomSchedule) (ready : GroupStage.StateBounds A S i)
    (names : Stage.Host J V age ↪ ℕ)
    (u : {a : (coalesced (W.selected G pick z hz fit pack p) key flag k g).graph.Edge // a ∈ (coalesced (W.selected G pick z hz fit pack p) key flag k g).core}) (j : Fin ((repetitions W G pick z hz fit pack p key flag k g q) u.val)) :
    namedLiveWire (physicalBase W G pick z hz fit pack p key flag k g q old picked affected) site
    (physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site) A S ready names
      (piece W G pick z hz fit pack p key flag k g q old picked affected u j)
      (core_piece W G edge pair pick z hz fit pack p key flag k g q old picked affected site u j) =
      serial W G edge pair pick z hz fit pack p key flag k g q old picked affected site A u ⟨0, Nat.zero_lt_of_lt j.isLt⟩ + j.val :=
  (namedLiveWire_eq (physicalBase W G pick z hz fit pack p key flag k g q old picked affected) site
    (physicalKey W G edge pair pick z hz fit pack p key flag k g q old picked affected site) A S ready names
    (piece W G pick z hz fit pack p key flag k g q old picked affected u j)
    (core_piece W G edge pair pick z hz fit pack p key flag k g q old picked affected site u j)).trans
    (add W G edge pair pick z hz fit pack p key flag k g q old picked affected site A qpos u j)

end
end Hierarchy.DescentOrdinarySiblingSerial

end OAI
