import OAI.Hierarchy.DescentPackedMatchNeighborOrder
import OAI.Hierarchy.DescentPackedMatchShape

namespace OAI
/-! # Actual accepted units at each live packed source before profiles -/
namespace Hierarchy.DescentPacking.PackedMatch.Local.Stage
open DescentSixParty DescentSixParty.StarKeys DescentStageEdgeReceipt DescentSIMDLookup PackedLocalMatch
open scoped Classical
noncomputable section
variable {F P V J : Type} [Field F] [Fintype V] [DecidableEq V] [Fintype J] [DecidableEq J]
    {d k i short a : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε : ℝ}
variable (A : GroupStage W G price ε J V k) (native : W.graph.Edge↪ℕ) (S : DescentCompiler.AtomSchedule) (ready : A.StateBounds S i)
variable (names : DescentSharedCableNames.Stage.Host J V k↪ℕ) (win : J×V→Fin (2^k)→Cell a)
    (next : (J×V)→Fin A.degree→Option (J×V)) (he : 0≤ε)
local notation "panel" => terrain (short:=short) A native S ready names win next
local notation "addr" => nativeAddress he A.stage
local notation "home" => scanHomeAt he A.stage
local notation "color" => scanColorAt he A.stage
local notation "T" => nativeTraffic W.graph W.core home
local notation "Dest" => target A native S ready names
variable (rank : (J×V)↪ℕ) (coord : Function.Injective (fun z=>(A.pos z,A.block z))) (named : A.SiteNamed rank)
    (fit : ∀u,(win (A.pos u) (A.block u)).val<2^short)
    (winner : ∀ u : W.graph.Site, (win (A.pos u) (A.block u)).val =
      1 + 2 * heap (nativeAddress he A.stage (scanHomeAt he A.stage u)).2 + (scanColorAt he A.stage u).toNat)
    (sorted : RosterSorted A next rank)

/-- The two facts about the immutable peer table are its numerical order and
correct routing of each signed source port to the corresponding old destination. -/
abbrev Routes := ∀h x (e : PackedCensus.Out W A.pos A.block h x),next h (Dest (h,x) e)=some (A.pos (W.graph.dst e.val))

private theorem live_bin_lt {r D p d : ℕ} (u : Panel r D p d) (v : Fin D) (x : Fin r)
    (active : u.peerWinner v x ≠ 0) : bin u v x < binCount r D := by
  have bounded := (first_live u v x active).2.trans_lt x.isLt
  have step : (v.val + 1) * r ≤ D * r := Nat.mul_le_mul_right _ v.isLt
  rw [Nat.add_mul, Nat.one_mul] at step
  unfold bin binCount
  omega

include fit winner in
theorem subword (h : J×V) (x : Fin (2^k)) (e : PackedCensus.Out W A.pos A.block h x)
    (route : Routes A native S ready names next) : bin (r:=2^k) (D:=A.degree) (p:=2*A.cap) (digit:=short) (panel h) (Dest (h,x) e) x<binCount (2^k) A.degree := by
  let dest : Fin A.degree := Dest (h,x) e
  let v : W.graph.Site := W.graph.dst e.val
  have hx : A.block v = x := (A.same e.val).symm.trans e.property.1.2
  have routed : next h dest = some (A.pos v) := route h x e
  have peer : (panel h).peerWinner dest x = (panel (A.pos v)).winner x := by
    change (next h dest).elim 0 (fun t => (panel t).winner x) = _
    exact congrArg (fun t : Option (J × V) => t.elim 0 (fun z => (panel z).winner x)) routed
  apply live_bin_lt (panel h) dest x
  intro vacant
  have val := congrArg Fin.val vacant
  rw [peer, ← hx, real_winner (short:=short) A native S ready names win next v (fit v), winner v] at val
  change 1 + 2 * _ + _ = 0 at val
  omega

variable (route : Routes A native S ready names next) (df : A.degree<2^short) (profile : ℕ)
local notation "s" => shape (2^k) A.degree (2*A.cap) profile

private theorem fiber_code {E V Z : Type*} [Fintype E] [Fintype V] (tag : E→Z) (v : V↪Z) (slot : E→V)
    (name : ∀e,v (slot e)=tag e) (x : V) : frequency slot x=frequency tag (v x) := by
  have same (e : E) : slot e = x ↔ tag e = v x := by
    rw [←name e, Function.Embedding.apply_eq_iff_eq]
  let equiv : {e : E // slot e = x} ≃ {e : E // tag e = v x} := Equiv.subtypeEquivRight same
  unfold frequency
  exact Fintype.card_congr equiv

private def apertureOfBins {E C U : Type} [Fintype E] [Fintype C]
    {r D p digit n : ℕ} (P : Panel r D p digit) (row : U ↪ ℕ)
    (groupOf : U → C) (geometry : Places P row groupOf) (onto : Function.Surjective groupOf)
    (groupOrder : ∀ b c : C, PositiveAperture.rank b < PositiveAperture.rank c ↔
      DescentPhysicalOrder.first row groupOf onto b < DescentPhysicalOrder.first row groupOf onto c)
    (dst : E → U) (receiverOf : E → Fin D) (blockOf : E → Fin r)
    (found : ∀ e, geometry.actor (receiverOf e) (blockOf e) = some (dst e))
    (bound : ∀ e, bin P (receiverOf e) (blockOf e) < n)
    (orig : C → ℕ) (capacity : Fin n → ℕ)
    (origCount : ∀ c, orig c = frequency (fun e : E => groupOf (dst e)) c)
    (binCountAt : ∀ b : Fin n, capacity b =
      frequency (fun e : E => bin P (receiverOf e) (blockOf e)) b.val) :
    PositiveAperture.Map orig (capacity ∘ PackedLocalMatch.position n) := by
  let tag : E → C := fun e => groupOf (dst e)
  let phys : E → ℕ := fun e => bin P (receiverOf e) (blockOf e)
  let num : Fin n ↪ ℕ := (PackedLocalMatch.position n).toEmbedding.trans Fin.valEmbedding
  let slot : E → Fin n := fun e => (PackedLocalMatch.position n).symm ⟨phys e, bound e⟩
  have num_eq (e : E) : num (slot e) = phys e :=
    congrArg Fin.val ((PackedLocalMatch.position n).apply_symm_apply ⟨phys e, bound e⟩)
  have ordered (e f : E) :
      PositiveAperture.rank (tag e) < PositiveAperture.rank (tag f) ↔
        PositiveAperture.rank (slot e) < PositiveAperture.rank (slot f) := by
    change _ ↔ num (slot e) < num (slot f)
    rw [num_eq e, num_eq f]
    exact geometry.ordered onto groupOrder (found e) (found f)
  have oldMass : orig = frequency tag := funext origCount
  have newMass : capacity ∘ PackedLocalMatch.position n = frequency slot := by
    funext j
    exact (binCountAt (PackedLocalMatch.position n j)).trans (fiber_code phys num slot num_eq j).symm
  rw [oldMass, newMass]
  exact from_occurrences (E := E) (C := C) (V := Fin n) tag slot ordered

include rank coord named fit winner sorted route df in
def aperture (c : ScanColonies he A.stage) (pf : Fin (s).pairs→Cell (s).digit) :
    PositiveAperture.Map (fun v=>Fintype.card (ThickPool T (thickList home color c) v))
      (PackedMatch.cap (inputs s A.cap (heap (addr c).2) (panel (addr c).1) pf) ∘ position (s).bins) := by
  let h : J × V := (addr c).1
  let u := panel h
  let dst : Edges A he c → W.graph.Site := fun e => W.graph.dst e.val
  let recv : Edges A he c → Fin A.degree := receiver A native S ready names he
  let block : Edges A he c → Fin (2^k) := fun e => A.block (W.graph.src e.val)
  let geom := places (short := short) (a := a) A native S ready names win next he rank coord
    named fit winner sorted h
  refine apertureOfBins (E := Edges A he c) (C := ScanColonies he A.stage) (U := W.graph.Site)
    (r := 2^k) (D := A.degree) (p := 2*A.cap) (digit := short) (n := (s).bins)
    u (originalId W.graph.Site) (home) geom (scanHomeAt_surjective he A.stage) (group_order A he)
    dst recv block ?_ ?_ (fun v : ScanColonies he A.stage => Fintype.card (ThickPool T (thickList home color c) v))
    (PackedMatch.cap (inputs s A.cap (heap (addr c).2) u pf)) (typed_capacity A he c) ?_
  · intro e
    change actor A next h (recv e) (block e) = some (dst e)
    exact (actor_iff A next coord h (recv e) (block e) (dst e)).mpr
      ⟨route h (block e) (endpoint A he e), (A.same e.val).symm⟩
  · intro e
    exact subword (short := short) (a := a) A native S ready names win next he
      fit winner h (block e) (endpoint A he e) route
  · intro b
    exact (cap_read profile A.cap (heap (addr c).2) u pf b).trans
      (physical_capacity (short := short) (a := a) A native S ready names win next he fit winner coord df c b.val)

private theorem pack_length {I : Type*} (weight : I→ℕ) (B : ℕ) (xs : List I) : (thinPacks weight B xs).length≤xs.length := by
  induction xs with
  | nil=>rfl
  | cons x xs ih=>
    rw [thinPacks];cases ps : thinPacks weight B xs with
    | nil=>simp
    | cons p rest=>rw [ps] at ih;simp only [List.length_cons] at ih ⊢;split <;> simp <;> omega

include rank coord named fit winner route df in
theorem measured_inputs (c : ScanColonies he A.stage) (pf : Fin (s).pairs→Cell (s).digit) :
    let xs:=thinPacks (live T) A.cap (thinList home color c)
    let u:=panel (addr c).1;let key:=heap (addr c).2
    xs.length≤(s).packs ∧ PackedMatch.need (inputs s A.cap key u pf)=needs (DescentPacking.amount (live T)) xs := by
  let u : Panel (2^k) A.degree (2*A.cap) short := panel (addr c).1
  let key := heap (addr c).2
  let x : Inputs (s) := inputs s A.cap key u pf
  let thin : List W.graph.Site := thinList home color c
  let xs : List (List W.graph.Site) := thinPacks (live T) A.cap thin
  have order := block_order A rank coord named
  have rows : sites u key false=thin.map A.block :=
    source_sites (short:=short) A native S ready names win next he fit winner order c false
  have lengths : (sites u key false).length=thin.length :=
    (congrArg (fun l : List (Fin (2^k)) => l.length) rows).trans (by simp only [List.length_map])
  have fits : xs.length≤(s).packs :=
    ((pack_length (live T) A.cap thin).trans_eq lengths.symm).trans (site_length u key false)
  have room (h : J×V) (b : Fin (2^k)) (e : PackedCensus.Out W A.pos A.block h b) :
      bin (panel h) (Dest (h,b) e) b<(s).bins :=
    subword (short:=short) A native S ready names win next he fit winner h b e route
  have readback : PackedMatch.need x=needs (n:=(s).packs) (DescentPacking.amount (live T)) xs := by
    funext j
    exact (need_read profile A.cap key u pf j).trans
      (pack_needs (short:=short) A native S ready names win next he fit winner s coord order df room c j)
  exact ⟨fits,readback⟩

private theorem measured_card {σ : Shape} {I C : Type*} [Fintype C] [DecidableEq C]
    (x : Inputs σ) (f : I→ℕ) (xs : List I) (orig : C→ℕ)
    (fits : xs.length≤σ.packs) (readback : PackedMatch.need x=needs (n:=σ.packs) f xs)
    (geometry : PositiveAperture.Map orig (PackedMatch.cap x ∘ position σ.bins)) :
    PackedMatch.amount x=Fintype.card (Pairs f (pack f xs orig).decisions) := by
  have replace := congrArg (fun req : Fin σ.packs→ℕ =>
    Fintype.card (PackedLocalMatch.Unit req (PackedMatch.cap x))) readback
  exact replace.trans (Holes.count f xs orig (PackedMatch.cap x) geometry fits)

include rank coord named fit winner sorted route df in
theorem live_amount (c : ScanColonies he A.stage) (pf : Fin (s).pairs→Cell (s).digit) :
    PackedMatch.amount (inputs s A.cap (heap (addr c).2) (panel (addr c).1) pf)=countIn he A c := by
  let x : Inputs (s) := inputs s A.cap (heap (addr c).2) (panel (addr c).1) pf
  let xs : List (List W.graph.Site) := thinPacks (live T) A.cap (thinList home color c)
  let f : List W.graph.Site→ℕ := DescentPacking.amount (live T)
  let orig (v : ScanColonies he A.stage) := Fintype.card (ThickPool T (thickList home color c) v)
  have actual : xs.length≤(s).packs ∧ PackedMatch.need x=needs (n:=(s).packs) f xs :=
    measured_inputs (short:=short) A native S ready names win next he rank coord named fit winner route df profile c pf
  have geometry : PositiveAperture.Map orig (PackedMatch.cap x ∘ position (s).bins) :=
    aperture (short:=short) A native S ready names win next he rank coord named fit winner sorted route df profile c pf
  exact measured_card x f xs orig actual.1 actual.2 geometry

end
end Hierarchy.DescentPacking.PackedMatch.Local.Stage

end OAI
