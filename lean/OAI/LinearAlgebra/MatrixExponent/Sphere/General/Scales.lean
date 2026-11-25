import OAI.LinearAlgebra.MatrixExponent.Sphere.Layout.Squares
import OAI.LinearAlgebra.MatrixExponent.Coloring.Vector
import OAI.LinearAlgebra.MatrixExponent.Transcript.Seats
import OAI.LinearAlgebra.MatrixExponent.Rounds.Local
import OAI.LinearAlgebra.MatrixExponent.Rounds.Contraction.Access
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Terminal
import OAI.LinearAlgebra.MatrixExponent.Sphere.Control.Initial
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Children.Correct
import OAI.LinearAlgebra.MatrixExponent.Assembly.Compute
import OAI.LinearAlgebra.MatrixExponent.Assembly.Matching
import OAI.LinearAlgebra.MatrixExponent.Sphere.General.Ballot
import OAI.LinearAlgebra.MatrixExponent.Assembly.Prepare.Parcel
import OAI.LinearAlgebra.MatrixExponent.Sphere.Print.Shows
import OAI.LinearAlgebra.MatrixExponent.Assembly.Prepare.Status
import OAI.LinearAlgebra.MatrixExponent.Sphere.Geometry.Decoding
import OAI.LinearAlgebra.MatrixExponent.Sphere.Panel.Shapes

/-! # Number of directed bundles at an input station -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Coloring Packing Finset
open scoped Classical

variable {F : Type} {a b : Wire} {h D T R g : ℕ} {W : ℝ} (P : Input F a b h D T R g W)

/-- Only these stations can meet `v` at an internal wire. -/
abbrev region (v : P.diagram.V) :=
  {w : P.diagram.V // (P.place w).2 = (P.place v).2 ∧
    (P.place w).1 ∈ insert (P.place v).1 (P.adj (P.place v).1)}

theorem region_bound (v : P.diagram.V) : Fintype.card (P.region v) ≤ (g + 1) * (100 * D) := by
  let N := insert (P.place v).1 (P.adj (P.place v).1)
  have hn : N.card ≤ g + 1 := (card_insert_le _ _).trans (Nat.add_le_add_right (P.degree _) _)
  let fiber (j : N) := {w // P.place w = (j.val, (P.place v).2)}
  let f (w : P.region v) : Σ j, fiber j :=
    ⟨⟨(P.place w.val).1, w.property.2⟩, w.val, Prod.ext rfl w.property.1⟩
  have hf : Function.Injective f := fun _ _ he => Subtype.ext (congrArg (fun x => x.2.val) he)
  calc
    _ ≤ Fintype.card (Σ j, fiber j) := Fintype.card_le_of_injective f hf
    _ = ∑ j, Fintype.card (fiber j) := Fintype.card_sigma
    _ ≤ ∑ _ : N, 100 * D := sum_le_sum fun _ _ => P.count _
    _ ≤ _ := by simpa using Nat.mul_le_mul_right (100 * D) hn

def inputBits (g D : ℕ) := Nat.clog 2 (2 * ((g + 1) * (100 * D) + 1))

/-- Reserve a direction bit and one additional remote name for the exterior. -/
theorem bundleCount (v : P.diagram.V) :
    Nonempty (Bool × Option (P.region v) ↪ B (inputBits g D)) := by
  apply Function.Embedding.nonempty_of_card_le
  rw [Fintype.card_prod, Fintype.card_bool, Fintype.card_option, Fintype.card_fin]
  exact (Nat.mul_le_mul_left 2 (Nat.add_le_add_right (P.region_bound v) 1)).trans
    (Nat.le_pow_clog (by decide) _)

theorem width_cap (v : P.diagram.V) : P.diagram.arity v < 2 ^ (Nat.clog 2 (100 * D * T + 1)) := by
  have hv : (P.diagram.arity v : ℝ) ≤ (100 : ℝ) * D * T := by
    refine le_trans ?_ (P.mass (P.place v))
    unfold push
    simpa only [ite_true] using single_le_sum
      (f := fun w => if P.place w = P.place v then (P.diagram.arity w : ℝ) else 0)
      (fun _ _ => by positivity) (mem_univ v)
  have hh : P.diagram.arity v ≤ 100 * D * T := by exact_mod_cast hv
  exact (Nat.lt_succ_of_le hh).trans_le (Nat.le_pow_clog (by decide) _)

theorem channel_cap {ℓ : ℕ} (hD : 2 * SphereScale.budget g ≤ D) :
    2 ^ (Nat.clog 2 (g + 1) + 1) ≤ D ^ (Sphere.Layout.Sharing.allocation g ℓ) + 1 := by
  have hb : 4 * (g + 1) ≤ D := by
    have h := Nat.le_mul_of_pos_right (10000000 * (1 + 4 * g)) (by omega : 0 < Routing.Private.energyConstant + 1)
    unfold SphereScale.budget at hD
    omega
  calc
    _ ≤ 4 * (g + 1) := by
      rw [pow_succ]
      have := Transcript.pow_clog_le_twice (by omega : 0 < g + 1)
      omega
    _ ≤ D := hb
    _ ≤ _ := (Nat.le_self_pow (by unfold Sphere.Layout.Sharing.allocation; omega) _).trans
      (Nat.le_add_right _ _)

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # The empty host needs no movement, labels or selectors -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Packing Finset
open scoped Classical

variable {F : Type} {x y : Wire} {h D T r g : ℕ} {W : ℝ}
  (P : Input F x y h D T r g W) [IsEmpty P.V]

theorem noStations : IsEmpty P.diagram.V := ⟨fun v => isEmptyElim (P.place v).1⟩
theorem noWires : IsEmpty P.diagram.E := ⟨fun e => isEmptyElim (P.place (P.diagram.source e)).1⟩

include P in
theorem noExterior : IsEmpty (slots x ⊕ slots y) :=
  ⟨fun i => isEmptyElim (P.place (portEnd P.diagram i)).1⟩

abbrev emptyTerm (u : ℕ) : LocalTerm F x y h u where
  V := P.V
  diagram := P.diagram
  freeze := ⟨fun _ => True, fun _ => trivial, fun e => isEmptyElim (P.place (P.diagram.source e)).1⟩
  frame := {
    place := P.place, frozen := fun _ => True, keep := fun _ => Iff.rfl
    N := P.adj, C := P.adj, ns := P.sym, cs := P.sym, sub := fun _ => Finset.Subset.refl _
    group := fun e => (P.edge e).1.symm
    edge := fun e => isEmptyElim (P.place (P.diagram.source e.val)).1
    full := fun e => isEmptyElim (P.place (P.diagram.source e)).1 }
  one v := isEmptyElim (P.place v).1
  width v := isEmptyElim (P.place v).1
  charge _ := 0
  cover v := isEmptyElim (P.place v).1
  floor v := isEmptyElim (P.place v).1

theorem emptyConcentrated (u C d ℓ : ℕ) : Concentrated P (P.emptyTerm u) C d ℓ := by
  have hW := (show 0 ≤ (univ.image P.place).card * (D : ℝ) * T by positivity).trans P.occupied
  let _ : IsEmpty (P.emptyTerm u).freeze.Fixed := ⟨fun t => isEmptyElim (P.place t.val).1⟩
  let _ : IsEmpty (P.emptyTerm u).freeze.Core := ⟨fun t => isEmptyElim (P.place t.val).1⟩
  refine ⟨?_, fun v => isEmptyElim v, fun v => isEmptyElim v, ?_, ?_, ?_, ?_, ?_⟩
  · change Fintype.card P.V ≤ _; simp
  · simp only [Fintype.card_eq_zero, Nat.cast_zero, zero_mul]; positivity
  · exact fun v => isEmptyElim v
  · simp only [univ_eq_empty, sum_empty]; positivity
  · exact fun v => isEmptyElim v
  · simp only [univ_eq_empty, sum_empty]; positivity

theorem emptyExpansion [Field F] (u C d ℓ A : ℕ) : LocalExpansion P u C d ℓ A :=
  ⟨Unit, inferInstance, fun _ => P.emptyTerm u, fun _ => 1, by simpa using Nat.one_le_pow _ 2 (by decide),
    fun _ _ => by simp, fun _ => P.emptyConcentrated ..⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

section
/-! # Identity of the stations holding named exterior bits -/

namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Raw
open Packing

variable {F : Type} {x y : Wire} {h D T g u : ℕ} {W : ℝ}
    (Q : Raw F x y h D T g W) (B : LocalTerm F x y h u) (parent : B.V → Q.V)

/-- Each original holder has one distinct final holder in its original cell. -/
structure Holders : Prop where
  location : ∀ i, let v := B.frame.place (portEnd B.diagram i)
    (parent v.1, v.2) = Q.place (portEnd Q.diagram i)
  fibers : ∀ i j, portEnd B.diagram i = portEnd B.diagram j ↔ portEnd Q.diagram i = portEnd Q.diagram j

end OAI.LinearAlgebra.MatrixExponent.Rounds.Raw
end

/-! # Locating a frozen collector by its short station name -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Coloring Assembly Sphere Surface Surface.Local Routing.Private
open Sphere.Layout (Place item)

variable {F K J : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
  {h D T b d g m ℓ H U : ℕ} {W : ℝ} (P : Input F x y h D T (d * b) g W)
  (p : P.Tools K ℓ m) (s : P.Occupied → Shape (SphereScale.probes ℓ D) b d)
  {z : P.Configuration p} (hz : (P.plant p s).Reach m (2 * g) H U z)
  {S : Scheme F} {r : S.format.obj} {portal : S.Presentation r P.diagram}
  {loc : P.Occupied ↪ B S.m × B S.h} {tone : B S.m → ℕ} {mobile : S.Vtx → Bool}
  (placed : P.Placed portal loc tone mobile)
  {β : P.Occupied ⊕ ℕ → J} {G : Record F (d * b) d P.Occupied P.grid.Seam J (B S.k)}
  (hm : Matches (P.reference p (finiteName S.k ∘ P.stationRank)).world β z G)
include placed

theorem namedKeeps (e : slots x ⊕ slots y) :
    let v := Packing.portEnd P.diagram e
    ∃ i : Place z.scene.cell, loc i.1 = ((portal.vertex v).1, (portal.vertex v).2.1) ∧
      (P.inputPorts p s hz).ports i = P.diagram.extLeft v ∧
      (P.outputPorts p s hz).ports i = P.diagram.extRight v ∧
      (hm.row i).name = some (portal.vertex v).2.2 ∧
      ∀ j, j.1 = i.1 → (hm.row j).name = (hm.row i).name → j = i := by
  intro v
  let i := P.draw p s hz e
  have pos (j : Place z.scene.cell) (w : P.diagram.V)
      (hn : (item z.scene.cell j).label.name = some w) :
      loc j.1 = ((portal.vertex w).1, (portal.vertex w).2.1) := by
    rw [← (P.reached_name p s hz (List.get_mem _ j.2) hn).2, placed.location]
  have row (j : Place z.scene.cell) :
      (hm.row j).name = (item z.scene.cell j).label.name.map (fun w => (portal.vertex w).2.2) := by
    have name : finiteName S.k ∘ P.stationRank = fun w => (portal.vertex w).2.2 := by
      funext w
      rw [Function.comp_apply, placed.name]
      exact Fin.ext (Nat.mod_eq_of_lt (portal.vertex w).2.2.isLt)
    rw [← name]
    exact (hm.represents j).name.symm
  have hn : (item z.scene.cell i).label.name = some v := P.draw_name p s hz e
  have hi : (hm.row i).name = some (portal.vertex v).2.2 := by rw [row, hn]; rfl
  refine ⟨i, pos i v hn, ?_, ?_, hi, ?_⟩
  · exact congrArg (fun a => a.elim [] P.diagram.extLeft) hn
  · exact congrArg (fun a => a.elim [] P.diagram.extRight) hn
  · intro j eq he
    rw [row j, hi] at he
    obtain ⟨w, hw, hs⟩ := Option.map_eq_some_iff.mp he
    have hl := (pos j w hw).symm.trans ((congrArg loc eq).trans (pos i v hn))
    obtain ⟨ha, hb⟩ := Prod.mk.inj hl
    have hv : w = v := portal.vertex.injective (Prod.ext ha (Prod.ext hb hs))
    exact (P.draw_eq p s hz e j (hw.trans (congrArg some hv))).symm

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-!
# Seating the input graph independently of a chart

One extra channel at a host is reserved for contacts inside that host.
A station's local number depends only on the cell containing it.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Sphere Finset
open scoped Classical

abbrev stationBits (D : ℕ) := Nat.clog 2 (100 * D + 1)
abbrev channelBits (g : ℕ) := Nat.clog 2 (g + 1)

variable {F : Type} {x y : Wire} {h D T R g m : ℕ} {W : ℝ}
  (P : Input F x y h D T R g W)

structure Seating (m : ℕ) where
  host : P.V ↪ B m
  vtx : P.diagram.V ↪ B m × B h × B (stationBits D)
  place : ∀ i, ((vtx i).1, (vtx i).2.1) = (host (P.place i).1, cellIndex h (P.place i).2)
  tape : (Print.Children.Tape m (channelBits g)).obj
  shows : Print.Children.Shows P.adj host tape
  moving : ∀ v j, tape.1 (host v) j ≠ host v → (tape.2 (host v)).2 j = true
  index : P.V → P.V → B (channelBits g)
  nav_link : ∀ v w, w ∈ insert v (P.adj v) → tape.1 (host v) (index v w) = host w

theorem seating (hm : Fintype.card P.V ≤ 2 ^ m) : Nonempty (P.Seating m) := by
  obtain ⟨host⟩ : Nonempty (P.V ↪ B m) :=
    Function.Embedding.nonempty_of_card_le (by simpa using hm)
  let adj v := insert v (P.adj v)
  have sym v w (hw : w ∈ adj v) : v ∈ adj w := by
    rcases mem_insert.mp hw with rfl | hw
    · exact mem_insert_self ..
    · exact mem_insert_of_mem (P.sym _ _ hw)
  let link (v : P.V) : ↥(adj v) ↪ B (channelBits g) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      rw [Fintype.card_coe, Fintype.card_fin]
      exact ((card_insert_le ..).trans (Nat.add_le_add_right (P.degree v) 1)).trans
        (Nat.le_pow_clog (by decide) _)))
  let A := Directory.numbered adj sym host link
  let tape : (Print.Children.Tape m (channelBits g)).obj :=
    (A.nav, fun i => (decide (i ∈ Set.range A.host), A.flags i))
  have shows : Print.Children.Shows P.adj A.host tape := by
    refine ⟨fun i => decide_eq_true_iff, A.closed, A.reciprocal, ?_⟩
    intro v w hw
    have he := A.marks v w
    simpa only [adj, mem_insert, hw.symm, false_or, tape] using he
  let seat (j : P.V × Packing.Cell h) : {i // P.place i = j} ↪ B (stationBits D) :=
    Classical.choice (Function.Embedding.nonempty_of_card_le (by
      rw [Fintype.card_fin]
      exact ((P.count j).trans (Nat.le_add_right _ _)).trans (Nat.le_pow_clog (by decide) _)))
  let number i := seat (P.place i) ⟨i, rfl⟩
  have num_eq i j (h : P.place i = j) : number i = seat j ⟨i, h⟩ := by subst j; rfl
  let f i := (A.host (P.place i).1, cellIndex h (P.place i).2, number i)
  have inj : Function.Injective f := by
    intro i j he
    simp only [f, Prod.mk.injEq] at he
    have ht := Prod.ext (A.host.injective he.1) ((cellIndex h).injective he.2.1)
    have eq := he.2.2
    rw [num_eq i _ ht, num_eq j _ rfl] at eq
    exact congrArg Subtype.val ((seat _).injective eq)
  exact ⟨⟨A.host, ⟨f, inj⟩, fun _ => rfl, tape, shows,
    fun v => Directory.numbered_moving adj sym host link (A.host v), A.index, A.nav_link⟩⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # From an ordered input dictionary to a canonical local presentation -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Packing Sphere
open scoped Classical

abbrev widthBits (D T : ℕ) := Nat.clog 2 (100 * D * T + 1)

variable {F : Type} [Field F] {a e : ℕ}

abbrev bundleScheme (read : BundleReader F a e) (m h g D T : ℕ) :=
  BundleOrder.scheme read m h (channelBits g) (stationBits D) (widthBits D T)

abbrev mobility (a e g D T : ℕ) := BundleOrder.mobile a e (channelBits g) (stationBits D) (widthBits D T)

namespace Seating
variable {x y : Wire} {h D T R g m : ℕ} {W : ℝ} {P : Input F x y h D T R g W}
  {read : BundleReader F a e} (v : P.Seating m) (o : BundleOrder P.diagram read)

local notation "S" => bundleScheme read m h g D T
local notation "G" => P.diagram
local notation "r" => 2 * D ^ 5 + 2

omit [Field F] in
private theorem linked (i : (G).E) (b : Bool) :
    let x := P.place (Restore.endpoint G i b)
    let y := P.place (Restore.endpoint G i (!b))
    x.2 = y.2 ∧ y.1 ∈ insert x.1 (P.adj x.1) := by
  obtain ⟨hb, he⟩ := P.edge i
  cases b
  · exact ⟨hb.symm, Finset.mem_insert.mpr he⟩
  · exact ⟨hb, Finset.mem_insert.mpr (he.imp Eq.symm (P.sym _ _))⟩

def schedule : o.Schedule m h (channelBits g) (stationBits D) (widthBits D T) where
  vertex := v.vtx
  flag i := decide (P.mobile i)
  nav := v.tape.1
  index i j := v.index (P.place i).1 (P.place j).1
  link i j he := by
    obtain ⟨t, b, rfl, rfl⟩ := o.peer_source he
    rw [o.station, o.station, Restore.station_tip, Restore.station_tip]
    let x := Restore.endpoint G t b
    let y := Restore.endpoint G t (!b)
    obtain ⟨hx, hx'⟩ := Prod.mk.inj (v.place x)
    obtain ⟨hy, hy'⟩ := Prod.mk.inj (v.place y)
    obtain ⟨hb, hn⟩ := linked (P := P) t b
    apply Prod.ext
    · exact (congrArg (fun i => v.tape.1 i (v.index (P.place x).1 (P.place y).1)) hx).trans
        ((v.nav_link _ _ hn).trans hy.symm)
    · exact Prod.ext (hx'.trans ((congrArg (cellIndex h) hb).trans hy'.symm)) rfl
  capacity := P.width_cap

local notation "C" => v.schedule o

def chart : P.HostChart (S) (C).tape where
  host := v.host
  block := (cellIndex h).toEmbedding
  adjacent i j he _ := ⟨v.index i j, v.nav_link i j (Finset.mem_insert_of_mem he)⟩
  reciprocal := v.shows.reciprocal

abbrev ordered := (v.chart o).normalized (C).presentation (C).directed r
abbrev next := (v.chart o).next (C).presentation (C).directed r
abbrev pres : (S).Presentation (C).tape (v.ordered o).diagram :=
  (C).presentation.toOrdered (C).directed

theorem eval : (v.ordered o).diagram.eval = P.diagram.eval :=
  P.normalize_eval _ _ _

theorem directed : (v.pres o).Directed := by
  intro i
  change (S).direction (C).tape (((C).presentation.toOrdered (C).directed).toSeating.ends i).1 = _
  rw [Scheme.Presentation.ordered_ends]
  exact (C).directed i

def mobile (z : (S).Vtx) := mobility a e g D T (((C).tape z.1).2 z.2.1) z.2.2

theorem placed : (v.ordered o).Placed (v.pres o) (v.next o).coord
    (fun i => ((v.next o).tone r i).val) (v.mobile o) :=
  (v.chart o).normalized_placed _ _ _ _ v.place (fun i => ((C).mobility i).symm)

theorem ranks : (v.ordered o).LocalRanks :=
  (v.chart o).normalized_ranks _ _ _ (by omega) (v.mobile o) v.place (fun i => ((C).mobility i).symm)

theorem location (x : (v.ordered o).Occupied) :
    (v.next o).coord x = ((v.next o).host x.val.1, cellIndex h x.val.2) := rfl

theorem parents :
    Print.Children.Shows (v.ordered o).adj (v.next o).host ((v.next o).graph, v.tape.2) := v.shows

end Seating
end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-!
# Seating before packetization

A padded span inherits its station, neighbor and direction. Thus the
schedule and mobility flags can be supplied before choosing the packet
width. Normalize the padded table in its displayed order.
-/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input.Seating
open Assembly Coloring Sphere
open scoped Classical

variable {F : Type} [Field F] {x y : Wire} {h D T R₀ g a e m : ℕ} {W : ℝ}
  {P : Input F x y h D T R₀ g W} {read : BundleReader F a e}
  (v : P.Seating m) (o : BundleOrder P.diagram read) (R : ℕ)
  (hr₀ : 0 < R) (hD : 400 * (g + 1) ≤ D) (hr : R * D ^ 2 ≤ 2 * T)

local notation "S" => Scheme.padded (bundleScheme read m h g D T) R
local notation "C" => v.schedule o
local notation "Q" => P.packetize R hr₀ hD hr
local notation "depth" => 2 * D ^ 5 + 2

private def baseChart : (Q).HostChart (S) (C).tape :=
  ⟨v.host, (cellIndex h).toEmbedding, (v.chart o).adjacent, (v.chart o).reciprocal⟩

private abbrev paddedPres : (S).Presentation (C).tape (Q).diagram :=
  (C).presentation.pad (C).directed (C).resolved R P.loopless

private theorem padDirected : (v.paddedPres o R hr₀ hD hr).Directed :=
  (C).presentation.pad_directed (C).directed (C).resolved R P.loopless

local notation "A" => v.baseChart o R hr₀ hD hr
local notation "B" => v.paddedPres o R hr₀ hD hr
local notation "dir" => v.padDirected o R hr₀ hD hr

abbrev packetOrdered := (A).normalized B dir depth
abbrev packetChart := (A).next B dir depth

local notation "orderedInput" => v.packetOrdered o R hr₀ hD hr
local notation "atlas" => v.packetChart o R hr₀ hD hr

abbrev packetPres : (S).Presentation (C).tape (orderedInput).diagram := (B).toOrdered dir

theorem packetEval : (orderedInput).diagram.eval = P.diagram.eval :=
  ((Q).normalize_eval _ _ _).trans (P.packetize_eval R hr₀ hD hr)

theorem packetDirected : (v.packetPres o R hr₀ hD hr).Directed := by
  intro i
  change (S).direction (C).tape (((B).toOrdered dir).toSeating.ends i).1 = _
  rw [Scheme.Presentation.ordered_ends]
  exact dir i

theorem packetPlaced : (orderedInput).Placed (v.packetPres o R hr₀ hD hr) (atlas).coord
    (fun i => ((atlas).tone depth i).val) (v.mobile o) :=
  (A).normalized_placed B dir depth (v.mobile o) v.place (fun i => ((C).mobility i).symm)

theorem packetRanks : (orderedInput).LocalRanks :=
  (A).normalized_ranks B dir depth (by omega) (v.mobile o) v.place (fun i => ((C).mobility i).symm)

theorem packetLocation (i : (orderedInput).Occupied) :
    (atlas).coord i = ((atlas).host i.val.1, cellIndex h i.val.2) := rfl

theorem packetParents :
    Print.Children.Shows (orderedInput).adj (atlas).host ((atlas).graph, v.tape.2) := v.shows

theorem packetMoving : ∀ w j, (atlas).graph ((atlas).host w) j ≠ (atlas).host w →
    (v.tape.2 ((atlas).host w)).2 j = true := v.moving

/-- Undo the change of budget and scale made by padding. -/
theorem packetBounds {u c d ℓ : ℕ} {Z : LocalTerm F x y h u}
    (hz : Concentrated (orderedInput) Z c d (ℓ + 1)) : Concentrated P Z (202 * c) d ℓ :=
  Concentrated.of_packetize P hr₀ hD hr
    ⟨hz.cells, hz.coreDegree, hz.fullDegree, hz.frozenCount, hz.frozenMax, hz.frozenSquare, hz.coreMax, hz.coreSum⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input.Seating
end

section
/-! # Linear label and logarithmic width bounds for ordered inputs -/

namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly

theorem widthBits_le (D T : ℕ) : widthBits D T ≤ stationBits D + Nat.clog 2 (T + 1) := by
  apply Nat.clog_le_of_le_pow
  rw [pow_add]
  exact (show 100 * D * T + 1 ≤ (100 * D + 1) * (T + 1) by ring_nf; omega).trans
    (Nat.mul_le_mul (Nat.le_pow_clog (by decide) _) (Nat.le_pow_clog (by decide) _))

def rowFactor (g D : ℕ) :=
  let e := inputBits g D
  2 ^ stationBits D * (3 + 2 ^ e * (2 * stationBits D + 3 + channelBits g + e))

private theorem linear (d k t e a : ℕ) :
    (2 + a + 2 ^ e * (k + t + 2 + d + k + e)) ≤ (3 + 2 ^ e * (2 * k + 3 + d + e)) * (1 + a + t) := by
  let n := 1 + a + t
  have h₁ : 2 + a ≤ 3 * n := by unfold n; omega
  have h₂ : k + t + 2 + d + k + e ≤ (2 * k + 3 + d + e) * n := by
    unfold n
    ring_nf
    omega
  exact (Nat.add_le_add h₁ (Nat.mul_le_mul_left (2 ^ e) h₂)).trans_eq (by unfold n; ring)

theorem bundleBits {F : Type} [Field F] {a e : ℕ} (read : BundleReader F a e)
    (m h g D T : ℕ) (he : e ≤ inputBits g D) :
    (bundleScheme read m h g D T).ℓ ≤ rowFactor g D * (1 + a + Nat.clog 2 (T + 1)) := by
  let k := stationBits D
  let d := channelBits g
  let z := inputBits g D
  let t := Nat.clog 2 (T + 1)
  change (BundleOrder.row a e d k (widthBits D T)).width ≤ _
  rw [BundleOrder.row_width]
  have hq := widthBits_le D T
  calc
    _ ≤ 2 ^ k * (2 + a + 2 ^ z * (k + t + 2 + d + k + z)) := by gcongr
    _ ≤ 2 ^ k * ((3 + 2 ^ z * (2 * k + 3 + d + z)) * (1 + a + t)) := Nat.mul_le_mul_left _ (linear ..)
    _ = _ := (mul_assoc ..).symm

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Dyadic and packet scales of the binary controller -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open SphereScale

abbrev rounded (D : ℕ) := 2 ^ Nat.clog 2 D
abbrev unitSize (g ℓ D T : ℕ) := (2 * T) / (rounded D) ^ terminalExponent g (ℓ + 1)

def threshold (g : ℕ) := 2 * budget g + 400 * (g + 1)

variable {D T g : ℕ}

theorem threshold_large (hD : threshold g ≤ D) : 2 ≤ D := by
  unfold threshold at hD
  omega

theorem threshold_packet (hD : threshold g ≤ D) : 400 * (g + 1) ≤ rounded D :=
  (Nat.le_add_left ..).trans (hD.trans (Nat.le_pow_clog (by decide) D))

theorem threshold_scales (hD : threshold g ≤ D) : 2 * budget g ≤ rounded D :=
  (Nat.le_add_right ..).trans (hD.trans (Nat.le_pow_clog (by decide) D))

theorem inputBits_round (g D : ℕ) : inputBits g D ≤ inputBits g (rounded D) := by
  unfold inputBits
  gcongr
  exact Nat.le_pow_clog (by decide) _

theorem doubled_log (T a B : ℕ) :
    B * (1 + a + Nat.clog 2 (2 * T + 1)) ≤ (2 * B) * (1 + a + Nat.clog 2 (T + 1)) := by
  have he : Nat.clog 2 (2 * T + 1) ≤ Nat.clog 2 (T + 1) + 1 := by
    apply Nat.clog_le_of_le_pow
    rw [pow_succ]
    have := Nat.le_pow_clog (by decide : 1 < 2) (T + 1)
    omega
  rw [mul_comm 2 B, mul_assoc]
  exact Nat.mul_le_mul_left _ (by omega)

theorem packet_unit {ℓ : ℕ} (hD : 2 ≤ D) (hT : (rounded D) ^ terminalExponent g (ℓ + 1) ≤ 2 * T) :
    0 < unitSize g ℓ D T ∧ T ≤ unitSize g ℓ D T * D ^ (2 * terminalExponent g (ℓ + 1)) := by
  let C := terminalExponent g (ℓ + 1)
  let a := (rounded D) ^ C
  let u := unitSize g ℓ D T
  obtain ⟨hu, _, ht⟩ := floor_units (B := a) (pow_pos (by unfold rounded; positivity) _) hT
  have hd : rounded D ≤ D ^ 2 := (Transcript.pow_clog_le_twice (by omega : 0 < D)).trans
    (by rw [pow_two]; exact Nat.mul_le_mul_right _ hD)
  have ha : a ≤ D ^ (2 * C) := by rw [pow_mul]; exact Nat.pow_le_pow_left hd C
  have hb : 2 * T ≤ 2 * (u * a) := ht.trans_eq (mul_assoc ..)
  exact ⟨hu, (show T ≤ u * a by omega).trans (Nat.mul_le_mul_left _ ha)⟩

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Agreement between the terminal records and the printer -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere SphereScale Surface Surface.Local
open scoped Classical

variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
    {g ℓ D T b d p l j : ℕ} {W : ℝ} {S : Scheme F}
    (P : Input F x y S.h D T (d * b) g W)
    {z : S.format.obj} (A : P.HostChart S z)
    (sc : Scales g ℓ D T (p ^ l) b d) (hK : Ready K ℓ D g (p ^ l) b d)
    (s : P.Occupied → Shape (probes ℓ D) b d)

local notation "kit" => P.kit sc hK
local notation "world" => P.localWorld A sc hK s
local notation "Cfg" => design S g ℓ D b d p l

theorem printSignal (pres : S.Presentation z P.diagram) {tone : B S.m → ℕ} {mobile : S.Vtx → Bool}
    (h : P.Placed pres A.coord tone mobile) (hd : pres.Directed)
    {menu : (Cfg).Menu F (B S.k) (B S.ℓ) j} (c : (world).Code (Cfg).waves menu)
    {M r t k n u j' e : ℕ}
    (U : Print.Printer F (panelKeys Cfg) (B S.k) S.m S.d S.h j M r t (Cfg).R D k n u j' e)
    (ha : d * b = M * r) (hb : d = M * t) (hm : U.menu = printMenu S menu ha hb)
    (status : (Print.Children.Header S.m S.d).obj)
    (loc : ∀ v, A.coord v = (A.host v.val.1, cellIndex S.h v.val.2))
    (parents : Print.Children.Shows P.adj A.host (A.graph, status)) :
    let f := c.frame
    let Q := P.finalSource A sc hK s f
    let left := P.inputPorts kit s f.reach
    let right := P.outputPorts kit s f.reach
    U.Signal Q left right (world).atlas (world).π f.address (world).ref f.record f.match'
      (P.panelIndex sc hK) (world).size (P.panelExt A) A.host c.tape status ∧
      Print.Keeps Q left right pres A.coord := by
  intro f Q left right
  refine ⟨?_, P.keeps kit s f.reach h⟩
  refine ⟨Nat.le_add_left _ _, rfl, rfl, ⟨_, f.layout⟩, ?_, loc, parents, c.host, ?_, ?_, fun _ _ _ _ => rfl, ?_, fun _ => rfl⟩
  · have he := f.clean.distinct
    change Distinct ((world).atlas.near (horizon _ (Cfg).waves (Cfg).waves)) _ _ at he
    simp only [horizon, Nat.sub_self, mul_zero, zero_add] at he
    exact he
  · intro i
    rw [hm]
    apply HEq.trans (cast_heq _ _)
    apply heq_of_eq
    refine (P.panel_read A sc hK s c i).trans ?_
    refine congrArg (fun z => (world).atlas.fill z i) (funext fun v => ?_)
    simp only [panelFace, Print.Printer.faces, Frame.info, f]
    congr 4
    exact Subsingleton.elim _ _
  · intro i w
    erw [← (f.match'.represents i).name]
    exact P.portsWidth kit s f.reach h hd i w
  · intro i a b w
    let j := (Layout.item f.stage.scene.cell i).label.name
    change P.external kit j ((a, b), w) =
      ((j.elim [] P.diagram.extLeft).map (bits x a), (j.elim [] P.diagram.extRight).map (bits y b))
    cases j <;> rfl

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input

namespace OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning.Trial
open Sphere.Print

variable {F : Type} [Field F] {x y : Wire} {D : Template F}
    {a H T R : ℕ} {θ L : ℝ} {b : D.Binning a H T R θ}
    {r : D.format.obj} {P : Rounds.Board F x y D.scheme.h} {p : D.Presents r P}
    (t : b.Trial p L) (q : ℕ)

theorem parents : Children.Shows (t.normal q).adj (t.atlas q).host ((t.atlas q).graph, b.status r) :=
  ⟨t.live_status q, t.closed q, (t.atlas q).reciprocal, t.edge_status q⟩

theorem directed_order : t.order.Directed := by
  unfold Scheme.Presentation.Directed
  rw [t.post.ordered_ends]
  exact t.directed

end OAI.LinearAlgebra.MatrixExponent.Assembly.Template.Binning.Trial
end

/-! # Printing a local expansion with arbitrary station mobility -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Input
open Assembly Coloring Routing.Private Sphere SphereScale Surface Surface.Local
open scoped Classical

variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
    {g ℓ D T b d p l j : ℕ} {W : ℝ} {S : Scheme F}
    (P : Input F x y S.h D T (d * b) g W)
    {z : S.format.obj} (A : P.HostChart S z)
    (sc : Scales g ℓ D T (p ^ l) b d) (hK : Ready K ℓ D g (p ^ l) b d)
    (s : P.Occupied → Shape (probes ℓ D) b d)

local notation "world" => P.localWorld A sc hK s
local notation "Cfg" => design S g ℓ D b d p l

/-- Any ordered presentation whose stations match the terminal frame
produces a weighted expansion that retains both exterior lists. -/
def localNamedRelease (pres : S.Presentation z P.diagram) {tone : B S.m → ℕ} {mobile : S.Vtx → Bool}
    (h : P.Placed pres A.coord tone mobile) (hd : pres.Directed)
    {menu : (Cfg).Menu F (B S.k) (B S.ℓ) j} (c : (world).Code (Cfg).waves menu)
    {M r t k n u e : ℕ}
    (U : Print.Printer F (panelKeys Cfg) (B S.k) S.m S.d S.h j M r t (Cfg).R D k n u (p ^ l) e)
    (ha : d * b = M * r) (hb : d = M * t) (hm : U.menu = printMenu S menu ha hb)
    (status : (Print.Children.Header S.m S.d).obj)
    (loc : ∀ v, A.coord v = (A.host v.val.1, cellIndex S.h v.val.2))
    (parents : Print.Children.Shows P.adj A.host (A.graph, status)) (hn : Nonempty P.V)
    (hM : M = chunks ℓ D) (hk : k = Sphere.Layout.Sharing.allocation g ℓ)
    (hu : u * D ^ (terminalExponent g ℓ) ≤ T)
    (hc : terminalExponent g ℓ * D * T ≤ u * U.cap) (hz : depth ℓ D g (p ^ l) (d * b) < 2 ^ e) :
    U.NamedRelease pres c.tape status ((world).eval c.frame) ℓ := by
  have sig := P.printSignal A sc hK s pres h hd c U ha hb hm status loc parents
  have bd := P.panelBounds A sc hK s c.frame
  have keep := P.namedKeeps (P.kit sc hK) s c.frame.reach h c.frame.match'
  exact sig.1.namedRelease keep hn bd sc ha hb rfl rfl hM hk hu hc hz

end OAI.LinearAlgebra.MatrixExponent.Rounds.Input
end

/-! # Common dimensions of the printer for a grouped layer -/

noncomputable section
namespace OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
open Assembly Coloring Sphere SphereScale
open scoped Classical
variable {F K : Type} [Field F] [Field K] [Algebra K F] {x y : Wire}
    {s : Rounds.Plan} {a T b d : ℕ} {θ L : ℝ}
    (P : Layer F x y) (B : P.template.Binning a s.D T (d * b) θ)

local notation "g" => ((4 * 5) ^ 300 : ℕ)

abbrev motionWidth (p l k : ℕ) :=
  let cfg := Input.design B.target g 10 s.D b d p l
  cfg.widthAt (Input.panelQuery B.target g 10 s.D b d p l k).width k cfg.waves

abbrev Printer (p l k r t z f : ℕ) :=
  let cfg := Input.design B.target g 10 s.D b d p l
  Print.Printer F (Input.panelKeys cfg) (Coloring.B B.target.k) B.target.m B.target.d B.target.h
    (P.motionWidth B p l k) (chunks 10 s.D) r t cfg.R s.D
    (Sphere.Layout.Sharing.allocation g 10) s.d (s.b * z) (p ^ l) f

variable [Fintype F] {p l k r t z f : ℕ} [ExpChar F p]
    (trials : ∀ i, B.Trial (P.presents i) L)
    (sc : Scales g 10 s.D T (p ^ l) b d) (hK : SphereScale.Ready K 10 s.D g (p ^ l) b d)
    (hF : room 10 s.D g *(2 * depth 10 s.D g (p ^ l) (d * b) + 1) < Fintype.card F)
    (U : P.Printer B p l k r t z f)

abbrev Releases := ∀ i : (P.moved B trials sc hK hF k).state,
  U.Release (P := (trials i.1.1).normal (panelRadius s.D)) (trials i.1.1).order
    i.2.tape (B.status (P.data i.1.1)) ((P.moved B trials sc hK hF k).eval i) 10

end OAI.LinearAlgebra.MatrixExponent.Rounds.Layer
end
