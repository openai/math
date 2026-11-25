import OAI.Computability.BorderVNP.FiniteRouteNumberedImage
import OAI.Computability.BorderVNP.DiagonalSharedDeclarationCapacity
import OAI.Computability.BorderVNP.CubeTeamOwnedGroupImage

/-! # The fixed signed network's capacity predicate on arbitrary copied declarations -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Crossing VPVNP.BurstRAM _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.GroupWeights Cube.LabelIndex
open Cube.MeanChoice LocalRow CubeHeaderInstall TeamContraction TeamContraction.JointHeader Transmission
open scoped Classical

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
    (ar : CubeArena.Layout) {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {slotted : Memory w} {base : ℕ}
    (f : BroadcastFrame) (old : Fin 81 → Word w) (fresh gates outputs width off ell controls : ℕ)
    (G : List Bool) (claims : List (List Bool)) (pad : ℕ) (rawDecl : Broadcast ar.n ar.header.d ar.header.cap)
    (R X : ℕ)
    (room : PinnedRawInput (ar := ar) (D := D) (pp := pp) (lp := lp) (pub := pub) (slotted := slotted) (base := base)
      f old fresh gates outputs width off ell controls G claims pad rawDecl R X)
    {dim : ℕ} {P A : Type*} [Fintype A] {bits : P → ℕ} (N : Network dim P bits)
    (cell : N.Site → Fin ar.cells) (recv : A → Fin ar.cells) (amount : A → ℕ)
local notation3 (prettyPrint := false) "m₀" => Packing.Directory.ISA.publish slotted (pub 0).val base (D.directory pp lp)
local notation3 (prettyPrint := false) "dir₀" => LabelIndex.layout (pub 0).val (readings m₀)
local notation3 (prettyPrint := false) "index" => readCode (ar.n+1) rawDecl.1
local notation3 (prettyPrint := false) "axis" => Fin.ofNat (ar.n+1) index
local notation3 (prettyPrint := false) "decl" => (axis,fun (pair : Sym2 (Fin ar.header.d)) (j : Fin (ar.n+1)) => readCode (ar.header.cap+1) (rawDecl.2 pair j))
local notation3 (prettyPrint := false) "wl" => weightLayout ar (pub 0).val (axis).val

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1400000 in
/-- The first two public scheduling passes on an in-range raw declaration
recover the common history's original cell labels and seven-word deliveries.
This holds for every return, before checking its least coordinate or team loads. -/
theorem pinned_declaration_image (hd : 0 < ar.header.d) {edgeOrd : N.CrossingEdge cell ↪ Fin (dir₀).cableCount}
    {dataOrd : A ↪ Fin (dir₀).deliveryCount}
    (placed : RowPlacement (networkRows N cell recv amount) (fromTables dir₀ (readings m₀) room.labels.endpoints)
      (finCongr room.cells.symm) (edgeOrd.sumMap dataOrd))
    (valid : declarationInRange rawDecl) (reg : Bank w)
    (z : Returns (.seq LabelIndex.directoryProgram NativeIntervals.prepare) pub mac reg m₀) :
    PhysicalImage wl (powerHeaderImage ar f.dst (readings z.val.2.2)) ar.header.blocks ar.b ar.K ar.h decl
      (meanPackedLabel N cell recv amount (List.finRange ar.cells) ar.n ar.header.d hd) recv amount := by
  obtain ⟨_,_,last,first,_,_,_,read⟩ := labelBoot_pinned pub f ar old fresh gates outputs width off ell mac reg
    m₀ G claims pad rawDecl room.boot room.geometry room.frameSpace room.copied hd room.blocks room.bank room.arena room.labels
  obtain rfl : last=z.val.2.2 := (first.unique_of_deterministic (by decide) z.property).2.2
  obtain ⟨_,lastReg,lastMem,_,_,decoded⟩ := read.complete valid
  have fit : ar.alphabet < 2^w := by
    have low : ar.alphabet ≤ ar.alphabet^2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right _ (pow_pos hd _)
    have stop := room.arena
    obtain ⟨_,_,_,_,_,_,_,_⟩ := ar.writer_order
    omega
  have native := groupImage_pinned pub mac f ar old fresh G.length gates outputs width off ell reg m₀ room.boot
    z.property room.labels room.arena fit room.cells hd axis rawDecl (.ofWords lastReg lastMem) decoded
  exact numbered_directory_image (l := wl) («dir» := dir₀) (before := readings m₀)
    (m := powerHeaderImage ar f.dst (readings z.val.2.2)) (ep := room.labels.endpoints) (n := ar.n)
    (blocks := ar.header.blocks) (b := ar.b) (K := ar.K) (h := ar.h)
    (edgeOrd := edgeOrd) (dataOrd := dataOrd) N cell recv amount room.cells.symm placed hd decl native

set_option maxRecDepth 6000 in
set_option maxHeartbeats 1200000 in
/-- The eligible raw declarations are independent of the team, substituted
pin, and discarded external bits. The selected native state tests exactly
the common candidate predicate at every in-range header. -/
theorem pinned_allowed_iff (hd : 0 < ar.header.d) {edgeOrd : N.CrossingEdge cell ↪ Fin (dir₀).cableCount}
    {dataOrd : A ↪ Fin (dir₀).deliveryCount}
    (placed : RowPlacement (networkRows N cell recv amount) (fromTables dir₀ (readings m₀) room.labels.endpoints)
      (finCongr room.cells.symm) (edgeOrd.sumMap dataOrd))
    (valid : declarationInRange rawDecl) (reg : Bank w)
    (z : Returns (.seq LabelIndex.directoryProgram NativeIntervals.prepare) pub mac reg m₀) :
    broadcastAllowed R X ar.header.blocks ar.b ar.K ar.h
        (meanPackedLabel N cell recv amount (List.finRange ar.cells) ar.n ar.header.d hd) recv amount rawDecl ↔
      declaredMinimum rawDecl ∧ capacities (weightLayout ar (pub 0).val index) (teamLayout ar R) X
        (powerHeaderImage ar f.dst (readings z.val.2.2)) := by
  have img := pinned_declaration_image ar f old fresh gates outputs width off ell controls G claims pad rawDecl R X
    room N cell recv amount hd placed valid reg z
  have bound := declarationCapacity_iff (t := teamLayout ar R) (X := X) img
  have ix : (axis).val=index := Nat.mod_eq_of_lt valid.1
  apply and_congr_right
  intro _
  simpa only [ix, weightLayout, teamLayout] using bound.symm

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
