import OAI.Computability.BorderVNP.DiagonalRoutedSourceReports
import OAI.Computability.BorderVNP.RoutingISASignedPrepRange
import OAI.Computability.BorderVNP.FiniteEvaluatorRouteScheduleOwners
import OAI.Computability.BorderVNP.CubeRouteCanonicalSchedule

/-! # The signed packet's chosen receiver at the native group RAM

For every true selector tuple, the published cable and delivery table drives
the actual conditional-mean label pass. The selected coordinate and all stored
row lengths are taken from the same broadcast. The numeric team at a cell is
then exactly the owner used by its routed signed report, including empty rows.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Crossing _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.MeanChoice Cube.GroupWeights Cube.LabelIndex Cube.Tally
open CubeHeaderInstall CubeArena TeamContraction TeamContraction.JointHeader LocalRow Transmission
open VPVNP.BurstRAM
open private loads_congr from OAI.Computability.BorderVNP.CubePhysicalGreedyTally
open private canonicalRead from OAI.Computability.BorderVNP.CubeTeamOwnedScheduledWords
open private actualMinimum from OAI.Computability.BorderVNP.CubeRouteCanonicalSchedule
open scoped Classical

variable {D w R : ℕ} {P A : Type} [Fintype A] {bits : P → ℕ} (N : Network D P bits)
    (ar : CubeArena.Layout) (cell : N.Site → Fin ar.cells) (recv : A → Fin ar.cells) (size : A → ℕ)
    {D₀ : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {pub : Arg → Word w} {base : ℕ}
    {slotted : Memory w} (f : BroadcastFrame) (old : Fin 81 → Word w)
    (fresh gates outputs width off ell controls : ℕ) (mac : TeamOpcode.Macros w 8) (reg : Bank w)
    (G : List Bool) (claims : List (List Bool)) (pad X : ℕ)
    (raw : Broadcast ar.n ar.header.d ar.header.cap)
local notation3 (prettyPrint := false) "mem" => Packing.Directory.ISA.publish slotted (pub 0).val base (D₀.directory pp lp)
local notation3 (prettyPrint := false) "frame" => (pub 0).val
local notation3 (prettyPrint := false) "dir" => LabelIndex.layout frame (readings mem)
variable (room : PinnedRawInput (ar := ar) (D := D₀) (pp := pp) (lp := lp) (pub := pub) (slotted := slotted) (base := base)
    f old fresh gates outputs width off ell controls G claims pad raw R X)
local notation3 (prettyPrint := false) "number" => finCongr room.cells.symm
local notation3 (prettyPrint := false) "labels" =>
  meanPackedLabel N cell recv size ((List.finRange (dir).cells).map (number).symm) ar.n ar.header.d
    ((Nat.succ_pos 1).trans_le room.alphabet)
local notation3 (prettyPrint := false) "owns" => greedyOwner R ar.b ar.s labels recv size

set_option maxHeartbeats 900000 in
/-- Every receiving cell's physical least-loaded team agrees with the exact signed
source report for the same true routed assignment. The label directory need only
give a placement of the genuine network rows, so unused slots are permitted. -/
theorem pinned_routed_owner_word
    (edgeOrd : N.CrossingEdge cell ↪ Fin (dir).cableCount) (dataOrd : A ↪ Fin (dir).deliveryCount)
    (traffic : RowPlacement (networkRows N cell recv size) (fromTables dir (readings mem) room.labels.endpoints)
      number (edgeOrd.sumMap dataOrd))
    (z : Returns (.seq LabelIndex.directoryProgram NativeIntervals.prepare) pub mac reg mem)
    (q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owns)
    (spells : (show ar.header.cap=declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s by
      rw [room.geometry]; rfl) ▸ raw = broadcast ar.b ar.s q.1) :
    let axis := Fin.ofNat (ar.n+1) (readCode (ar.n+1) raw.1)
    let input := powerHeaderImage ar f.dst (readings z.val.2.2)
    ∀ c : Fin ar.cells, (ar.receivingOwner frame axis R input c.val).val =
      routedOwnerWord ar owns labels q c.val := by
  intro axis input c
  have pos : 0 < ar.header.d := (by decide : 0 < 2).trans_le room.alphabet
  have cap : ar.header.cap=declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s := by rw [room.geometry]; rfl
  have valid := (actualMinimum q.1 raw cap spells).1
  obtain ⟨ix,counts⟩ := canonicalRead q.1 raw cap spells
  have axisEq : axis = chosen ar.b ar.s q.1 := by
    apply Fin.ext
    exact (Nat.mod_eq_of_lt valid.1).trans ix
  obtain ⟨_,_,out,first,_,_,_,decoded⟩ := labelBoot_pinned pub f ar old fresh gates outputs width off ell
    mac reg mem G claims pad raw room.boot room.geometry room.frameSpace room.copied pos room.blocks
    room.bank room.arena room.labels
  obtain rfl : out=z.val.2.2 := (first.unique_of_deterministic (by decide) z.property).2.2
  obtain ⟨_,endRegs,endMem,_,_,read⟩ := decoded.complete valid
  have alphabetFit : ar.alphabet < 2^w := by
    have big : ar.alphabet ≤ ar.alphabet^2 := by rw [pow_two]; exact Nat.le_mul_of_pos_right _ (pow_pos pos _)
    have h := room.arena
    obtain ⟨_,_,_,_,_,_,_,_⟩ := ar.writer_order
    omega
  let wl := weightLayout ar frame axis.val
  have image := groupImage_pinned pub mac f ar old fresh G.length gates outputs width off ell reg mem room.boot
    z.property room.labels room.arena alphabetFit room.cells pos axis raw (.ofWords endRegs endMem) read
  let decl : LengthDeclaration ar.n ar.header.d := (axis,fun p j => readCode (ar.header.cap+1) (raw.2 p j))
  have weights (j : Fin ar.header.d) :
      wl.weight input j.val = declarationWeight ar.header.blocks ar.b ar.K ar.h decl labels recv size j.val := by
    rw [image.weight_eq j]
    simp only [declarationWeight,dite_eq_left j.isLt,Fin.eta]
    apply congrArg (fun v => TeamNative.scaledWeight (incidentWidth ar.header.blocks ar.K ar.h decl j) v
      (groupRaw (ar.header.blocks*(ar.h*ar.b)) axis j))
    exact directory_incoming_eq N cell recv size number traffic (l := wl) room.cells.symm pos axis j
  have lab : directoryLabel (l := wl) («dir» := dir) (before := readings mem) room.cells.symm pos
      room.labels.endpoints ar.n c = labels c := by
    exact decoded_tableCodes N cell recv size dir (readings mem) room.labels.endpoints number traffic ar.n ar.header.d pos c
  have symbol : wl.symbol input c.val = (labels c axis).val :=
    (image.symbol_eq c).trans (congrArg (fun a : Label (ar.n+1) ar.header.d => (a axis).val) lab)
  have eqDecl : decl = Scatter.Assignment.Routed.trueDeclaration ar.b ar.s q.1 := Prod.ext axisEq counts
  rw [routedOwnerWord_at]
  change (TeamNative.owner R (wl.weight input) (wl.symbol input c.val)).val = _
  rw [symbol,show (labels c axis).val = (labels c (chosen ar.b ar.s q.1)).val by rw [axisEq]]
  apply congrArg Fin.val
  apply congrArg firstMinimum
  apply loads_congr
  intro j hj
  exact (weights ⟨j,hj.trans (labels c (chosen ar.b ar.s q.1)).isLt⟩).trans
    (congrArg (fun z => declarationWeight ar.header.blocks ar.b ar.K ar.h z labels recv size j) eqDecl)

/-- The caller can choose the label and the routed selector before any processor
returns. Its cell ordering is the fixed canonical enumeration of the original
network's cells. Only the physical row placement depends on the returned RAM. -/
theorem pinned_static_owner_word
    (edgeOrd : N.CrossingEdge cell ↪ Fin (dir).cableCount) (dataOrd : A ↪ Fin (dir).deliveryCount)
    (traffic : RowPlacement (networkRows N cell recv size) (fromTables dir (readings mem) room.labels.endpoints)
      number (edgeOrd.sumMap dataOrd))
    (z : Returns (.seq LabelIndex.directoryProgram NativeIntervals.prepare) pub mac reg mem)
    (positive : 0 < ar.header.d) :
    let label := meanPackedLabel N cell recv size (List.finRange ar.cells) ar.n ar.header.d positive
    let owner := greedyOwner (blocks := ar.header.blocks) (K := ar.K) (h := ar.h) R ar.b ar.s label recv size
    ∀ q : NativeAssignments.Routed (b := ar.b) (s := ar.s) owner,
      (show ar.header.cap=declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s by
        rw [room.geometry]; rfl) ▸ raw = broadcast ar.b ar.s q.1 →
      let axis := Fin.ofNat (ar.n+1) (readCode (ar.n+1) raw.1)
      let input := powerHeaderImage ar f.dst (readings z.val.2.2)
      ∀ c : Fin ar.cells, (ar.receivingOwner frame axis R input c.val).val = routedOwnerWord ar owner label q c.val := by
  have asc {v w : ℕ} (h : v=w) : (List.finRange w).map (finCongr h).symm = List.finRange v := by
    subst w
    simp
  have certified := pinned_routed_owner_word N ar cell recv size f old fresh gates outputs width off ell controls
    mac reg G claims pad X raw room edgeOrd dataOrd traffic z
  have ordering : (List.finRange (dir).cells).map (number).symm = List.finRange ar.cells := asc room.cells.symm
  let result (lab : Fin ar.cells → Label (ar.n+1) ar.header.d) : Prop :=
    ∀ q : NativeAssignments.Routed (b := ar.b) (s := ar.s) (greedyOwner R ar.b ar.s lab recv size),
      (show ar.header.cap=declarationCap ar.n ar.header.d ar.header.blocks ar.b ar.h ar.s by rw [room.geometry]; rfl) ▸
        raw = broadcast ar.b ar.s q.1 → ∀ c : Fin ar.cells,
      (ar.receivingOwner frame (Fin.ofNat (ar.n+1) (readCode (ar.n+1) raw.1)) R
        (powerHeaderImage ar f.dst (readings z.val.2.2)) c.val).val =
        routedOwnerWord ar (greedyOwner R ar.b ar.s lab recv size) lab q c.val
  have same : labels = meanPackedLabel N cell recv size (List.finRange ar.cells) ar.n ar.header.d positive :=
    congrArg (fun cs => meanPackedLabel N cell recv size cs ar.n ar.header.d positive) ordering
  exact (congrArg result same).mp certified

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
