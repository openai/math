import OAI.Computability.BorderVNP.DiagonalSignedCommonPlacement
import OAI.Computability.BorderVNP.DiagonalPinnedDeclarationImage
import OAI.Computability.BorderVNP.RoutingISASignedAdmittedWriters

/-! # Running the signed writer from the common geometric eligibility test -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open Crossing Packing Packing.Directory VPVNP.BurstRAM TeamContraction JointHeader
open _root_.OAI.Computability.BorderVNP.Cube Cube.Physical Cube.GroupWeights Cube.LabelIndex Cube.MeanChoice Cube.Tally LocalRow
open private loads_congr from OAI.Computability.BorderVNP.CubePhysicalGreedyTally
open scoped Classical

variable {w R X : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {reg : Bank w}
  {ar : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp pp' lp' : ℕ → ℕ × ℕ} {pins : Pins.Layout}
  {slotted : Memory w} {base : ℕ} {I : Type*} [Fintype I] {host : I → Fin ar.cells}
  {id : I ↪ ℕ} {width : I → ℕ} (writer : SlottedWriter ar D pp lp pins pub slotted base host id width)
  (f : BroadcastFrame) (old : Fin 81 → Word w) (fresh gates outputs bitWidth off ell controls : ℕ)
  (G : List Bool) (claims : List (List Bool)) (pad : ℕ) (word : Broadcast ar.n ar.header.d ar.header.cap)
  (room : PinnedRawInput (ar:=ar) (D:=D) (pp:=pp) (lp:=lp) (pub:=pub) (slotted:=slotted) (base:=base)
    f old fresh gates outputs bitWidth off ell controls G claims pad word R X)
  {dim : ℕ} {P A : Type*} [Fintype A] {bits : P → ℕ}
  (N : Network dim P bits) (cell : N.Site → Fin ar.cells) (recv : A → Fin ar.cells) (size : A → ℕ)
local notation3 (prettyPrint := false) "ram" => ISA.publish slotted (pub 0).val base (D.directory pp lp)
local notation3 (prettyPrint := false) "dir" => LabelIndex.layout (pub 0).val (readings ram)
local notation3 (prettyPrint := false) "ix" => readCode (ar.n+1) word.1
local notation3 (prettyPrint := false) "axis" => Fin.ofNat (ar.n+1) ix
local notation3 (prettyPrint := false) "decl" => Prod.mk axis (fun (p : Sym2 (Fin ar.header.d)) (j : Fin (ar.n+1)) =>
  readCode (ar.header.cap+1) (word.2 p j))
local notation3 (prettyPrint := false) "hd" => (Nat.zero_lt_of_lt room.alphabet : 0 < ar.header.d)
local notation3 (prettyPrint := false) "label" => meanPackedLabel N cell recv size (List.finRange ar.cells) ar.n ar.header.d hd
local notation3 (prettyPrint := false) "wl" => weightLayout ar (pub 0).val ix
local notation3 (prettyPrint := false) "tl" => teamLayout ar R
local notation3 (prettyPrint := false) "input" m => powerHeaderImage ar f.dst (readings m)
local notation3 (prettyPrint := false) "labelTicks" => labelPrefixCost (pub 0).val (readings ram)
local notation3 (prettyPrint := false) "ticks" => ((labelTicks+publicBootCost ar f.dst)+(minimumCost ar.n+
  (GroupWeights.ticks wl+TeamNative.assignmentTicks tl+(TeamBudget.setup.slots+(R+1)*(TeamBudget.row.slots+1)+1))))+
  directoryTicks ar (pub 0).val
local notation3 (prettyPrint := false) "charge" => declarationWeight ar.header.blocks ar.b ar.K ar.h decl label recv size
local notation3 (prettyPrint := false) "group" => fun j : Fin ar.header.d => TeamNative.owner R charge j.val
local notation3 (prettyPrint := false) "owner" => fun c : ℕ => if h : c < ar.cells then group (label ⟨c,h⟩ axis) else 0

set_option maxHeartbeats 2200000 in
/-- For each permitted raw declaration, execute the physical unsigned scheduling
prefix on this pin. Every actual receiver and symbol uses the same fixed
geometric weight and least-loaded owner. The resulting signed writer receipt
retains the reference directory, including the original live zero-width slots. -/
theorem geometric_header_writers {edgeOrd : N.CrossingEdge cell ↪ Fin (dir).cableCount}
    {dataOrd : A ↪ Fin (dir).deliveryCount}
    (placed : RowPlacement (networkRows N cell recv size) (fromTables dir (readings ram) room.labels.endpoints)
      (finCongr room.cells.symm) (edgeOrd.sumMap dataOrd))
    (valid : declarationInRange word)
    (allowed : broadcastAllowed R X ar.header.blocks ar.b ar.K ar.h label recv size word)
    (ref : BankPlacement D pp' lp' I host id width) (same : ∀ k,writer.placement.key k=ref.key k) :
    ∃ es z selected, Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) reg ram es z selected ∧
      traceCost es ≤ labelTicks ∧ (∀ j<ar.publicBase,readings selected j=readings ram j) ∧
      (∀ j : Fin ar.header.d, TeamNative.owner R ((wl).weight (input selected)) j.val = group j) ∧
      (∀ c : Fin ar.cells, ar.receivingOwner (pub 0).val axis R (input selected) c.val = owner c.val) ∧
      ∃ events endReg out, ∃ W : WriterHistory ar.n (selectorWidth ar.n ar.K ar.h) pub mac reg ram events endReg out,
        ReturnedWriters ar D pp' lp' owner decl group pins W ∧
        traceCost events ≤ ticks+writerTicks (D.directory pp' lp').length ar.header.d := by
  have get (p : Returns (.seq LabelIndex.directoryProgram NativeIntervals.prepare) pub mac reg ram) :=
    pinned_allowed_iff ar f old fresh gates outputs bitWidth off ell controls G claims pad word R X room N cell recv
      size hd placed valid reg p
  obtain ⟨es,z,m,run,paid,low,_,events,endReg,out,W,report,bound⟩ :=
    admitted_writers writer f old fresh gates outputs bitWidth off ell controls G claims pad word room valid
      allowed.1 (fun {es z m} run => ((get ⟨(es,z,m),run⟩).mp allowed).2)
  let p : Returns (.seq LabelIndex.directoryProgram NativeIntervals.prepare) pub mac reg ram := ⟨(es,z,m),run⟩
  have image := pinned_declaration_image ar f old fresh gates outputs bitWidth off ell controls G claims pad word
    R X room N cell recv size hd placed valid reg p
  have read : (axis).val=ix := Nat.mod_eq_of_lt valid.1
  let W₀ := weightLayout ar (pub 0).val (axis).val
  have groups (j : Fin ar.header.d) : TeamNative.owner R (W₀.weight (input m)) j.val = group j := by
    apply congrArg firstMinimum
    apply loads_congr
    intro i hi
    have h : i<ar.header.d := hi.trans j.isLt
    exact (image.weight_eq ⟨i,h⟩).trans (by simp only [declarationWeight,dite_eq_left h]; rfl)
  have owners (c : Fin ar.cells) : ar.receivingOwner (pub 0).val axis R (input m) c.val = owner c.val := by
    change TeamNative.owner R (W₀.weight (input m)) (W₀.symbol (input m) c.val) = if h : c.val < ar.cells then group (label ⟨c.val,h⟩ axis) else 0
    rw [dite_eq_left c.isLt]
    rw [image.symbol_eq c]
    exact groups _
  have equal := writer.placement.directory_eq ref same writer.destinations
  refine ⟨es,z,m,run,paid,low,?_,owners,events,endReg,out,W,?_,?_⟩
  · simpa only [W₀,read] using groups
  · apply report.congr_tables equal ref writer.destinations
    · intro c hc
      exact owners ⟨c,hc⟩
    · funext j
      simpa only [W₀,read] using groups j
  · simpa only [←equal] using bound

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
