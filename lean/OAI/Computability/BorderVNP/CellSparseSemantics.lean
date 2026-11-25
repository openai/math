import OAI.Computability.BorderVNP.CellSparse

/-! # Semantics of a compact directory at a cell

The cell reads every required Boolean entry and counts the selected gadget positions
before any scalar is evaluated. A missing box or row rejects its assignment.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace CellSparse

/-- The two ends of every repeated interval carry the same bit. -/
def equalValid (bank : ℕ → Bool) (copies lanes : ℕ) (src dst : Port) : Prop :=
  ∀ i < copies, ∀ k < lanes, bank (src.atBit i k) = bank (dst.atBit i k)

/-- Unary zero pins give every padding bit one possible assignment. -/
def zeroValid (bank : ℕ → Bool) (copies lanes : ℕ) (p : Port) : Prop :=
  ∀ i < copies, ∀ k < lanes, bank (p.atBit i k) = false

/-- A successful local read may toggle the sign and may count one gadget position.
A false Boolean row, an absent truth-table row, or an incorrectly reported unary use
rejects the entire assignment. -/
def Factor.observe (f : Factor) (bank : ℕ → Bool) (offset copy : ℕ) : Option (Bool × Option ℕ) :=
  match f with
  | .truth wires rows =>
    if rows[word bank (wires.map (offset + ·))]? = some true then some (false, none) else none
  | .sign wires rows => rows[word bank (wires.map (offset + ·))]?.map (fun b => (b, none))
  | .gadget wires rows => rows[word bank (wires.map (offset + ·))]?.map (fun g => (false, some g))
  | .unary wire reportedUse =>
    if bank (offset + wire) = bank (reportedUse.atBit copy 0) then some (false, none) else none

/-- A factor occurrence in a particular copy of a private site description. -/
structure Occurrence where
  /-- The one-copy table whose row is read. -/
  factor : Factor
  /-- The first private bit of this box copy. -/
  offset : ℕ
  /-- Original copy number for the corresponding outer use bits. -/
  copy : ℕ
  deriving DecidableEq

/-- Expand the box metadata privately in record, copy, and factor order. -/
def Directory.occurrences (D : Directory) : List Occurrence :=
  D.records.flatMap fun r => match r with
  | .box id base copies stride => (List.range copies).flatMap fun i =>
      (D.boxes.getD id []).map (fun f => ⟨f, base + i * stride, i⟩)
  | _ => []

/-- Public rows constrain bit slots and certify that private directory references exist. -/
def Record.Valid (boxes : List (List Factor)) (bank : ℕ → Bool) : Record → Prop
  | .equal copies lanes src dst => equalValid bank copies lanes src dst
  | .zero copies lanes p => zeroValid bank copies lanes p
  | .box id _ _ _ => id < boxes.length
  | .profile copies s w hist routes => profileValid bank copies s w hist routes

/-- Read the list of sign and gadget observations, rejecting on the first absent row. -/
def Directory.observations (D : Directory) (bank : ℕ → Bool) : Option (List (Bool × Option ℕ)) :=
  D.occurrences.mapM fun occ => occ.factor.observe bank occ.offset occ.copy

/-- Each gadget position is checked against its proposed count, including positions
whose actual scalar in the finite field is zero. -/
def countsValid (bank : ℕ → Bool) (reported : List (List ℕ)) (obs : List (Bool × Option ℕ)) : Prop :=
  let ids := obs.filterMap Prod.snd
  (∀ a ∈ ids, a < reported.length) ∧
    ∀ a : Fin reported.length, ids.count a.val = word bank reported[a]

/-- Signed weight for one assignment of all ports and private wires. -/
noncomputable def Directory.weight (D : Directory) (bank : ℕ → Bool) : Int := by
  classical
  exact match D.observations bank with
  | none => 0
  | some obs => if (∀ r ∈ D.records, r.Valid D.boxes bank) ∧ countsValid bank D.reportedCounts obs then
      if (obs.map Prod.fst).foldl Bool.xor false then -1 else 1 else 0

end CellSparse

end BorderVNP
end Computability
end OAI
