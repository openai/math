import OAI.Computability.BorderVNP.DiagonalPositiveCoreReceived
import OAI.Computability.BorderVNP.DiagonalNativeJoinedRows
import OAI.Computability.BorderVNP.DiagonalNativeHistoryCell
import OAI.Computability.BorderVNP.DiagonalExternalFragmentValues
import OAI.Computability.BorderVNP.DiagonalJoinedPrivateBank

/-! # Original private banks at the actual positive program's owned sparse calls -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Physical.NativeAssignments.ReceivedRows

open VPVNP.BurstRAM Crossing Packing.CellAddresses Packing.BottomReports Packing.Inherited Site.Programs
open RoutingISA RoutingISA.Evaluator RoutingISA.CompactMachine RoutingISA.CellDispatch DiagonalTallyCellReports
open scoped Classical

variable {D C ns ne np n d blocks b h K s T : ℕ} {P Team : Type} [Fintype P]
    {bits : P → ℕ} {layout : Fin T → ReportLayout} (R : ReceivedRows layout C)
    (N : Network D P bits) (cell : N.Site → Fin C)
    (siteID : N.Site ↪ Fin ns) (edgeID : N.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (state : Site.Programs N) (owners : (Packet n d blocks → Selector n K h) → Fin d → Team)
    (slot : LiveBit N cell ↪ Slot n d blocks (h*b)) (ports : Ports bits)
    (owner : Fin ns → ℕ) (bottom : Fin C → List Bundle) (q : Routed (b:=b) (s:=s) owners)
    (raw : (c : Fin C) → Fin (externalBase N cell c (placedSize N state)) → Bool)

local notation3 "size" => placedSize N state
local notation3 "key" => (fun v => (cell v).val)
local notation3 "progs" => (fun v => (state v).program)
local notation3 "atRow" => R.assignedAt N cell siteID edgeID portID state owners slot ports owner bottom q raw
local notation3 "allRows" => R.assigned N cell siteID edgeID portID state owners slot ports owner bottom q raw
local notation3 (prettyPrint := false) "num" => (fun (u : Fin T) (i : Fin (R.cells u).length) => R.order ⟨u,i⟩)
local notation3 "supply" c => pathSupply N cell edgeID portID owners slot ports q c

private theorem castBits {m n : ℕ} (h : m=n) (a : Fin n → Bool) :
    List.ofFn (a ∘ Fin.cast h) = List.ofFn a := by
  subst n
  rfl

/-- The assignment attached to this original report cell consists of exactly
its original raw choices, including the staged bits after the cable lanes. -/
theorem assignedAt_privateBits (u : Fin T) (i : Fin (R.cells u).length) :
    List.ofFn ((atRow u i).assignment) = List.ofFn (raw (num u i)) := by
  let c := num u i
  let widths := Packing.FinalReports.bank_sizes N cell progs c
  let g := privateWires N cell size c (raw c)
  let st := privateStaging N cell size c (raw c)
  change List.ofFn (Fin.append (g ∘ Fin.cast widths.1) (st ∘ Fin.cast widths.2.1))=List.ofFn (raw c)
  rw [List.ofFn_fin_append,castBits,castBits,← List.ofFn_fin_append]
  exact congrArg List.ofFn Fin.append_castAdd_natAdd

/-- The boundary attached to the report row is the full supplied bit vector
of this very cell in the original routed assignment. -/
theorem assignedAt_boundary (u : Fin T) (i : Fin (R.cells u).length) :
    (atRow u i).boundary=List.ofFn (supply (num u i)) :=
  castBits (Packing.FinalReports.bank_sizes N cell progs (num u i)).2.2 _

/-- Recover the raw private bank width from the actual source assignment,
including cells having an empty private bank. -/
theorem assignedAt_width (u : Fin T) (i : Fin (R.cells u).length) :
    (atRow u i).privateWires=externalBase N cell (num u i) size := by
  have words := R.assignedAt_privateBits N cell siteID edgeID portID state owners slot ports owner bottom q raw u i
  simpa only [List.length_ofFn] using congrArg List.length words

variable (reports : NativeReports (R.assigned N cell siteID edgeID portID state owners slot ports owner bottom q raw))

local notation3 (prettyPrint := false) "observed" => (fun (u : Fin T) (i : Fin (R.cells u).length) =>
  (reports u).val.get (Fin.cast (((assignedRows_length (reports u)).trans (List.length_ofFn (f := atRow u))).symm) i))

variable {dim box lanes selectors symbols w order : ℕ} {id : TableEntry dim box lanes selectors symbols → ℕ}
    (S : Fin T → PositiveTeam id SparseExterior.driver order w) (p : ∀ u,(S u).Prefix)
    (team : Fin C → Fin T) (base : Fin T → ℕ)
    (table : ∀ u,OwnerTable (S u).pub ((S u).postMemory (p u)) ⟨u.val,base u,C⟩ (PositiveTeam.ownerWord team))
    (owned : ∀ u (i : Fin (R.cells u).length), team (R.order ⟨u,i⟩)=u)
local notation3 "J" => PositiveTeam.joinOwnedRows S p team base table

/-- The report checker's physical arguments before its private bit guesses.
The first equality comes from the native sparse translator at the final
typed return. The second equality identifies its original sorted packet,
the spliced binding rows and the decoded routed supply with the actual
frozen cell. These data can vary with every report and preparation. -/
structure NativeCallInputs where
  /-- Global sparse calls in the receiving team's real compact serializer. -/
  typed : Fin T → ℕ → CellInput
  /-- Actual generated cells at the particular final states of the preparations. -/
  published : ∀ u,((S u).generated (p u)).cell=typed u
  /-- The typed call from the restored original packet and its source-weight bindings. -/
  restored : ∀ u (i : Fin (R.cells u).length),
    typed u (num u i).val=⟨(atRow u i).augmented,(atRow u i).privateWires,
      (atRow u i).boundary++(observed u i).bits⟩

variable (X : NativeCallInputs R N cell siteID edgeID portID state owners slot ports owner bottom q raw reports S p)

include owned X in
/-- Locate the original row using the global owner word in the true final
dispatch table, then read its exact cell input on its receiving team. -/
theorem joined_cell_at (u : Fin T) (i : Fin (R.cells u).length) :
    (J).cells (num u i)=⟨(atRow u i).augmented,(atRow u i).privateWires,
      (atRow u i).boundary++(observed u i).bits⟩ := by
  rw [PositiveTeam.joined_owned_input,owned u i,X.published]
  exact X.restored u i

include owned X in
/-- Each actual positive private input has exactly as many digits as the
original source at that global cell number. -/
theorem joined_width (c : Fin C) : ((J).cells c).privateWires=externalBase N cell c size := by
  obtain ⟨⟨u,i⟩,rfl⟩ := R.order.surjective c
  exact (congrArg CellInput.privateWires (R.joined_cell_at N cell siteID edgeID portID state owners slot ports owner
    bottom q raw reports S p team base table owned X u i)).trans
      (R.assignedAt_width N cell siteID edgeID portID state owners slot ports owner bottom q raw u i)

local notation3 (prettyPrint := false) "widths" => R.joined_width N cell siteID edgeID portID state owners slot ports owner bottom q raw reports
  S p team base table owned X

include owned X in
/-- A bijection on all bit choices of the installed private generators and
all original raw cable/staging assignments, without checking the guards. -/
noncomputable def privateBankEquiv :
    (J).Private ≃ ((c : Fin C) → Fin (externalBase N cell c size) → Bool) :=
  (J).bankEquiv (Equiv.refl _) (fun c => externalBase N cell c size) widths

local notation3 (prettyPrint := false) "E" => R.privateBankEquiv N cell siteID edgeID portID state owners slot ports owner bottom q raw reports
  S p team base table owned X

/-- A physical inverse image contains every digit of the input raw assignment,
in its original order. -/
theorem privateBankEquiv_bits (a : (c : Fin C) → Fin (externalBase N cell c size) → Bool) (c : Fin C) :
    List.ofFn ((E).symm a c)=List.ofFn (a c) := by
  have seen (j : Fin ((J).cells c).privateWires) :=
    (J).bankEquiv_read (Equiv.refl _) (fun c => externalBase N cell c size) widths ((E).symm a) c j
  have same : (E).symm a c = a c ∘ Fin.cast (widths c) := by
    funext j
    have hj := seen j
    change (E) ((E).symm a) c (Fin.cast (widths c) j)=(E).symm a c j at hj
    rw [Equiv.apply_symm_apply] at hj
    exact hj.symm
  rw [same,castBits]

/-- The original candidate private bits and arbitrary physical report rows
give the joined input image on the genuine positive preparation endpoints.
The row numbering is precisely the compact directory's global enumeration. -/
noncomputable def reportImageOfNativeInputs : (J).ReportImage ((E).symm raw) allRows reports := by
  let number := (Equiv.sigmaCongrRight (fun u => finCongr (List.length_ofFn (f := atRow u)))).trans R.order
  have entry (u : Fin T) (i : Fin (allRows u).length) : (allRows u).get i=atRow u (Fin.cast List.length_ofFn i) :=
    List.get_ofFn _ _
  refine ⟨number,?_,?_,?_⟩
  · intro u i
    rw [entry]
    exact congrArg CellInput.directory (R.joined_cell_at N cell siteID edgeID portID state owners slot ports owner bottom q raw
      reports S p team base table owned X u (Fin.cast List.length_ofFn i))
  · intro u i
    rw [entry]
    exact (R.privateBankEquiv_bits N cell siteID edgeID portID state owners slot ports owner bottom q raw reports S p team
      base table owned X raw (number ⟨u,i⟩)).trans (R.assignedAt_privateBits N cell siteID edgeID portID state owners slot
        ports owner bottom q raw u (Fin.cast List.length_ofFn i)).symm
  · intro u i
    rw [entry]
    exact congrArg CellInput.external (R.joined_cell_at N cell siteID edgeID portID state owners slot ports owner bottom q raw
      reports S p team base table owned X u (Fin.cast List.length_ofFn i))

end Cube.Physical.NativeAssignments.ReceivedRows

end BorderVNP
end Computability
end OAI
