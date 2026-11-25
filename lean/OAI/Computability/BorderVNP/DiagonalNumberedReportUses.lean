import OAI.Computability.BorderVNP.CubePhysicalReportLedger
import OAI.Computability.BorderVNP.DiagonalNativeNumbering
import OAI.Computability.BorderVNP.DiagonalNumberedTape

/-! # Numbering the original unary occurrences in a processor's assigned cells -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Diagonal.CellEntries

open Crossing Shortening Shortening.Adaptive DiagonalTallyCellReports
open BorderVNP.Cube.Physical
open scoped Classical

/-- Row-major original leaf and copy labels name precisely one of the
recursive mathematical slots for each grammar parameter and exponent bit. -/
def originalReportSlots {Param : Type} (fan depth copies B : ℕ) :
    Fin copies × (Fin (fan^depth) × (Param × Fin B)) ≃ PowerSlot (Port fan (Fin copies × Unit) depth) Param B where
  toFun z := ((portEquiv fan (Fin copies × Unit) depth).symm (z.2.1,z.1,()),z.2.2)
  invFun i := let old := portEquiv fan (Fin copies × Unit) depth i.1; (old.2.1,old.1,i.2)
  left_inv z := by simp
  right_inv i := by
    rcases i with ⟨t,w⟩
    let index := portEquiv fan (Fin copies × Unit) depth
    change (index.symm ((index t).1,(index t).2.1,()),w) = (t,w)
    have eta : ((index t).1,(index t).2.1,()) = index t := by
      rcases index t with ⟨j,i,⟨⟩⟩
      rfl
    rw [eta,index.symm_apply_apply]

/-- Restrict an enumeration by the current owner while retaining the
independent original copy index. The target owner is checked on every slot. -/
def numberedOwnedSlots {C U V Team : Type*} (slots : C × U ≃ V) (owner : U → Team)
    (current : Team) (readOwner : V → Team) (same : ∀ c u, readOwner (slots (c,u)) = owner u) :
    C × {u // owner u=current} ≃ {i // readOwner i=current} where
  toFun a := ⟨slots (a.1,a.2.val),(same a.1 a.2.val).trans a.2.property⟩
  invFun i := let p := slots.symm i.val; (p.1,⟨p.2,(same p.1 p.2).symm.trans
    ((congrArg readOwner (slots.apply_symm_apply i.val)).trans i.property)⟩)
  left_inv a := by apply Prod.ext <;> simp
  right_inv i := Subtype.ext (slots.apply_symm_apply i.val)

variable {fan T copies R B H U : ℕ} {Param Gadget : Type} [Fintype Param]
    (count : fan^T*copies=R+1) (param : Param ≃ Fin H) (scalar : Gadget ≃ Fin U)

local notation "batch" => SewnTape.teamNumber fan T copies R count
local notation "source" => originalReportSlots (Param := Param) fan T copies B
local notation "nums" => numberSlot (b := B) batch param

/-- The actual three-axis numerical encoding used by the residue reader. -/
def numberedOriginalReportSlots :
    Fin copies × (Fin (fan^T) × (Param × Fin B)) ≃ PowerSlot (Fin (R+1)) (Fin H) B :=
  (source).trans nums

/-- Finite enumeration of the native row-major nested batch labels. -/
noncomputable local instance numberedInputTeams {f n c : ℕ} : Fintype (Port f (Fin c × Unit) n) :=
  Replay.batchFinite f (Fin c × Unit) n

variable {D : ℕ} {P : Type} {bits : P → ℕ} {N : Network D P bits} {tags : N.Tables (Entry Param Gadget)}
  (words : PowerWords (Port fan (Fin copies × Unit) T) Param Gadget B N tags)
  (z : PowerSites.LocalEdges N) (x : PowerSites.LocalPorts N)
  {l : ReportLayout} (reports : List (ReportCell l))
  (owner : (Fin (fan^T) × (Param × Fin B)) → Fin (R+1)) (current : Fin (R+1))
  (readOwner : PowerSlot (Fin (R+1)) (Fin H) B → Fin (R+1))
  (sourceRows : UseOccurrence reports ≃ Fin copies × {u // owner u=current})
  (same : ∀ c u, readOwner (numberedOriginalReportSlots count param (c,u)) = owner u)

local notation "encoded" => numberedOriginalReportSlots (B := B) count param
local notation "numbered" => words.number batch param scalar

/-- Chronological physical uses, with their processing-team filter, in the
same slot coordinates as the genuinely numbered power tally. -/
noncomputable def numberedReportSource :
    UseOccurrence reports ≃ {i // readOwner i = current} :=
  sourceRows.trans (numberedOwnedSlots encoded owner current readOwner same)

/-- The integer descriptor of each true native use has the numbered grammar
coordinate and exactly the weight of its own physical path bit. -/
theorem numberedReportSource_pair
    (agree : ∀ u : UseOccurrence reports, let a := sourceRows u
      let s := source (a.1,a.2.val)
      occurrencePair reports u = ((param a.2.val.2.1).val,if words.localUse z x s.1 s.2.1 s.2.2 then 2^s.2.2.val else 0))
    (u : UseOccurrence reports) :
    let i := (numberedReportSource count param reports owner current readOwner sourceRows same u).val
    occurrencePair reports u = (i.2.1.val,if (numbered).localUse z x i.1 i.2.1 i.2.2 then 2^i.2.2.val else 0) := by
  let a := sourceRows u
  let w := source (a.1,a.2.val)
  change occurrencePair reports u = ((param w.2.1).val,if (numbered).localUse z x (batch w.1) (param w.2.1) w.2.2 then 2^w.2.2.val else 0)
  rw [PowerWords.number_localUse,Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  exact agree u

end Diagonal.CellEntries

end BorderVNP
end Computability
end OAI
