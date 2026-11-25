import OAI.Computability.NearSquareRoot.InterchangeROMStageRoles

/-! # Typed register sets for the rectangle stage's literal frame -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStage.Frame
open Interchange Interchange.StageLedger

/-- Logical indices underlying the frame's ordinal parameters and incidence mask. -/
structure Realization (g : Frame) where
  rank : ℕ
  rect : Fin (boxes g) → Rectangle (Fin (labels g))
  sel : Bool → Fin rank → Fin (labels g)
  minor_length : ∀ s, (minor g s).length = rank
  minor_get : ∀ s (i : Fin rank), (minor g s)[i.val]? = some (sel s i).val
  incident_iff : ∀ s (v : Fin (labels g)) (b : Fin (boxes g)),
    incident g s v.val b.val = true ↔ v ∈ if s then (rect b).destinations else (rect b).sources

namespace Realization

variable {g : Frame} (r : Realization g)

def endpointCode {s : Bool} (e : Endpoint r.rect s) : Role := endpoint e.1.val e.2.val.val

def queryEndpointCode {s : Bool} (p : Fin (queries g) × Endpoint r.rect s) : Role :=
  queryEndpoint p.1.val p.2.1.val p.2.2.val.val

def termCode {s : Bool} (p : Fin (queries g) × RankTerm r.rect s (r.sel s)) : Role :=
  rankTerm p.1.val p.2.1.val (p.2.2.elim 0 (fun b => b.val.val+1))

/-- The native register type at each of the eleven gate boundaries. -/
def Boundary : ℕ → Type
  | 0 => Fin (labels g)
  | 1 => Fin (labels g) ⊕ Endpoint r.rect false
  | 2 => Fin (labels g) ⊕ (Fin (queries g) × Endpoint r.rect false)
  | 3 => Fin (labels g) ⊕ (Fin (queries g) × Fin (boxes g))
  | 4 => (Fin (labels g) ⊕ (Fin (queries g) × Fin (boxes g))) ⊕
      (Fin (queries g) × RankTerm r.rect true (r.sel true))
  | 5 => (Fin (labels g) ⊕ (Fin (queries g) × Fin (boxes g))) ⊕ (Fin (queries g) × Fin r.rank)
  | 6 => (Fin (labels g) ⊕ (Fin (queries g) × Fin (boxes g))) ⊕
      (Fin (queries g) × RankTerm r.rect false (r.sel false))
  | 7 => (Fin (labels g) ⊕ (Fin (queries g) × Fin (labels g))) ⊕ (Fin (queries g) × Fin (boxes g))
  | 8 => (Fin (labels g) ⊕ (Fin (queries g) × Fin (labels g))) ⊕
      (Fin (queries g) × Endpoint r.rect true)
  | 9 | 10 => Fin (labels g) ⊕ Endpoint r.rect true
  | _+11 => Fin (labels g)

def labelCode (v : Fin (labels g)) : Role := label v.val
def boxCode (p : Fin (queries g) × Fin (boxes g)) : Role := rectangle p.1 p.2
def rankCode (p : Fin (queries g) × Fin r.rank) : Role := rankRow p.1 p.2
def queryCode (p : Fin (queries g) × Fin (labels g)) : Role := queryLabel p.1 p.2

/-- The ordinal tuple that a native register occupies in the running bank. -/
def code : (n : ℕ) → r.Boundary n → Role
  | 0 => labelCode
  | 1 => Sum.elim labelCode r.endpointCode
  | 2 => Sum.elim labelCode r.queryEndpointCode
  | 3 => Sum.elim labelCode boxCode
  | 4 => Sum.elim (Sum.elim labelCode boxCode) r.termCode
  | 5 => Sum.elim (Sum.elim labelCode boxCode) r.rankCode
  | 6 => Sum.elim (Sum.elim labelCode boxCode) r.termCode
  | 7 => Sum.elim (Sum.elim labelCode queryCode) boxCode
  | 8 => Sum.elim (Sum.elim labelCode queryCode) r.queryEndpointCode
  | 9 | 10 => Sum.elim labelCode r.endpointCode
  | _+11 => labelCode

end Realization
end InterchangeROMStage.Frame

end NearSquareRoot
end Computability
end OAI
