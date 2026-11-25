import Mathlib.Data.Fintype.BigOperators

namespace OAI
/-! # Numbered chronological node records and their two stored charges -/

namespace ThreeFlat.RAM.NavigationNodeRows
open scoped BigOperators

structure Banks where
  current : ℕ
  charges : ℕ
  nodes : ℕ
  lanes : ℕ
  perLanePairs : ℕ
  totalPairs : ℕ
  traceWork : ℕ
  unitWork : ℕ

structure Layer where
  first : ℕ
  count : ℕ
  kind : ℕ
  childCount : ℕ
  children : ℕ
  kernels : ℕ
  incident : ℕ
  info : ℕ

structure Parent where
  finalLayer : Bool
  first : ℕ
  owners : ℕ

/-- The charge pass reads only these three projections of the local physical node records. -/
structure LayerData (s : Layer) where
  child : Fin s.count → Fin s.childCount → ℕ
  halfWidth : Fin s.count → List ℕ
  motifCopies : Fin s.count → List ℕ

def ParentReads {n : ℕ} (p : Parent) (owners : Fin n → ℕ) (mem : ℕ→ℕ) : Prop :=
  p.finalLayer=false → ∀ j, mem (p.owners+j.val)=owners j

def LayerData.cost {s : Layer} (d : LayerData s) (b : Banks) (prior : ℕ→Fin 2→ℕ)
    (j : Fin s.count) (col : Fin 2) : ℕ :=
  let leaf := s.kind=0 ∧ j.val<b.lanes
  let p := if leaf then min (b.totalPairs-j.val*b.perLanePairs) b.perLanePairs else 0
  let localWork := 1+(d.halfWidth j).sum+
    (if s.kind=0 then 0 else (d.motifCopies j).sum)+p+(if leaf then b.traceWork else 0)
  (if col.val=0 then b.unitWork*localWork else p)+∑ i, prior (d.child j i) col

end ThreeFlat.RAM.NavigationNodeRows

end OAI
