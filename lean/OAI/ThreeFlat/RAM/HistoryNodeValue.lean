import OAI.ThreeFlat.Diagonal.TickScratchRegion
import OAI.ThreeFlat.RAM.HistoryGeneratedStore

namespace OAI
/-! # The six-word result and its stored compiled factor at an issued chronology node -/

namespace ThreeFlat.RAM.HistoryStageRoot

/-- The first four words of an eight-word selected result record are the
`HistoryBoundedJoin.Info` read by every later join. The next two are the
physical endpoint array and its length. -/
structure Result where
  stream : ℕ
  pins : ℕ
  rows : ℕ
  bits : ℕ
  ext : ℕ
  extCount : ℕ

def atResult (m : ℕ→ℕ) (p : ℕ) : Result := ⟨m p,m (p+1),m (p+2),m (p+3),m (p+4),m (p+5)⟩

end ThreeFlat.RAM.HistoryStageRoot

namespace ThreeFlat.RAM.HistoryStageBody.Physical
open Computability.VPVNP.BurstRAM PrivateRAM Diagonal.TickWorkspace
open scoped Fin.CommRing
noncomputable section
variable {F : Type*} {W : ℕ}

/-- The two S12 pointers come from the selected kind's native result.
External words are physical tick addresses, in inherited child order. -/
structure NodeValue (F : Type*) where
  pins : ℕ
  net : BitNetwork F pins
  external : ℕ
  endpoint : Fin external → ℕ
  stream : ℕ
  ext : ℕ

namespace NodeValue
variable (v : NodeValue F) (id : ((Fin 3→Bool)→F)→ℕ)

def info : HistoryStageRoot.Result :=
  ⟨v.stream,v.pins,v.net.cells,v.net.internal,v.ext,v.external⟩

/-- Only the six occupied S13 fields are read, even when inspecting a leaf.
All four columns of every generated trivalent gate remain available in S12. -/
structure Cached (u i : ℕ) (m : Memory W) : Prop where
  header : HistoryStageRoot.atResult (fun a=>(m a).val) (base u 13+8*i)=v.info
  rows : HistoryCompiledRows.Records id v.net v.stream m
  ends : ∀ j,m (v.ext+j.val)=(v.endpoint j:Word W)

end NodeValue
end
end ThreeFlat.RAM.HistoryStageBody.Physical

end OAI
