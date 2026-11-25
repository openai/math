import OAI.Hierarchy.ProtocolRAMSinkData
import OAI.Hierarchy.ProtocolRAMReserveUse
import OAI.Hierarchy.ProtocolRAMPacked

namespace OAI
/-! # Native reserve-scatter and route-reporter input records -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM AdaptiveProbe
open scoped Classical Fin.CommRing BigOperators

variable {w r edges : ℕ} {I J : Type*} [Fintype I] [Fintype J]
variable {core : I→List (Fin edges)} {center : J→List (Fin edges)}

namespace Sink

/-- The three immutable tables are checked in the actual pre-reconciliation memory.
The remaining hypotheses describe extents, word size and expression reads only. -/
structure Before (s : Sink r edges) (m : Memory w) (e : Fin r≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→ℕ) : Prop where
  directory : RouteSettlement.Directory s.banks m e ci cj
  owners : Owners s.owners edges m
  kindEnd : s.banks.kind.base+s.banks.kind.size ≤ s.banks.reserved.base
  indexEnd : s.banks.index.base+s.banks.index.size ≤ s.banks.reserved.base
  ownerReserve : s.owners.base+s.owners.size ≤ s.banks.reserved.base
  ownerWidth : s.owners.base+s.owners.size ≤ s.banks.width.base
  inputs : (RouteSettlement.words s.banks).Fits w s.source
  source : s.source+2*r<2^w
  width : s.banks.width.base+edges ≤ s.source
  wide : 3<w
  fields : (packed s.owners (RouteSettlement.fields s.banks s.geometry)).Fits w s.table
  table : s.table+8*edges<2^w
  destination : s.destination+9*edges<2^w
  apart : s.table+8*edges ≤ s.destination ∨ s.destination+9*edges ≤ s.table

end Sink

namespace Whole

/-- The actual address and value reads required for the reserve pass. The supply
bound is checked per physical resource, including every repeated chronological debit. -/
structure Reconciliation {n count : ℕ} (s : Sink r edges) (a : ReserveUse.Archive) (reserve : ℕ)
    (site : Fin n→Fin count) (debit : Fin n→ℕ) (e : Fin r≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→Fin count) (m : Memory w) : Prop where
  archive : ReserveUse.Mounted a s.banks reserve site debit m
  ports : s.Before m e ci (fun j=>(cj j).val)
  usedSize : count ≤ s.banks.used.size
  reserveSize : count ≤ s.banks.reserved.size
  funded : ∀ i : Fin count,(∑ j,if site j=i then debit j else 0)≤reserve
  word : reserve<2^w

end Whole
end Hierarchy.ProtocolRAM.Calendar

end OAI
