import OAI.Hierarchy.ProtocolRAMReserveReconciliation

namespace OAI
/-! # Running the native reporter from the surviving reserve and role banks -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open AdaptiveProbe
open scoped Fin.CommRing Classical
noncomputable section

variable {w q d r edges : ℕ} {I J : Type*} [Fintype I] [Fintype J]
variable {core : I→List (Fin edges)} {center : J→List (Fin edges)}

def Sink.native (f : Sink r edges) (w : ℕ) :=
  RouteSettlement.reporter w f.source f.table f.destination edges r f.banks f.owners f.geometry

def Sink.clock (f : Sink r edges) :=
  RouteSettlement.ticks r f.banks +
    ((ProtocolRAM.clock []+(report f.table edges f.owners (RouteSettlement.fields f.banks f.geometry)).clock)
      +(27+117*edges))

def Sink.output (f : Sink r edges) (m : Memory w) (e : Fin r ≃ RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→ℕ) :=
  finalMemory f.table f.destination edges f.owners [] (RouteSettlement.fields f.banks f.geometry)
    (RouteSettlement.output f.banks f.source m e ci cj)

structure Sink.Mounted (f : Sink r edges) (m : Memory w) (e : Fin r≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→ℕ) : Prop where
  directory : RouteSettlement.Directory f.banks m e ci cj
  inputs : (RouteSettlement.words f.banks).Fits w f.source
  sourceFits : f.source+2*r<2^w
  sourceRoom : f.banks.width.base+edges≤f.source
  wide : 3<w
  available : ∀ j,RouteSettlement.actual f.banks.used m (cj j)≤RouteSettlement.actual f.banks.reserved m (cj j)
  owners : Owners f.owners edges (RouteSettlement.output f.banks f.source m e ci cj)
  fields : (packed f.owners (RouteSettlement.fields f.banks f.geometry)).Fits w f.table
  packedFits : f.table+8*edges<2^w
  emittedFits : f.destination+9*edges<2^w
  apart : f.table+8*edges≤f.destination ∨ f.destination+9*edges≤f.table

omit [Fintype I] [Fintype J] in
theorem Sink.exec (f : Sink r edges) (m : Memory w) (e : Fin r≃RouteOccurrence core center)
    (ci : I→ℕ) (cj : J→ℕ) (h : f.Mounted m e ci cj) :
    (f.native w).Exec m (f.output m e ci cj) f.clock := by
  intro P R K M pc reg pub exit rom data cfg start entry same
  exact RouteSettlement.reporter_exec f.banks f.source f.table f.destination f.owners f.geometry m e ci cj
    h.directory h.inputs h.sourceFits h.sourceRoom h.wide h.available h.owners h.fields h.packedFits h.emittedFits
    h.apart M pc reg pub exit rom data cfg start entry same

open scoped BigOperators
namespace Sink

omit [Fintype I] [Fintype J] in
theorem Before.mounted {n count : ℕ} {s : Sink r edges} {m : Memory w}
    {e : Fin r≃RouteOccurrence core center} {ci : I→ℕ} {cj : J→Fin count}
    (before : s.Before m e ci (fun j=>(cj j).val))
    (a : ReserveUse.Archive) (reserve : ℕ) (site : Fin n→Fin count) (debit : Fin n→ℕ)
    (archive : ReserveUse.Mounted a s.banks reserve site debit m)
    (usedSize : count ≤ s.banks.used.size) (reserveSize : count ≤ s.banks.reserved.size)
    (funded : ∀ i : Fin count,(∑ j,if site j=i then debit j else 0)≤reserve)
    (fits : reserve<2^w) :
    s.Mounted (ReserveUse.output a s.banks reserve site debit m) e ci (fun j=>(cj j).val) := by
  let h := ReserveUse.output a s.banks reserve site debit m
  have keep (x : ℕ) (lo : x<s.banks.reserved.base) : h x=m x := by
    have placed := archive.reserved
    have scratch := archive.used
    exact ReserveUse.frame a s.banks reserve site debit m x (.inl lo) (.inl (by omega)) (.inl (by omega))
  have readBank (b : Bank) (last : b.base+b.size ≤ s.banks.reserved.base) (i : Word w) : b.read h i=b.read m i :=
    keep _ ((Nat.add_lt_add_left (Nat.mod_lt i.val (Nat.two_pow_pos b.bits)) b.base).trans_le last)
  refine ⟨⟨fun i=>(readBank _ before.kindEnd _).trans (before.directory.headKind i),
    fun i=>(readBank _ before.indexEnd _).trans (before.directory.headIndex i),
    fun i=>(readBank _ before.kindEnd _).trans (before.directory.tailKind i),
    fun i=>(readBank _ before.indexEnd _).trans (before.directory.tailIndex i)⟩,
    before.inputs,before.source,before.width,before.wide,?_,?_,before.fields,before.table,before.destination,before.apart⟩
  · intro j
    obtain ⟨used,reserved⟩ := ReserveUse.reported a s.banks reserve site debit m archive (cj j)
      usedSize reserveSize (funded (cj j)) fits
    rw [used,reserved]
    exact funded (cj j)
  · intro i j
    let row := ((8*i.val+j.val : ℕ):Word w)
    let x := s.owners.base+row.val%s.owners.size
    have inside : x<s.owners.base+s.owners.size :=
      Nat.add_lt_add_left (Nat.mod_lt row.val (Nat.two_pow_pos s.owners.bits)) _
    exact (RouteSettlement.output_below s.banks s.source h e ci (fun j=>(cj j).val)
      x (inside.trans_le before.ownerWidth) before.width).trans
      ((keep x (inside.trans_le before.ownerReserve)).trans (before.owners i j))

end Sink

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
