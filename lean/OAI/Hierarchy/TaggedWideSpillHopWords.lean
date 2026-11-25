import OAI.Hierarchy.TaggedWireDatedTurnStart
import OAI.Hierarchy.ProtocolRAMTurnShelf
import OAI.Hierarchy.TaggedWireShelfReads
import OAI.Hierarchy.ProbeBroadcastReadout

namespace OAI
/-! # Dated turn coordinates for each occurrence and its gathered bit -/

noncomputable section
set_option quotPrecheck false
namespace Hierarchy.ProtocolRAMTurnShelf
open Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing Classical
variable {N n sites slots W : ℕ} (col : Fin N→Fin 7→ℕ) (real : Fin n ↪ Fin N)

/-- Erasing zero-width records preserves the public scatter location of
every live record. -/
def restrictedLive : Live (col ∘ real) ↪ Live col where
  toFun u:=⟨real u.val,u.property⟩
  inj' _ _ h:=Subtype.ext (real.injective (congrArg Subtype.val h))

theorem entry_restrict (cover : ∀i,col i 4≠0→i∈Set.range real)
    (put : Live col ↪ Seats sites slots) (f : Fin 5) (a : Seats sites slots) :
    entry (W:=W) col put f a=entry (col ∘ real) ((restrictedLive col real).trans put) f a := by
  classical
  by_cases present : a∈Set.range put
  · obtain ⟨u,rfl⟩:=present
    obtain ⟨i,hi⟩:=cover u.val u.property
    let v : Live (col ∘ real):=⟨i,by change col (real i) 4≠0;rw [hi];exact u.property⟩
    have e : restrictedLive col real v=u:=Subtype.ext hi
    have ea : ((restrictedLive col real).trans put) v=put u:=congrArg put e
    rw [entry_live,←ea,entry_live]
    change (col u.val _:Word W)=(col (real i) _:Word W)
    rw [hi]
  · rw [entry_blank _ _ _ _ present,entry_blank]
    rintro ⟨u,rfl⟩
    exact present ⟨restrictedLive col real u,rfl⟩

end Hierarchy.ProtocolRAMTurnShelf

namespace Hierarchy.WireTelescope
open LinearAlgebra.SpectralBooks SiteTensor ChordGraph AdaptiveProbe
open scoped Classical
variable {S n m h : ℕ} (old : Fin n→Chord S) (edge : Fin m→Chord S)
    (route : Fin n→List (Fin m)) (bits : Fin n→ℕ) (ord : Fin h≃Σi,Fin (route i).length)
local notation "idx" => NativeSlot.allocation route bits ord
local notation "mass" => routeLoad route bits

def datedHopPort (i : Fin n) (u : Fin (route i).length) (j : Fin (bits i)) (b : Bool) (s : Fin S)
    (loc : (rowGraph edge).vertex ((route i).get u) b=s) : (bitGraph (rowGraph edge) mass).Port s :=
  let key:=idx ⟨⟨i,j⟩,u⟩
  have address : key.1=(route i).get u:=NativeSlot.allocation_edge route bits ord _
  ⟨(key,b),by cases b <;> simpa [bitGraph,PortGraph.vertex,address] using loc⟩

theorem datedHopPort_edge (i : Fin n) (u : Fin (route i).length) (j : Fin (bits i)) (b : Bool)
    (s : Fin S) (loc : (rowGraph edge).vertex ((route i).get u) b=s) :
    (datedHopPort edge route bits ord i u j b s loc).1.1.1=(route i).get u :=
  NativeSlot.allocation_edge route bits ord _

theorem datedHopPort_offset (i : Fin n) (u : Fin (route i).length) (j : Fin (bits i)) (b : Bool)
    (s : Fin S) (loc : (rowGraph edge).vertex ((route i).get u) b=s) :
    (datedHopPort edge route bits ord i u j b s loc).1.1.2.val=NativeSlot.start route bits ord i u+j.val :=
  NativeSlot.allocation_value route bits ord i u j

theorem datedTurn_bit (i : Fin n) (u : Fin (route i).length) (j : Fin (bits i)) (b : Bool) (s : Fin S)
    (loc : (rowGraph edge).vertex ((route i).get u) b=s)
    (x : BitState (bitGraph (rowGraph old) bits) s) (y : BitState (bitGraph (rowGraph edge) mass) s) :
    readTurn (rowGraph edge) (rowGraph old) route bits idx ⟨i,j⟩ s (x,y) (.inr (u.val,b))=
      y (datedHopPort edge route bits ord i u j b s loc) := by
  let key:=idx ⟨⟨i,j⟩,u⟩
  have within : u.val<(placedRoute route bits idx ⟨i,j⟩).length := by simp [placedRoute]
  have get : (placedRoute route bits idx ⟨i,j⟩).get ⟨u.val,within⟩=key := by simp [placedRoute,key]
  have atSite : (bitGraph (rowGraph edge) mass).vertex key b=s :=
    (datedHopPort edge route bits ord i u j b s loc).2
  simp only [readTurn,dite_eq_left within,get,dite_eq_left atSite]
  apply congrArg y
  apply Subtype.ext
  exact congrArg (fun k => (k,b)) get

/-- A component of the spill matrix is the low part of the original dated
chord. Its own rows still have their genuine same-chord mixed-radix prefix. -/
theorem datedSpill_chord {K n : ℕ} (ends : Fin n→Chord K) (width : Fin n→ℕ) (carried active : Widths K)
    (same : installedWidths ends width=active) (s : Fin K) (z : State (carried+active) s)
    (p : (bitGraph (rowGraph ends) width).Port s) :
    rowBits ends width (cast (congrArg (fun V=>State V s) same.symm) (splitPortState carried active s z).2) p=
      (z (sourcePort ends width p)).val.testBit
        (TaggedShorterCommonScan.earlier (NamedAperture.key ends) width p.1.1.1.val
          (NamedAperture.key ends p.1.1.1)+p.1.1.2.val) := by
  let : Nonempty (Fin K) := ⟨s⟩
  subst active
  rw [←NamedAperture.offset ends width p.1.1,NamedAperture.rowBit_datum]
  exact Probe.split_selector_bit carried (installedWidths ends width) s z (sourcePort ends width p)
    (NamedAperture.sourceBit ends width p.1.1)

end Hierarchy.WireTelescope

end

end OAI
