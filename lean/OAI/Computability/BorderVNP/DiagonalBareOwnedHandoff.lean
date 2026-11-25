import OAI.Computability.BorderVNP.DiagonalNativeOwnerBankObserved
import OAI.Computability.BorderVNP.RoutingISASignedPrepInputCut

/-! # Carrying the observed transmission into the original native owned scan -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP.BurstRAM RoutingISA RoutingISA.Evaluator RoutingISA.Evaluator.SignedPrep RoutingISA.Transmission
open RoutingISA.CompactMachine CellMacro.Generator BorderVNP.Cube BorderVNP.Cube.Physical Routing
open scoped Classical

variable {R n w : ℕ} (ar : CubeArena.Layout)
    {gen : Fragment IO} {id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ}
    (U : Fin (R+1) → PinStart gen n w) (a : ∀ u, (U u).Prefix id)
    (H : Fin (R+1) → TeamHistory w)
local notation3 (prettyPrint := false) "V(" u ")" => (U u).visited (a u)
local notation3 (prettyPrint := false) "F" => PinStart.ownedVisits (ar:=ar) U a

variable (pub : ∀ u, (U u).pub=(H u).pub)
    (macEq : ∀ u, RoutingISA.CompactMachine.install gen n (U u).routines=(H u).macros)
    (routed : ∀ u, (H u).history.val.2=((U u).visited (a u)).routing.val.2)

private theorem runAt {p p' : Arg → Word w} {q q' : TeamOpcode.Macros w 8} {bs bs' : Bank w} {m m' : Memory w}
    {code : Code} {events : List (TeamRAM.Event w)} {last : Bank w} {saved : Memory w}
    (hp : p=p') (hq : q=q') (hs : (bs,m)=(bs',m')) (run : Runs p q code bs m events last saved) :
    Runs p' q' code bs' m' events last saved := by
  obtain rfl := hp
  obtain rfl := hq
  obtain ⟨rfl,rfl⟩ := Prod.mk.inj hs
  exact run

include pub macEq routed in
/-- The installer recorded in a complete native preparation is a true run
from the public transition's exact returned registers and memory. -/
theorem installed_on_bare (u : Fin (R+1)) :
    ∃ es, Runs (H u).pub (H u).macros (CubeConstants.install id) (H u).history.val.2.1 (H u).history.val.2.2
      es ((F).initialRegs u) ((F).input u) := by
  refine ⟨(V(u)).constants.val.1,?_⟩
  exact runAt (pub u) (macEq u) (routed u).symm (V(u)).constants.property

/-- Relabeling the inputs of a joint owned scan along equal functions
preserves every chronological event and both of its output arrays. -/
private theorem ownedHistory_transport
    {p p' : Fin (R+1) → Arg → Word w} {m m' : Fin (R+1) → TeamOpcode.Macros w 8}
    {b b' : Fin (R+1) → Bank w} {h h' : Fin (R+1) → Memory w}
    (pubEq : p=p') (macEq : m=m') (regsEq : b=b') (memEq : h=h') (z : OwnedRuns ar p m b h) :
    ∃ z' : OwnedRuns ar p' m' b' h', ownedHistory ar p' m' b' h' z'=ownedHistory ar p m b h z := by
  subst p'; subst m'; subst b'; subst h'
  exact ⟨z,rfl⟩

include pub macEq routed in
/-- The canonical constant table installer used by the physical owned
equivalence reaches exactly the state of the original chronological
preparation. The resulting joint owned run carries every native event. -/
theorem bare_owned_after_install
    (canonical : ∀ u, Returns (CubeConstants.install id) (H u).pub (H u).macros (H u).history.val.2.1 (H u).history.val.2.2) :
    let p := fun u => (H u).pub
    let m := fun u => (H u).macros
    let b := fun u => (canonical u).val.2.1
    let h := fun u => (canonical u).val.2.2
    ∃ z : OwnedRuns ar p m b h, ownedHistory ar p m b h z=F := by
  intro p m b h
  have states (u : Fin (R+1)) : (V(u)).constants.val.2=(canonical u).val.2 := by
    obtain ⟨es,run⟩ := installed_on_bare ar U a H pub macEq routed u
    let actual : Returns (CubeConstants.install id) (H u).pub (H u).macros (H u).history.val.2.1 (H u).history.val.2.2 :=
      ⟨(es,(F).initialRegs u,(F).input u),run⟩
    have empty : (canonical u).val.1.flatMap TeamRAM.Event.choices=[] := List.flatMap_eq_nil_iff.mpr fun v hv =>
      ((canonical u).property.unsigned_events (CubeConstants.install_unsigned id).1 v hv).1
    have native := (CubeConstants.install id).nativeOnly_of_unsigned (CubeConstants.install_unsigned id).1
    have same := return_eq_of_empty (H u).pub (H u).macros native (canonical u) actual empty
    exact congrArg (fun z => z.val.2) same.symm
  exact ownedHistory_transport ar (funext pub) (funext macEq) (funext fun u => congrArg Prod.fst (states u))
    (funext fun u => congrArg Prod.snd (states u)) fun u => (V(u)).owned

variable {r t d link inner : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
    {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {receive : ℕ → Fin (R+1)} {origin stride : ℕ}
    {pins : Fin (R+1) → Pins.Layout} {f : ReturnedDelivery G pin ext wire D pp lp receive origin stride H pins}
    {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ} {decl : LengthDeclaration ar.n ar.header.d}
    {group : Fin ar.header.d → Fin (R+1)} {template : DiagonalTallyPacketEmit.Frame} {count : ℕ}

include pub routed in
/-- Reuse the actual fitted scanner words, pointer layout and complete
constant table from the received wire image. The handoff into the original
tuple uses its own recorded constant-installer run. -/
theorem OwnedHandoff.onBareVisits {prior : TeamRows.Returns (Fin (R+1)) ar w}
    (old : OwnedHandoff f g src ar decl group template id count prior)
    (sameMacro : ∀ u, RoutingISA.CompactMachine.install gen n (U u).routines = (H u).macros) :
    OwnedHandoff f g src ar decl group template id count (PinStart.ownedVisits (ar:=ar) U a) := by
  refine ⟨pub,?_,old.banks,old.spacing,old.room,old.table,old.frame,old.source,old.fits,old.fields,?_⟩
  · exact sameMacro
  · exact installed_on_bare ar U a H pub sameMacro routed

end TeamContraction

end BorderVNP
end Computability
end OAI
