import OAI.Computability.BorderVNP.FiniteEvaluatorSignedRouteValue
import OAI.Computability.BorderVNP.CubeScatterReturnedOwnedFamily

/-! # The owned-group traversal inside a returned field route

Splitting a returning installer and traversal at the instruction boundary
recovers the actual intermediate registers and memory. The installer makes
no private choices, so the traversal carries the entire private tape.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CubeTriple

open BorderVNP.Cube BorderVNP.Cube.Tally RoutingISA VPVNP.BurstRAM

variable {Team F : Type*} [Fintype F] (ar : CubeArena.Layout)
variable (table : TableEntry ar.n ar.b ar.h ar.K ar.s → F)
variable {w : ℕ} {pub : Team → Arg → Word w} {mac : Team → TeamOpcode.Macros w 8}
variable {regs : Team → Bank w} {original : Team → Memory w}
variable (paths : ∀ u, Evaluator.Returns (installGroups table) (pub u) (mac u) (regs u) (original u))

private structure SplitAt (u : Team) where
  middleRegs : Bank w
  mem : Memory w
  first : List (TeamRAM.Event w)
  last : List (TeamRAM.Event w)
  events : (paths u).val.1=first++last
  installed : Runs (pub u) (mac u) (CubeDeck.install table) (regs u) (original u) first middleRegs mem
  traversed : Runs (pub u) (mac u) (TeamRows.ownedGroups ar.n ar.b ar.h ar.K ar.s) middleRegs mem last
    (paths u).val.2.1 (paths u).val.2.2

private noncomputable def splitAt (u : Team) : SplitAt ar table paths u := Classical.choice (by
  obtain ⟨s,m,es,fs,eq,first,last⟩ := Runs.seq_iff.mp (paths u).property
  exact ⟨⟨s,m,es,fs,eq,first,last⟩⟩)

/-- The returning owned traversals reached after the actual field installers.
The final registers and output RAM are the endpoints of the original programs. -/
noncomputable def splitTeams : TeamRows.Returns Team ar w where
  pub := pub
  macros := mac
  initialRegs u := (splitAt ar table paths u).middleRegs
  input u := (splitAt ar table paths u).mem
  events u := (splitAt ar table paths u).last
  finalRegs u := (paths u).val.2.1
  output u := (paths u).val.2.2
  path u := (splitAt ar table paths u).traversed

/-- The intermediate bank and RAM are reached by a real installer run. -/
theorem split_install (u : Team) : ∃ es, Runs (pub u) (mac u) (CubeDeck.install table) (regs u) (original u)
    es ((splitTeams ar table paths).initialRegs u) ((splitTeams ar table paths).input u) :=
  ⟨(splitAt ar table paths u).first,(splitAt ar table paths u).installed⟩

/-- Every private choice of the combined run belongs to the owned traversal. -/
theorem split_tape (u : Team) :
    (splitTeams ar table paths).tape ar u=(paths u).val.1.flatMap TeamRAM.Event.choices := by
  let cut := splitAt ar table paths u
  have empty : cut.first.flatMap TeamRAM.Event.choices=[] := List.flatMap_eq_nil_iff.mpr fun e he =>
    (cut.installed.unsigned_events (CubeConstants.install_unsigned (CubeDeck.entry table)).1 e he).1
  change cut.last.flatMap _=_
  rw [cut.events,List.flatMap_append,empty,List.nil_append]

end FiniteEvaluator.CubeTriple

namespace TeamContraction

open VPVNP BurstRAM Diagonal.Layout RoutingISA RoutingISA.Transmission Routing
open BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter DiagonalTallyPacketEmit FiniteEvaluator

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
variable {pin : Fin d → Bool} {ext : Exterior R r link → Bool} {wire : WireLayout (R+1) r link}
variable {dir : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)} {origin stride : ℕ}
variable {H : Fin (R+1) → TeamHistory w} {pins : Fin (R+1) → Pins.Layout}
variable {delivery : ReturnedDelivery G pin ext wire dir pp lp owner origin stride H pins}
variable {g : SharedRows.Layout} {src : Fin (R+1) → ℕ → ℕ} {F : Type*} [Fintype F]

/-- A returned writer and the source's scanner and installer words supply the physical
handoff at any declaration, including declarations with invalid common bit strings. -/
theorem SharedWriters.splitHandoff (writer : SharedWriters delivery g src) (ar : CubeArena.Layout)
    (decl : LengthDeclaration ar.n ar.header.d) (group : Fin ar.header.d → Fin (R+1))
    (table : TableEntry ar.n ar.b ar.h ar.K ar.s → F) (template : Frame) (count : ℕ)
    {mc : Fin (R+1) → TeamOpcode.Macros w 8}
    (paths : ∀ u, Evaluator.Returns (CubeTriple.installGroups table) (H u).pub (mc u)
      (H u).history.val.2.1 (H u).history.val.2.2) (model : ∀ u, (H u).macros=mc u)
    (banks : g.banks=ar.pairBase) (spacing : g.stride=ar.pairStride)
    (room : ∀ u, ar.ReplayRoom w (readings (H u).pub 0)) (tab : ∀ u, delivery.table=ar.table (readings (H u).pub 0) count)
    (frame : ∀ u, g.frame=readings (H u).pub 0)
    (scanner : ∀ u, ar.ScannerWords (readings (H u).pub 0) u.val decl.1.val (fun x => (group x).val)
      (readings (H u).pub) (src u) decl.2)
    (wide : CubeDeck.minimumWidth F ar.n ar.b ar.h ar.K ar.s ≤ w)
    (deck : CubeConstants.arenaEnd ar.stop (CubeDeck.entry table)<2^w)
    (fields : ∀ u, CubeConstants.Fields (CubeConstants.inArena template ar.stop ar.n ar.b ar.h ar.K ar.s)
      (readings (H u).pub 0) (CubeConstants.idBase ar.stop ar.n ar.b ar.h ar.K ar.s) (src u)) :
    OwnedHandoff delivery g src ar decl group template (CubeDeck.entry table) count (CubeTriple.splitTeams ar table paths) := by
  refine ⟨fun _ => rfl,fun u => (model u).symm,banks,spacing,room,tab,frame,scanner,?_,?_,?_⟩
  · intro u
    have header := LocalRow.header_le_publicBase ar
    have separate := ar.separated
    have primary := (room u).primary
    exact CubeDeck.fits table template ar.stop (readings (H u).pub 0) (by omega) deck wide
  · intro u
    exact writer.returned_constant_fields ar (readings (H u).pub 0) count (tab u) (room u).primary
      (frame u) _ _ u (fields u)
  · intro u
    obtain ⟨es,run⟩ := CubeTriple.split_install ar table paths u
    exact ⟨es,(congrArg (fun macros => Runs (H u).pub macros (CubeDeck.install table)
      (H u).history.val.2.1 (H u).history.val.2.2 es ((CubeTriple.splitTeams ar table paths).initialRegs u)
      ((CubeTriple.splitTeams ar table paths).input u)) (model u)).mpr run⟩

end TeamContraction

namespace FiniteDiagonal.FieldRawLayout.SignedRouteReceipt

open Crossing BorderVNP.Cube BorderVNP.Cube.Physical BorderVNP.Cube.Scatter BorderVNP.Cube.Tally
open FiniteEvaluator RoutingISA TeamContraction VPVNP.BurstRAM

variable {D : ℕ} {P : Type} [Fintype P] {bits : P → ℕ} {N : Network D P bits}
variable {F : Type*} [Field F] [Fintype F] {T : N.Tables F} {L : FieldPacketPlan N F} {S : FieldSiteDirectory N T}
variable {V : FieldRawLayout L S} {R : ℕ} {raw : V.Raw R} {codec : Cells.Codec} (a : SignedRouteReceipt V R raw codec)
variable (paths : a.Returns)

local notation "decl" => Assignment.Routed.trueDeclaration L.bitWidth L.supply (Sigma.fst (Prod.fst raw))
local notation "group" => V.owners R (Sigma.fst (Prod.fst raw))

/-- Owned-group returns on the signed route's actual register and memory histories. -/
noncomputable abbrev split : TeamRows.Returns (Fin (R+1)) a.arena a.w :=
  CubeTriple.splitTeams a.arena a.table paths

/-- Splitting this signed route preserves each team's exact private choices. -/
theorem split_tape (u : Fin (R+1)) :
    (a.split paths).tape a.arena u=(paths u).val.1.flatMap TeamRAM.Event.choices :=
  CubeTriple.split_tape a.arena a.table paths u

set_option maxHeartbeats 1200000 in
/-- The physical delivery, four surviving installer pointers, and actual installer
returns provide the scanner handoff for the complete family of split team paths. -/
theorem split_handoff : OwnedHandoff a.delivery a.g a.src a.arena decl group
    (a.signedArena.lookupFrame 0) (CubeDeck.entry a.table) a.count (a.split paths) := by
  apply a.writer.splitHandoff a.arena decl group a.table (a.signedArena.lookupFrame 0) a.count paths
    a.model a.banks a.spacing a.room a.tab a.frame a.scanner a.wide _ (a.fields ·)
  let A := V.bankData R raw a.arena.header.packetBase a.arena.singleBank
  obtain ⟨_,ds,_,_,rf,ids,top⟩ := a.signedArena.lookup_rooms (count:=0) A rfl (Nat.zero_le _) (Nat.zero_le _)
    a.digits (a.room 0).primary a.word
  exact ds.trans_lt (by omega)

end FiniteDiagonal.FieldRawLayout.SignedRouteReceipt

end BorderVNP
end Computability
end OAI
