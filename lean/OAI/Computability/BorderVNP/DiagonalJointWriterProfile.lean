import OAI.Computability.BorderVNP.DiagonalBootedJointClock
import OAI.Computability.BorderVNP.DiagonalSignedReferenceFrame

/-! # The reference writer on the physical profile of a joint signed return -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction

open VPVNP BurstRAM RoutingISA RoutingISA.Transmission RoutingISA.Evaluator
open Routing RoutingISA.CompactMachine ProcessorSlots BorderVNP.Cube Physical Tally
open private schedule_native from OAI.Computability.BorderVNP.RoutingISASignedPrepCoupling

variable {R r t d link inner n w : ℕ} {Edge : Type} {G : Wiring R r t d link inner n Edge}
    {wire : WireLayout (R+1) r link} {header : List Bool} {ar : CubeArena.Layout}
    {decl : LengthDeclaration ar.n ar.header.d} {pin : Fin d → Bool}
variable {pub : HeaderExterior wire header → Fin (R+1) → Arg → Word w} {mac : HeaderExterior wire header → Fin (R+1) → TeamOpcode.Macros w 8}
    {reg : HeaderExterior wire header → Fin (R+1) → Bank w} {mem : HeaderExterior wire header → Fin (R+1) → Memory w}
    (F : PreparationFrame G wire ar decl header pin pub mac reg mem)
    (x : HeaderExterior wire header) {hardware : Fin (R+1) → Bank w} {args : Fin (R+1) → UnitAddresses}
    (B : ∀ u, BootedPinStart SparseExterior.driver G (pub x) hardware args pin x.val u)
    (id : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
variable (a : PinStart.JointPrefix id (fun i => (B i).start))
local notation3 (prettyPrint := false) "vst(" i ")" => PinStart.visits id (fun k => (B k).start) (a i)
variable (installed : ∀ u, mac x u=install SparseExterior.driver n (B u).start.routines)
    (start : ∀ u, (reg x u,mem x u)=((B u).pins (a u).1).val.2)

include installed start in
/-- On its own substituted pins, the chronological joint return executes the
frame's silent schedule with exactly the same trace, registers, and memory. -/
theorem PreparationFrame.jointProfile (u : Fin (R+1)) :
    (F.schedule x u).val=(vst(u)).profile.val := by
  let actual : Returns (SignedPrep.schedule ar.n ar.K ar.h) (pub x u) (mac x u) (reg x u) (mem x u) :=
    ⟨(vst(u)).profile.val,by
      have regs : reg x u=((B u).pins (a u).1).val.2.1 := congrArg Prod.fst (start u)
      have ram : mem x u=((B u).pins (a u).1).val.2.2 := congrArg Prod.snd (start u)
      rw [installed u,regs,ram]
      exact (vst(u)).profile.property⟩
  exact congrArg Subtype.val (SignedPrep.return_eq_of_empty (pub x u) (mac x u) (schedule_native ..)
    (F.schedule x u) actual (F.empty x u))

variable {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ} {owner : ℕ → Fin (R+1)}
    {group : Fin ar.header.d → Fin (R+1)} {frame : ℕ} {guess : Fin (R+1) → ℕ → Bool}
    {dst ib hb sb : Fin (R+1) → ℕ}
    {epoch : ∀ y u, Returns epochPlacement (pub y u) (mac y u) (reg y u) (mem y u)}
    {published : ∀ y u, Returns Packing.Directory.ISA.program (pub y u) (mac y u)
      (epoch y u).val.2.1 (epoch y u).val.2.2}
    {endReg : HeaderExterior wire header → Fin (R+1) → Bank w} {out : HeaderExterior wire header → Fin (R+1) → Memory w}
    {events : HeaderExterior wire header → Fin (R+1) → List (TeamRAM.Event w)}
    {W : ∀ y u, WriterHistory ar.n (selectorWidth ar.n ar.K ar.h) (pub y u) (mac y u)
      (published y u).val.2.1 (published y u).val.2.2 (events y u) (endReg y u) (out y u)}
    (chosen : PreparationFrame.WriterProjection G wire ar D pp lp owner decl group frame header pin guess dst ib hb sb
      pub mac reg mem epoch published endReg out events W F)

local notation "entries" => List.length (D.directory pp lp)
local notation "tab" => ar.table frame (entries+ar.header.d.choose 2)
local notation "row" => RouteRecords.combinedRow (D.directory pp lp) owner ar.header.blocks ar.K ar.h decl group
local notation "shared" => ar.sharedRows frame (Fin.val (Prod.fst decl)) entries

include chosen installed start in
/-- The reference frame's physical table is ready on the actual memory seen
by every team in this joint prefix. Its emitted shared words come from the
original writer, with the same records and source pointers. -/
theorem PreparationFrame.WriterProjection.jointInitialized :
    SharedRoutePrepared G pin x.val wire D pp lp owner ar.cellBank ar.cellStride tab row (pub x)
      (fun u => (vst(u)).profile.val.2.2) dst ib hb sb guess ∧
    ∀ u, (vst(u)).profile.val.2=(endReg x u,out x u) ∧
      (shared).Emitted (readings (W x u).sharedInput) (readings (vst(u)).profile.val.2.2) := by
  have profile := F.jointProfile x B id a installed start
  have memory := funext fun u => congrArg (fun z => z.2.2) (profile u)
  constructor
  · simpa only [chosen.directory,chosen.privatePairs,chosen.livePairs,chosen.owned,chosen.origin,chosen.stride,
      chosen.table,chosen.slot,chosen.destination,chosen.input,chosen.column,chosen.reference,chosen.guesses,memory]
      using F.initialized x
  · intro u
    constructor
    · rw [←profile u,chosen.stages]
      rfl
    · simpa only [chosen.shared,chosen.image,profile] using F.emitted x u

end TeamContraction

end BorderVNP
end Computability
end OAI
