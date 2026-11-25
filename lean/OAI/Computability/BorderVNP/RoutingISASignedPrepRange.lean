import OAI.Computability.BorderVNP.RoutingISASignedPrepCoupling
import OAI.Computability.BorderVNP.CubeRouteAllDeclarations

/-! # Range, minimum and load guards forced by the actual signed public phase

Cut an arbitrary returning preparation at its physical geometry, directory
and group-schedule instructions. The genuine pinned prefix consumes no
private bits, so its returned registers and published directory are the ones
in this run. The eleven-stage schedule then excludes every malformed raw
declaration before routing or private cells can return.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube Physical Tally LocalRow CubeArena CubeHeaderInstall
open TeamContraction.JointHeader Transmission DiagonalResidueRAM

variable {w : ℕ} {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8}
variable {s reg : Bank w} {m input : Memory w}

/-- Cut the actual profile return at the end of the genuine pinned geometry
and private-directory publication, retaining every event of the group suffix. -/
theorem groups_after_pinned {n K h : ℕ} {pre : List (TeamRAM.Event w)}
    (prefixRun : Runs pub mac (.seq epochPlacement Packing.Directory.ISA.program) s m pre reg input)
    (noBits : pre.flatMap TeamRAM.Event.choices=[]) (r : Returns (schedule n K h) pub mac s m) :
    ∃ suffix, Runs pub mac (scheduleGroups n (selectorWidth n K h)) reg input suffix r.val.2.1 r.val.2.2 ∧
      r.val.1=pre++suffix := by
  have cut : Runs pub mac (.seq (.seq epochPlacement Packing.Directory.ISA.program) (scheduleGroups n (selectorWidth n K h)))
      s m r.val.1 r.val.2.1 r.val.2.2 :=
    (Runs.block_append_iff (a := [epochPlacement,Packing.Directory.ISA.program])
      (b := [scheduleGroups n (selectorWidth n K h)]) (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)).mp r.property
  obtain ⟨t,mt,es,fs,trace,prior,post⟩ := Runs.seq_iff.mp cut
  let orig : Returns (.seq epochPlacement Packing.Directory.ISA.program) pub mac s m := ⟨(pre,reg,input),prefixRun⟩
  let observed : Returns (.seq epochPlacement Packing.Directory.ISA.program) pub mac s m := ⟨(es,t,mt),prior⟩
  have eqn := return_eq_of_empty pub mac (show (Code.seq epochPlacement Packing.Directory.ISA.program).nativeOnly=true by decide)
    orig observed noBits
  obtain ⟨rfl,rfl,rfl⟩ : pre=es ∧ reg=t ∧ input=mt :=
    ⟨congrArg (fun z => z.val.1) eqn,congrArg (fun z => z.val.2.1) eqn,congrArg (fun z => z.val.2.2) eqn⟩
  exact ⟨fs,post,trace⟩

variable {ar : CubeArena.Layout} {D : Packing.Directory.Layout} {pp lp : ℕ → ℕ × ℕ}
variable {pins : Pins.Layout} {slotted : Memory w} {base : ℕ}
variable {I : Type*} [Fintype I] {cell : I → Fin ar.cells} {id : I ↪ ℕ} {widths : I → ℕ}
variable (P : SlottedWriter ar D pp lp pins pub slotted base cell id widths)
variable (f : BroadcastFrame) (old : Fin 81 → Word w) (fresh gates outputs width off ell controls : ℕ)
variable (G : List Bool) (claims : List (List Bool)) (pad : ℕ) (rawDecl : Broadcast ar.n ar.header.d ar.header.cap)
variable (R X : ℕ)

local notation3 "published" => Packing.Directory.ISA.publish slotted (pub 0).val base (D.directory pp lp)
local notation3 "raw" => padded (spelling (G++DeclarationBits.spelling rawDecl) claims) pad
local notation3 "physical" => geometryInputs fresh G.length gates outputs width w ar.header.d ar.n ar.header.blocks ar.b ar.h ar.s
local notation3 "ext" => jointFields (ar.extension old) fresh G.length gates outputs width off ell ar.header.d ar.n ar.header.blocks ar.b ar.h ar.s

/-- Physical input words and numeric room for the raw scheduler on the pinned
processor. All fields are prior to any range or minimum test of the declaration. -/
structure PinnedRawInput : Prop where
  boot : BootPins pub f ext raw published
  geometry : ar.header=physical
  frameSpace : (pub 0).val+112 ≤ ar.header.header
  copied : f.dst+(raw).length ≤ ar.header.header
  alphabet : 2 ≤ ar.header.d
  blocks : 0 < ar.header.blocks
  bank : 0 < bankWidth ar.n ar.b ar.h ar.K ar.s
  arena : ar.stop < 2^w
  labels : LabelPrefixFits (pub 0).val w (readings published)
  cells : readings published ((pub 0).val+11)=ar.cells
  teamCount : f.teams=R+1
  teamArena : ar.teams=R+1
  budget : (old 0).val=X
  million : 1000000 < 2^w
  scaled : 1000000*X*(R+1) < 2^w
  controlLow : controls+10 < ar.header.header
  pointers : readings published ((pub 0).val+92)=controls ∧ readings published (controls+9)=ar.cellBank ∧
    readings published (controls+10)=ar.cellStride
  processors : 0 < D.processors
  payload : 0 < D.block
  fields : D.fields ≤ 2
  rawSpace : 1000000*(ar.stop+3*D.teams*(D.processors*D.literal))+2*ar.stop < 2^w
  records : (D.directory pp lp).length+ar.header.d.choose 2 ≤ ar.maxRows

variable (room : PinnedRawInput (ar := ar) (D := D) (pp := pp) (lp := lp) (pub := pub) (slotted := slotted) (base := base)
  f old fresh gates outputs width off ell controls G claims pad rawDecl R X)

local notation3 "wl" => weightLayout ar (pub 0).val (readCode (ar.n+1) rawDecl.1)
local notation3 "tl" => teamLayout ar R

include P room in
/-- A complete signed profile return forces the declared coordinate and every
row word in range, the actual least coordinate, and all team and global load
guards on the genuine native chooser and interval image. -/
theorem raw_guards {pre : List (TeamRAM.Event w)}
    (prefixRun : Runs pub mac (.seq epochPlacement Packing.Directory.ISA.program) s m pre reg published)
    (noBits : pre.flatMap TeamRAM.Event.choices=[]) (r : Returns (schedule ar.n ar.K ar.h) pub mac s m) :
    declarationInRange rawDecl ∧ declaredMinimum rawDecl ∧ ∃ tr mid selected,
      Runs pub mac (.seq LabelIndex.directoryProgram NativeIntervals.prepare) reg published tr mid selected ∧
      (∀ x < ar.publicBase, readings selected x=readings published x) ∧
      capacities wl tl X (powerHeaderImage ar f.dst (readings selected)) := by
  obtain ⟨es,actual,_⟩ := groups_after_pinned prefixRun noBits r
  obtain ⟨tr,mid,selected,chooser,_,low,_,test⟩ :=
    P.raw_schedule f old fresh gates outputs width off ell controls mac reg G claims pad rawDecl R X room.boot room.geometry
      room.frameSpace room.copied room.alphabet room.blocks room.bank room.arena room.labels room.cells room.teamCount
      room.teamArena room.budget room.million room.scaled room.controlLow room.pointers room.processors room.payload room.fields
      room.rawSpace room.records
  obtain ⟨⟨range,least,cap⟩,_⟩ := test.2 actual
  exact ⟨range,least,tr,mid,selected,chooser,low,cap⟩

include P room in
/-- An out-of-range coordinate or row word, or a wrong least coordinate, has
an empty fiber of complete signed preparations at these original pinned inputs. -/
theorem visits_empty_of_bad_raw {pre : List (TeamRAM.Event w)}
    (prefixRun : Runs pub mac (.seq epochPlacement Packing.Directory.ISA.program) s m pre reg published)
    (noBits : pre.flatMap TeamRAM.Event.choices=[])
    (table : TableEntry ar.n ar.b ar.h ar.K ar.s → ℕ)
    (bad : ¬(declarationInRange rawDecl ∧ declaredMinimum rawDecl)) :
    IsEmpty (Visits table pub mac s m) := by
  refine ⟨fun visit => bad ?_⟩
  obtain ⟨range,least,_⟩ := raw_guards P f old fresh gates outputs width off ell controls G claims pad rawDecl R X room
    prefixRun noBits visit.profile
  exact ⟨range,least⟩

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
