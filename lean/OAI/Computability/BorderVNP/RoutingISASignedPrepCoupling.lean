import OAI.Computability.BorderVNP.DiagonalNativeSignedWindow
import OAI.Computability.BorderVNP.DiagonalNativePreparedRoute

/-! # Chronological choices of the signed pre-cell evaluation

Expose the actual states at the route, owned-group and bottom-report boundaries.
The geometry circuit's interpreter admits a free-input opcode in its static code.
On the physical table with zero free inputs its successful trace draws no bits.
A single such trace suffices to recover the public prefix of every joint return.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace RoutingISA.Evaluator.SignedPrep

open VPVNP.BurstRAM BorderVNP.Cube BorderVNP.Cube.Tally
open private groups_native from OAI.Computability.BorderVNP.DiagonalNativeSignedTags

variable {dim b h K sym w : ℕ}
variable (id : TableEntry dim b h K sym → ℕ)
variable (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)

private abbrev ownerProgram := TeamRows.ownedGroups dim b h K sym
private abbrev groupProgram := scheduleGroups dim (selectorWidth dim K h)

/-- Native profile, geometric placements, row checks and physical routing directory. -/
def schedule (dim K h : ℕ) : Code := beforeRoute epochPlacement (scheduleGroups dim (selectorWidth dim K h))

/-- Post-scatter banks and report control records prepared from actual incoming bits. -/
def controls : Code := .block [Padding.verify,HostScatter.program,Packing.BundleDirectory.program,CellControlRows.program]

/-- Assemble the actual compact cell tasks from the published report and host-cell banks. -/
def arguments : Code := .block [FragmentRows.program,FragmentBucket.program,TypedTaskBuilder.program,CellPacket.Supplement.Batch.entry,
  SparseExterior.prepare,TypedBatch.entry]

/-- Task-record construction and the supplemental writes before typed serialization. -/
def beforeTyped : Code := .block [FragmentRows.program,FragmentBucket.program,TypedTaskBuilder.program,CellPacket.Supplement.Batch.entry,
  SparseExterior.prepare]

/-- The producer and serializer touch exactly the same event sequence as the compact
argument stage in the actual signed evaluator. -/
theorem arguments_split {s m es t mt} :
    Runs pub mac arguments s m es t mt ↔ Runs pub mac (.seq beforeTyped TypedBatch.entry) s m es t mt :=
  Runs.block_append_iff (a := [FragmentRows.program,FragmentBucket.program,TypedTaskBuilder.program,CellPacket.Supplement.Batch.entry,
  SparseExterior.prepare])
    (b := [TypedBatch.entry]) (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)

private noncomputable abbrev prepared := prepareExpansion epochPlacement (groupProgram (dim := dim) (K := K) (h := h))
  (signedInputs id (ownerProgram (dim := dim) (b := b) (h := h) (K := K) (sym := sym)))

private abbrev following {c : Code} {s : Bank w} {m : Memory w}
    (p : Returns c pub mac s m) (d : Code) := Returns d pub mac p.val.2.1 p.val.2.2

/-- One real return at each cut of the evaluation before the private calls. Each
later stage begins in the exact register bank and memory produced by its predecessor. -/
structure Visits (s : Bank w) (m : Memory w) where
  /-- Fitted profile and concrete emitted public tables. -/
  profile : Returns (schedule dim K h) pub mac s m
  /-- Complete four-pass routing return. -/
  routing : following pub mac profile route
  /-- Installed constant words and cube recipe tables. -/
  constants : following pub mac routing (CubeConstants.install id)
  /-- Owned packet and singleton scans. -/
  owned : following pub mac constants (TeamRows.ownedGroups dim b h K sym)
  /-- Zero tail checks, host copies and emitted cell controls. -/
  controls : following pub mac owned SignedPrep.controls
  /-- Actual bottom report choices. -/
  reports : following pub mac controls DiagonalTallyCellReports.prepareCellReports
  /-- Serialized arguments to the private cell dispatcher. -/
  arguments : following pub mac reports SignedPrep.arguments

private theorem input_iff (owned : Code) {s m es t mt} :
    Runs pub mac (signedInputs id owned) s m es t mt ↔
      Runs pub mac (.seq (CubeConstants.install id) (.seq owned (.seq controls
        (.seq DiagonalTallyCellReports.prepareCellReports arguments)))) s m es t mt := by
  let a := [Padding.verify,HostScatter.program,Packing.BundleDirectory.program,CellControlRows.program]
  let l := [DiagonalTallyCellReports.prepareCellReports,FragmentRows.program,FragmentBucket.program,TypedTaskBuilder.program,
    CellPacket.Supplement.Batch.entry,SparseExterior.prepare,TypedBatch.entry]
  change Runs pub mac (.seq _ (.seq owned (.block (a++l)))) _ _ _ _ _ ↔
    Runs pub mac (.seq _ (.seq owned (.seq (.block a) (.block l)))) _ _ _ _ _
  simp only [Runs.seq_iff, Runs.block_append_iff (a := a) (b := l) (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)]

private theorem cut {c : Code} {s m} (p q : Returns c pub mac s m) {l l' : List (TeamRAM.Event w)}
    (e : p.val.1 ++ l = q.val.1 ++ l') : p=q ∧ l=l' := by
  obtain ⟨ev,st,mm⟩ := p.property.eq_of_shared_events q.property e
  exact ⟨Subtype.ext (Prod.ext ev (Prod.ext st mm)),List.append_cancel_left (ev ▸ e)⟩

/-- The five physical phases after routing, up to the completed private call arguments. -/
noncomputable def inputVisitsEquiv (owned : Code) (s : Bank w) (m : Memory w) :
    (Σ c : Returns (CubeConstants.install id) pub mac s m,
      Σ o : following pub mac c owned, Σ d : following pub mac o controls,
      Σ f : following pub mac d DiagonalTallyCellReports.prepareCellReports, following pub mac f arguments) ≃
      Returns (signedInputs id owned) pub mac s m := by
  let go (v : Σ c : Returns (CubeConstants.install id) pub mac s m,
      Σ o : following pub mac c owned, Σ d : following pub mac o controls,
      Σ f : following pub mac d DiagonalTallyCellReports.prepareCellReports, following pub mac f arguments) :
      Returns (signedInputs id owned) pub mac s m :=
    ⟨(v.1.val.1 ++ (v.2.1.val.1 ++ (v.2.2.1.val.1 ++ (v.2.2.2.1.val.1 ++ v.2.2.2.2.val.1))),v.2.2.2.2.val.2),
      (input_iff id pub mac owned).mpr (v.1.property.seq (v.2.1.property.seq
        (v.2.2.1.property.seq (v.2.2.2.1.property.seq v.2.2.2.2.property))))⟩
  refine Equiv.ofBijective go ⟨?_,?_⟩
  · rintro ⟨c,o,d,f,a⟩ ⟨c',o',d',f',a'⟩ eq
    have vals := congrArg Subtype.val eq
    change (c.val.1 ++ (o.val.1 ++ (d.val.1 ++ (f.val.1 ++ a.val.1))),a.val.2) =
      (c'.val.1 ++ (o'.val.1 ++ (d'.val.1 ++ (f'.val.1 ++ a'.val.1))),a'.val.2) at vals
    obtain ⟨head,last⟩ := Prod.mk.inj vals
    obtain ⟨rfl,head⟩ := cut pub mac c c' head
    obtain ⟨rfl,head⟩ := cut pub mac o o' head
    obtain ⟨rfl,head⟩ := cut pub mac d d' head
    obtain ⟨rfl,head⟩ := cut pub mac f f' head
    obtain rfl : a=a' := Subtype.ext (Prod.ext head last)
    rfl
  · rintro ⟨⟨es,z,mz⟩,run⟩
    obtain ⟨_,_,_,_,rfl,rc,rest⟩ := Runs.seq_iff.mp ((input_iff id pub mac owned).mp run)
    obtain ⟨_,_,_,_,rfl,ro,rest⟩ := Runs.seq_iff.mp rest
    obtain ⟨_,_,_,_,rfl,rd,rest⟩ := Runs.seq_iff.mp rest
    obtain ⟨_,_,_,_,rfl,rf,ra⟩ := Runs.seq_iff.mp rest
    exact ⟨⟨⟨(_,_,_),rc⟩,⟨(_,_,_),ro⟩,⟨(_,_,_),rd⟩,⟨(_,_,_),rf⟩,⟨(_,_,_),ra⟩⟩,rfl⟩

/-- The input constructor appends the five concrete traces in visitation order. -/
theorem inputVisitsEquiv_val (owned : Code) {s m}
    (c : Returns (CubeConstants.install id) pub mac s m)
    (o : following pub mac c owned) (d : following pub mac o controls)
    (f : following pub mac d DiagonalTallyCellReports.prepareCellReports) (a : following pub mac f arguments) :
    (inputVisitsEquiv id pub mac owned s m ⟨c,o,d,f,a⟩).val =
      (c.val.1 ++ (o.val.1 ++ (d.val.1 ++ (f.val.1 ++ a.val.1))),a.val.2) := rfl

private theorem preparation_iff {s m es t mt} : Runs pub mac (prepared id) s m es t mt ↔
    Runs pub mac (.seq (schedule dim K h) (.seq route (signedInputs id (TeamRows.ownedGroups dim b h K sym)))) s m es t mt :=
  Runs.block_append_iff (a := [epochPlacement,Packing.Directory.ISA.program,scheduleGroups dim (selectorWidth dim K h)])
    (b := [route,signedInputs id (TeamRows.ownedGroups dim b h K sym)]) (List.cons_ne_nil _ _) (List.cons_ne_nil _ _)

/-- Every successful native preparation gives one chronological sequence of physical
stage returns, including its exact final bank and memory. This also covers early
rejection in any individual stage. -/
noncomputable def visitsEquiv (s : Bank w) (m : Memory w) :
    Visits id pub mac s m ≃ Returns (prepared id) pub mac s m := by
  let go (v : Visits id pub mac s m) : Returns (prepared id) pub mac s m :=
    ⟨(v.profile.val.1 ++ (v.routing.val.1 ++ (v.constants.val.1 ++ (v.owned.val.1 ++
      (v.controls.val.1 ++ (v.reports.val.1 ++ v.arguments.val.1))))),v.arguments.val.2),
      (preparation_iff id pub mac).mpr (v.profile.property.seq (v.routing.property.seq
        ((input_iff id pub mac _).mpr (v.constants.property.seq (v.owned.property.seq
          (v.controls.property.seq (v.reports.property.seq v.arguments.property)))))))⟩
  refine Equiv.ofBijective go ⟨?_,?_⟩
  · rintro ⟨p,r,c,o,d,f,a⟩ ⟨p',r',c',o',d',f',a'⟩ eq
    have vals := congrArg Subtype.val eq
    change (p.val.1++(r.val.1++(c.val.1++(o.val.1++(d.val.1++(f.val.1++a.val.1))))),a.val.2) =
      (p'.val.1++(r'.val.1++(c'.val.1++(o'.val.1++(d'.val.1++(f'.val.1++a'.val.1))))),a'.val.2) at vals
    obtain ⟨head,last⟩ := Prod.mk.inj vals
    obtain ⟨rfl,head⟩ := cut pub mac p p' head
    obtain ⟨rfl,head⟩ := cut pub mac r r' head
    obtain ⟨rfl,head⟩ := cut pub mac c c' head
    obtain ⟨rfl,head⟩ := cut pub mac o o' head
    obtain ⟨rfl,head⟩ := cut pub mac d d' head
    obtain ⟨rfl,head⟩ := cut pub mac f f' head
    obtain rfl : a=a' := Subtype.ext (Prod.ext head last)
    rfl
  · rintro ⟨⟨es,z,mz⟩,run⟩
    obtain ⟨_,_,_,_,rfl,rp,rest⟩ := Runs.seq_iff.mp ((preparation_iff id pub mac).mp run)
    obtain ⟨_,_,_,_,rfl,rr,inputs⟩ := Runs.seq_iff.mp rest
    obtain ⟨_,_,_,_,rfl,rc,rest⟩ := Runs.seq_iff.mp ((input_iff id pub mac _).mp inputs)
    obtain ⟨_,_,_,_,rfl,ro,rest⟩ := Runs.seq_iff.mp rest
    obtain ⟨_,_,_,_,rfl,rd,rest⟩ := Runs.seq_iff.mp rest
    obtain ⟨_,_,_,_,rfl,rf,ra⟩ := Runs.seq_iff.mp rest
    exact ⟨⟨⟨(_,_,_),rp⟩,⟨(_,_,_),rr⟩,⟨(_,_,_),rc⟩,⟨(_,_,_),ro⟩,
      ⟨(_,_,_),rd⟩,⟨(_,_,_),rf⟩,⟨(_,_,_),ra⟩⟩,rfl⟩

/-- Concatenation of the seven real event streams and exact final state. -/
theorem visitsEquiv_val {s m} (v : Visits id pub mac s m) :
    (visitsEquiv id pub mac s m v).val =
    (v.profile.val.1 ++ (v.routing.val.1 ++ (v.constants.val.1 ++ (v.owned.val.1 ++
      (v.controls.val.1 ++ (v.reports.val.1 ++ v.arguments.val.1))))),v.arguments.val.2) := rfl

/-- The joint cut exposes the real register bank and complete RAM passed to the private cells. -/
theorem visitsEquiv_outState {s m} (v : Visits id pub mac s m) :
    (visitsEquiv id pub mac s m v).val.2 = v.arguments.val.2 := rfl

/-- Each of the seven native stages is charged on its own true event stream. -/
theorem cost {s m} (v : Visits id pub mac s m) :
    traceCost (visitsEquiv id pub mac s m v).val.1 =
      traceCost v.profile.val.1 + (traceCost v.routing.val.1 + (traceCost v.constants.val.1 +
        (traceCost v.owned.val.1 + (traceCost v.controls.val.1 +
          (traceCost v.reports.val.1 + traceCost v.arguments.val.1))))) := by
  simp only [visitsEquiv_val,Transmission.cost_append]

/-- The three disjoint choice streams following the public profile. -/
structure Tapes where
  /-- Choice bits read by the co-located transfers during routing. -/
  transfer : List Bool
  /-- Choice bits read while scanning the team’s owned packets and singleton slots. -/
  owned : List Bool
  /-- Choice bits read by the bottom report producer. -/
  report : List Bool
  deriving DecidableEq

/-- Bits read by co-located transfers, private packet/singleton slots, and bottom reports. -/
def tapes {s m} (v : Visits id pub mac s m) : Tapes :=
  ⟨v.routing.val.1.flatMap TeamRAM.Event.choices,v.owned.val.1.flatMap TeamRAM.Event.choices,
    v.reports.val.1.flatMap TeamRAM.Event.choices⟩

/-- An actual ordinary return on an empty private tape is the unique return
from that state, even when the interpreter contains dormant choice opcodes. -/
theorem return_eq_of_empty {c : Code} {s m} (native : c.nativeOnly=true) (p r : Returns c pub mac s m)
    (noBits : p.val.1.flatMap TeamRAM.Event.choices=[]) : p=r := by
  have same := DiagonalResidueRAM.unique_returns (c.program_tag_native native) p.property r.property
    (tail := r.val.1.flatMap TeamRAM.Event.choices) (tail' := []) (by simp [noBits])
  exact Subtype.ext (Prod.ext same.1 (Prod.ext same.2.1 same.2.2))

private theorem schedule_native (n K h : ℕ) : (schedule n K h).nativeOnly=true := by
  simp only [schedule,beforeRoute,Code.block,Code.nativeOnly,groups_native,
      show epochPlacement.nativeOnly=true by decide,show Packing.Directory.ISA.program.nativeOnly=true by decide,Bool.and_self]

/-- The complete private stream of the returned preparation, after stripping its
unique public prefix and all deterministic state construction. -/
theorem choices {s m} (p : Returns (schedule dim K h) pub mac s m)
    (empty : p.val.1.flatMap TeamRAM.Event.choices=[]) (v : Visits id pub mac s m) :
    (visitsEquiv id pub mac s m v).val.1.flatMap TeamRAM.Event.choices =
    (tapes id pub mac v).transfer ++ ((tapes id pub mac v).owned ++ (tapes id pub mac v).report) := by
  have peq := return_eq_of_empty pub mac (schedule_native ..) p v.profile empty
  have const : v.constants.val.1.flatMap TeamRAM.Event.choices=[] :=
    List.flatMap_eq_nil_iff.mpr fun e he => (v.constants.property.unsigned_events (CubeConstants.install_unsigned id).1 e he).1
  have first : v.profile.val.1.flatMap TeamRAM.Event.choices=[] := peq ▸ empty
  simp only [visitsEquiv_val,List.flatMap_append,first,const,Pins.noChoices v.controls.property (by decide),
    Pins.noChoices v.arguments.property (by decide),List.append_nil,List.nil_append,tapes]

/-- At fixed physical inputs and substituted pins, two passing triples of stage
choices give distinct complete native preparations. -/
theorem tapes_injective {s m} (p : Returns (schedule dim K h) pub mac s m)
    (empty : p.val.1.flatMap TeamRAM.Event.choices=[]) :
    Function.Injective (tapes id pub mac (s := s) (m := m)) := by
  intro a b eq
  let e := visitsEquiv id pub mac s m
  have same : (e a).val.1.flatMap TeamRAM.Event.choices = (e b).val.1.flatMap TeamRAM.Event.choices := by
    let flat (x : Tapes) := x.transfer ++ (x.owned ++ x.report)
    exact (choices id pub mac p empty a).trans ((congrArg flat eq).trans (choices id pub mac p empty b).symm)
  have ends := DiagonalResidueRAM.unique_returns ((prepared id).program_tag_native (signedPrepare_nativeOnly id))
    (e a).property (e b).property (tail := []) (tail' := []) (congrArg (· ++ []) same)
  exact e.injective (Subtype.ext (Prod.ext ends.1 (Prod.ext ends.2.1 ends.2.2)))

end RoutingISA.Evaluator.SignedPrep

end BorderVNP
end Computability
end OAI
