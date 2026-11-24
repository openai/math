import OAI.Computability.VPVNP.CompressorRefreshCoreBuild
import OAI.Computability.VPVNP.CompressorRefreshPrepareGroup
import OAI.Computability.VPVNP.CompressorCanonicalNativeTapes
import OAI.Computability.VPVNP.CompressorSourceObservableFrame

/-!
# Exact preparation, selector and suffix reports of the refresh calendar

Split the actual native source at its term ordinal. The prefix is the
preparation reported by the graph builder. The selector consumes the
canonical worker tapes. Every other stage reads an empty choice tape.
-/

namespace OAI
namespace Computability
namespace VPVNP

noncomputable section

set_option quotPrecheck false

namespace CompressorRecords.RefreshCore

open BurstRAM Compression Compression.Refresh Compression.DegreeRefresh PhaseRecipe BlockPlanner Schedule
open DescriptorSpace PortRefresh PortRefresh.LevelRecipe PortRefresh.Allocation SourceTransport
open scoped Fin.CommRing

variable {w : ℕ}

private theorem split_walk {J : Type*} {src : J → Memory w → List (Report w) → Prop}
    (a b : List J) {m : Memory w} {rs : List (Report w)} (walk : SourceWalk src (a++b) m rs) :
    ∃ left right, rs=left++right ∧ SourceWalk src a m left ∧ SourceWalk src b (after m (eventLog left)) right := by
  induction a generalizing m rs with
  | nil => exact ⟨[],rs,rfl,.done _,walk⟩
  | cons j js ih =>
    cases walk with
    | @next _ _ _ head tail current more =>
      obtain ⟨pre,post,eqn,hp,hs⟩ := ih more
      refine ⟨head++pre,post,by rw [eqn,List.append_assoc],.next current hp,?_⟩
      rw [SourceWalk.after_append]; exact hs

private theorem weaken {J : Type*} {src dst : J → Memory w → List (Report w) → Prop}
    (imp : ∀ j m rs, src j m rs → dst j m rs) {js : List J} {m : Memory w} {rs : List (Report w)}
    (h : SourceWalk src js m rs) : SourceWalk dst js m rs := by
  induction h with
  | done => exact .done _
  | next h _ ih => exact .next (imp _ _ _ h) ih

variable {k : Type*} [_root_.Field k] {S : BlockSchedule k} (B : S.Templates)
local notation "sh" => RefreshBlockPlan.shape B
local notation "hd" => S.degree_bounds.2
local notation "hc" => (S.port_bound.connected_and_pos S.port_order).1
local notation "he" => Nat.two_pow_pos S.expanderExponent
local notation "ties" => RefreshBlockPlan.order B

/-- Native stages strictly following the chosen refresh term. -/
def afterTerm : List (Stage sh) := [.supply] ++ (List.finRange ((sh).ports*(sh).dH)).map .rom ++
  (List.finRange (sh).degree).map .slot ++ [.base]

theorem stage_split : LevelRecipe.order sh = RefreshPrepare.stages B ++ .term :: afterTerm B := by
  simp only [RefreshPrepare.stages,afterTerm,LevelRecipe.order,List.append_assoc,List.cons_append,List.nil_append]

variable {g : ℕ} (X : State S.portExponent (S.portExponent+g))
variable (c : DyadicRefreshChoice X S.graph (Nat.two_pow_pos _) (S.port_bound.connected_and_pos S.port_order).1 B.refresh)
variable (old : IncidenceDirectory w) (start termCap low : ℕ)

local notation "P" => plan X (sh).a₀ (sh).dH (sh).ties (sh).stride start
local notation "native" => Scheduled.Source X S.graph he hc B.refresh hd c ties old start (sh).stride termCap
local notation "bounds" => Scheduled.StageBounds (t := (sh).ties) X S.graph he hc B.refresh start (sh).stride low
local notation "checked" => fun j m rs => native j m rs ∧ bounds j m rs
local notation "Q" => Plan.scratch P w
local notation "D" => NewSlots.word (bits := w) (Plan.demand P)
local notation "recordBase" => NewSlots.word (bits := w) (Plan.term P)
local notation "frame" => PrepareLayout X old (sh).a₀ (sh).dH (sh).ties (sh).stride start

open private demands from OAI.Computability.VPVNP.CompressorRefreshScheduledRuns

private theorem prepare_walk {L : frame} {m : Memory w} {rs : List (Report w)}
    (h : PrepareRun X old Q D ties (NewSlots.word (2^g)) L.regions.fits m (after m (eventLog rs)) rs) :
    SourceWalk native (RefreshPrepare.stages B) m rs := by
  obtain ⟨rg,rb,ro,ds,⟨hg,hb,ho,_⟩,rows,_,rfl⟩ := h
  have front : SourceWalk native [.gather,.bundles,.offsets] m (rg++rb++ro) := by
    rw [List.append_assoc]; exact .next hg (.next hb (.singleton ho))
  apply front.append
  rw [SourceWalk.after_append,SourceWalk.after_append]
  exact demands X S.graph he hc B.refresh hd c ties old start (sh).stride termCap rows

/-- All chronological calls of either side of the selector are deterministic. -/
theorem side_quiet {js : List (Stage sh)} {m : Memory w} {rs : List (Report w)}
    (quiet : ∀ j ∈ js, j ≠ .term) (run : SourceWalk checked js m rs) :
    branchPaths rs = List.replicate rs.length [] := by
  induction run with
  | done => rfl
  | @next j js m pre post one _ ih =>
    have eqn := ((runSegment_iff ..).mp one.1).2.2
    have ne := quiet j List.mem_cons_self
    have h : branchPaths pre = List.replicate pre.length [] := by
      have h' : branchPaths pre = List.replicate (j.limit X start-j.first) [] := by
        cases j <;> first | exact eqn | exact (ne rfl).elim
      have len := congrArg List.length h'
      simp only [branchPaths,List.length_map,List.length_replicate] at len
      rwa [len]
    have rest := ih (fun j hj => quiet j (List.mem_cons_of_mem _ hj))
    rw [branchPaths,List.map_append,List.length_append,List.replicate_add]
    change branchPaths pre ++ branchPaths post = _
    rw [h,rest]

/-- The exact split of the reports simultaneously retains the real native
stage proofs and the graph builder's preparation/term/suffix memory interfaces. -/
theorem split_logs {m : Memory w} {rs : List (Report w)} (L : frame)
    (build : Build.Run X S.graph he hc B.refresh S.port_order hd c ties old start (sh).stride termCap L m rs)
    (actual : SourceWalk checked (LevelRecipe.order sh) m rs) :
    ∃ pre terms tail, rs=pre++terms++tail ∧
      (let m₁ := after m (eventLog pre)
       let m₂ := after m₁ (eventLog terms)
       SourceWalk checked (RefreshPrepare.stages B) m pre ∧ checked .term m₁ terms ∧
       SourceWalk checked (afterTerm B) m₂ tail ∧
       PrepareRun X old Q D ties (NewSlots.word (2^g)) L.regions.fits m m₁ pre ∧
       termRun S.graph he hc B.refresh ties X D recordBase (sh).stride termCap (blockTapes S.graph he hc B.refresh X c w) m₁ = some terms ∧
       Finish.Run X S.graph he hc B.refresh S.port_order hd c recordBase (sh).stride ((P).inputs w) ((P).output w) m₂ tail) := by
  obtain ⟨prep,ts,suf,eqn,hp,ht,hs⟩ := build
  rw [stage_split] at actual
  obtain ⟨pre,rest,all,hpre,hrest⟩ := split_walk (RefreshPrepare.stages B) (.term::afterTerm B) actual
  cases hrest with
  | @next _ _ _ termLog tail chosen last =>
    have same : pre=prep := walk_deterministic (src := native) (fun _ _ _ _ a b => Option.some.inj (a.symm.trans b))
      (weaken (dst := native) (fun _ _ _ h => h.1) hpre) (prepare_walk B X c old start termCap (L := L) hp)
    subst prep
    have lengthEq : termLog.length=ts.length := by
      have ln := congrArg List.length (((runSegment_iff ..).mp chosen.1).2.2)
      have lt := congrArg List.length (((runSegment_iff ..).mp ht).2.2)
      simpa only [branchPaths,List.length_map] using ln.trans lt.symm
    have ab : pre++(termLog++tail) = pre++(ts++suf) := (all.symm.trans eqn).trans (List.append_assoc ..)
    have ss := List.append_cancel_left ab
    obtain ⟨rfl,rfl⟩ := List.append_inj ss lengthEq
    refine ⟨pre,termLog,tail,?_,hpre,chosen,last,hp,ht,hs⟩
    exact all.trans (List.append_assoc ..).symm

end CompressorRecords.RefreshCore

end

end VPVNP
end Computability
end OAI
