import OAI.Hierarchy.DescentNamedCutObservations
import OAI.Hierarchy.DescentRegisterCutInduction
import OAI.Hierarchy.DescentRegisteredReelAddresses

namespace OAI
/-! # Reading the original count and rotation words of the registered history -/
namespace Hierarchy.DescentSixParty.Chronology.RegisterTimeline
open DescentCompiler DescentColonies DescentExterior DescentTerminalEpochDecoder DescentKernelHistory
open Computability.BorderVNP.Crossing Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
set_option hygiene false
variable {F P : Type} [Field F] [Fintype P] {G:PoweredGadget F} {S:AtomSchedule}
    {d k wire hist len w : ℕ} {bits:P→ℕ} {q ε : ℝ} {C:Type*}
    (traces:C→RunTrace G q ε S k wire hist len bits d)
    {bn bd:ℕ} (b:Menu bn bd) (initial:Position) (c:C) (m:Memory w)
local notation "t" => traces c
local notation "cpu" => instruction (w:=w) traces b initial
local notation "cursor" => calendar (w:=w) traces b initial
local notation "atRAM" => DateCode.history cpu m
local notation "tag" => Menu.resetFlag S
local notation "rot" => (fun i=>b.rotationAt G S k i (cursor i))
local notation "count_" => (fun i=>b.selectorAt G S k i (cursor i))

def capturedWords (i:ℕ) (e:(t).path.Event i) : Prop:=by
  cases e with
  | @ordinary _ _ _ _ _ _ src he _ _ _ dst before ticket after joined=>
    let μ:=multiplier src.placement.fieldBits (BitDescription.scannedRows he src.placement.stage).μ
    exact tag i=false ∧ atRAM (i+1) (count_ i)=(selectionCount G ticket.selection:Computability.VPVNP.BurstRAM.Word w) ∧
      atRAM (i+1) (rot i)=((matrixCode μ).val:Computability.VPVNP.BurstRAM.Word w)
  | reset before B after joined=>
    exact tag i=true ∧ atRAM (i+1) (rot i)=((matrixCode B.frame.basis).val:Computability.VPVNP.BurstRAM.Word w)

variable (limit:ℕ) (valid:Prop)
variable (fixed:∀i (l r:RunTrace.Events traces i) (x y : Move w),
  issued traces b i l (cursor i) x→issued traces b i r (cursor i) y→x=y)
variable (seed:initial.ports.held (t).first initial.floor m)
variable (advance:∀i (e:(t).path.Event i),advances traces b initial c m limit valid i e)
variable (readAt:∀i (e:(t).path.Event i),
  (e.isReset=true → valid) → e.incoming (cursor i) (atRAM i) → capturedWords traces b initial c m i e)

include fixed seed advance readAt in
omit [Fintype P] in
/-- The first rejected ballot can still contribute its selector count. Later dates
need no observations once the selected path has stopped. -/
theorem observed_path :
    (t).path.dateReadbacks atRAM tag rot count_ limit valid:=by
  let resident : ∀{U:MarkedWorld F d P bits} {a j D:ℕ} {r:Reached U G q ε S k a j D wire hist},
      Path (t).first r→Memory w→Prop:=fun {_} {a} {_} {_} {r} _ state=>(cursor a).ports.held r (cursor a).floor state
  apply ((t).path.observations_of_cuts atRAM resident tag rot count_ limit valid ?_).1
  intro U a j D r pre post joined
  cases pre with
  | here=>exact seed
  | @ordinary _ i _ _ _ _ src before _ he T pick norm dst ticket=>
    let e:(t).path.Event i:=.ordinary before ticket post joined
    intro incoming
    have words:=readAt i e (by intro h; cases h) incoming
    refine ⟨fun _=>words.2.1,fun _=>⟨words.1,words.2.2⟩,?_⟩
    exact fun active=>actual_transition traces b initial c m limit valid fixed advance i e incoming active
  | @reset _ i _ _ _ _ _ _ _ _ _ src before ctl B=>
    let e:(t).path.Event i:=.reset before B post joined
    intro incoming
    exact ⟨fun live=>readAt i e (fun _=>live) incoming,
      fun active=>actual_transition traces b initial c m limit valid fixed advance i e incoming active⟩

end
end Hierarchy.DescentSixParty.Chronology.RegisterTimeline

end OAI
