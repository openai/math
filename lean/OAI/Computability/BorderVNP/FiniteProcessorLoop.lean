import OAI.Computability.BorderVNP.FiniteProcessorWeightEvents
import OAI.Computability.BorderVNP.TeamSiteRun

/-! # Field-augmented elementary instruction loop

Clock charging, timestamp reset and ordinary memory callbacks are the same
elementary instructions of the signed validator and carry a neutral field factor.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP RAMTape TeamSite TeamPrivateFragment
open VPVNP.BurstRAM (Word wordBits)
open RAMSerialization (WordRecord)
open private rename_acc from OAI.Computability.BorderVNP.FiniteProcessorWeightSegments
open private callback from OAI.Computability.BorderVNP.TeamSiteLoop

variable {Q Γ : Type} {p r k a m g width H : ℕ} {F : Type*} [Field F] [Fintype F] {hw : 2 ≤ width+1}

/-- The private-halt factor in the actual nested instruction loop. -/
noncomputable def loopFactor {P : TeamOpcode.Program p r k a} (lib : Fin a → Macro Q Γ m g)
    (w : Returns Q Γ F m a) : Loop.Label P Q m g → F
  | .privateCall _ j _ q => privateFactor (lib j) (w j) q
  | _ => 1

/-- The original loop code with field weights, ready to install in the physical processor. -/
noncomputable def loopCode (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (w : Returns Q Γ F m a) :=
  FieldStack.productCode (Loop.code P lib) (loopFactor lib w)

/-- A charged fetch preserves the accumulator on every physical clock and dispatcher row. -/
theorem clock_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (w : Returns Q Γ F m a)
    (sg : Option Bool) (acc : F) (pub : Fin k → Word width) (s : TeamOpcode.State width p r)
    (block left elapsed cap : Word width) (safe : elapsed.val+left.val < 2^width)
    (base : Stacks (TeamSite.Port r k (m*g))) (hc : base ∘ TeamSite.Port.clock = TeamLocalClock.bank pub s block left elapsed cap)
    (bits : List Bool) :
    let x := TeamLocalClock.Loop.result P pub s block left elapsed cap
    ∃ n ≤ 1050*(width+1)^2, StackRuns (replay (loopCode P lib w)) n
      ((.clock sg (.enter s.pc),Fintype.equivFin F acc),bits) base
      ((.clock sg (.exit x.1),Fintype.equivFin F acc),bits) (installStacks TeamSite.Port.clock base x.2) := by
  intro x
  obtain ⟨n,hn,h⟩ := TeamLocalClock.Loop.step P pub s block left elapsed cap safe
  let label := fun q => (Loop.Label.clock (P := P) (Q := Q) (m := m) (g := g) sg q,Fintype.equivFin F acc)
  have r := h.lift TeamSite.Port.clock (fun _ _ he => TeamSite.Port.clock.inj he) label base (target := loopCode P lib w) (by
    intro q hq
    have eq : Loop.code P lib (.clock sg q) = (TeamLocalClock.Loop.rows P q).rename TeamSite.Port.clock (.clock sg) := by
      cases q <;> first | rfl | simp [TeamLocalClock.Loop.rows] at hq
    simp only [loopCode,FieldStack.productCode,label,loopFactor,Equiv.symm_apply_apply,mul_one,eq,rename_acc])
  have he := installStacks_eq (fun _ _ he => TeamSite.Port.clock.inj he) base (TeamLocalClock.bank pub s block left elapsed cap) (congrFun hc)
  exact ⟨n,hn,by simpa only [he] using replay_segment r bits⟩

/-- Timestamp clearing contributes no field factor and reaches the original next PC. -/
theorem reset_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (w : Returns Q Γ F m a)
    (sg : Option Bool) (acc : F) (pc : Fin p) (s : Stacks (TeamSite.Port r k (m*g))) (bits : List Bool) :
    StackRuns (replay (loopCode P lib w)) ((s (.clock .stamp)).length+1)
      ((Loop.resume sg pc,Fintype.equivFin F acc),bits) s
      ((.clock sg (.enter pc),Fintype.equivFin F acc),bits) (Function.update s (.clock .stamp) []) := by
  let q := fun z => (Loop.Label.reset (P := P) (Q := Q) (m := m) (g := g) sg pc z,Fintype.equivFin F acc)
  apply replay_segment
  apply TeamLink.routine_id (SliceArithmetic.CallClear.clear_runs _ s) (loopCode P lib w) q (.clock sg (.enter pc),Fintype.equivFin F acc)
  intro u
  simp only [loopCode,FieldStack.productCode,q,Loop.code,loopFactor,Equiv.symm_apply_apply,mul_one,rename_acc]
  congr 1
  funext o
  cases o <;> rfl

/-- An ordinary memory callback consumes the same previous-word bits, emits the
same records and preserves the field accumulator. -/
theorem memory_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g) (w : Returns Q Γ F m a)
    (sg : Option Bool) (acc : F) (pc : Fin p) (op : TeamMemoryCallback.Op r) (old : Word width) (suffix : List Bool)
    {s : Stacks (TeamSite.Port r k (m*g))} {rs : List (WordRecord (width+1))}
    (ready : Work.Ready hw H rs s) (pub : Fin k → Word width) (state : TeamOpcode.State width p r)
    (meter : Fin 6 → Word width) (tick cap : Word width)
    (clock : s ∘ TeamSite.Port.clock = TeamLocalClock.banks pub state.logged meter cap (wordBits tick))
    (free : rs.length+2 ≤ 4*H) :
    ∃ t out, t ≤ 186*width+227 ∧ StackRuns (replay (loopCode P lib w)) t
      ((.clock sg (.exit (.callback (Work.memoryExit pc op))),Fintype.equivFin F acc),(wordBits old).reverse++suffix) s
      ((Loop.resume sg pc,Fintype.equivFin F acc),suffix) out ∧ Work.Ready hw H (rs++TeamMemoryCallback.pair op state.reg tick old) out ∧
      out ∘ TeamSite.Port.clock = TeamLocalClock.banks pub
        (TeamOpcode.State.logged ⟨pc,TeamMemoryCallback.registers op state.reg old⟩) meter cap (wordBits tick) := by
  have entry := ready.memoryReady (pub := pub) (reg := state.reg) (tick := tick)
    (funext fun j => congrFun clock (.isa j)) (congrFun clock .stamp) (congrFun clock .copyScratch)
  obtain ⟨t,b,ht,run,out⟩ := TeamMemoryCallback.run op old suffix entry free
  let label := fun z => (Loop.Label.memory (P := P) (Q := Q) (m := m) (g := g) sg pc op z,Fintype.equivFin F acc)
  have path := TeamLink.replay_lift run (loopCode P lib w) TeamSite.memory TeamSite.memory_injective label s (by
    intro j hj
    have eq : Loop.code P lib (.memory sg pc op j) = (TeamMemoryCallback.code op j).rename TeamSite.memory (.memory sg pc op) := by
      cases j <;> first | rfl | simp [TeamMemoryCallback.code] at hj
    simp only [loopCode,FieldStack.productCode,label,loopFactor,Equiv.symm_apply_apply,mul_one,eq,rename_acc])
  have first : StackRuns (replay (loopCode P lib w)) 1
      ((.clock sg (.exit (.callback (Work.memoryExit pc op))),Fintype.equivFin F acc),(wordBits old).reverse++suffix) s
      (label (TeamMemoryCallback.entry op),(wordBits old).reverse++suffix) s := by
    cases op <;> apply StackRuns.cons _ (StackRuns.nil ..) <;> apply StackStep.goto <;>
      simp [replay,loopCode,FieldStack.productCode,Loop.code,loopFactor,Work.memoryExit,label,callback,StackOp.rename]
  have last : StackRuns (replay (loopCode P lib w)) 1 (label .done,suffix) (Work.withMemory s b)
      ((Loop.resume sg pc,Fintype.equivFin F acc),suffix) (Work.withMemory s b) := by
    apply StackRuns.cons _ (StackRuns.nil ..)
    exact .goto (by simp [replay,loopCode,FieldStack.productCode,Loop.code,loopFactor,label,StackOp.rename])
  rw [installStacks_eq TeamSite.memory_injective s (s ∘ TeamSite.memory) (fun _ => rfl),Work.installMemory] at path
  refine ⟨_,_,by omega,(first.trans path).trans last,ready.withMemory out,?_⟩
  funext j
  cases j with
  | isa j => exact congrFun out.registers j
  | stamp => exact out.time
  | copyScratch => exact out.tmp
  | meter j => exact congrFun clock (.meter j)
  | maxBurst => exact congrFun clock .maxBurst

end FieldProcessor

end BorderVNP
end Computability
end OAI
