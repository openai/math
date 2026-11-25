import OAI.Computability.BorderVNP.TeamSiteStop
import OAI.Computability.BorderVNP.TeamSiteWitness

/-! # Exact correspondence between local RAM chunks and physical close witnesses

The physical choice string may have arbitrary length and the recorded weight
may be zero. A genuine close uniquely determines the native event sequence,
architectural state, clock, sign and continuation PC. A range failure has a
different terminal label even when its coefficient is zero.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite

open VPVNP RAMTape TeamPrivateFragment TeamSiteChoices TeamSiteEvents SupplyRun
open BurstRAM (Word)
open TeamRAM (Event)
open RAMSerialization (WordRecord)

variable {Q Γ : Type} {w p r k a m g H : ℕ} {hw : 2 ≤ w+1}

/-- The final local control either accepts or refuses the next whole instruction,
sending the unmodified live PC in the latter case. -/
def Closed (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w)
    (s : TeamOpcode.State w p r) (c : Window w) (live : Option (Fin p)) : Prop :=
  (live = none ∧ exit P pub s c = .accepted) ∨
    (live = some s.pc ∧ exit P pub s c = .handoff s.pc)

private theorem terminal_accept {P : TeamOpcode.Program p r k a} {pub : Fin k → Word w}
    {lib : Fin a → Macro Q Γ m g} {fuel : ℕ} {s : TeamOpcode.State w p r} {c : Window w} {u : Supply}
    (h : Run P pub lib fuel s c u [] s c .accepted) : exit P pub s c = .accepted := by
  cases h; assumption

private theorem terminal_handoff {P : TeamOpcode.Program p r k a} {pub : Fin k → Word w}
    {lib : Fin a → Macro Q Γ m g} {fuel : ℕ} {s : TeamOpcode.State w p r} {c : Window w} {u : Supply}
    (h : Run P pub lib fuel s c u [] s c .handoff) : exit P pub s c = .handoff s.pc := by
  cases h; assumption

private theorem halts_of_outcome (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    {sg pc q v} (h : Outcome P lib sg pc q v) : ∃ b, Loop.code P lib q = .halt b := by
  cases v with
  | accepted | handoff => subst_vars; exact ⟨_,rfl⟩
  | reject => exact ⟨false,h.1⟩

/-- A stopped physical close determines the native chunk it executed, with identical
consumed bits, exact chronological records and the physically carried final clock.
No validity assumption on the proposed branch bits is needed. -/
theorem close_sound (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w) (lib : Fin a → Macro Q Γ m g)
    (fuel : ℕ) (s : TeamOpcode.State w p r) (c : Window w) (rs : List (WordRecord (w+1)))
    (base : Stacks (Port r k (m*g))) (sg : Option Bool)
    (safe : c.Safe) (clock : base ∘ Port.clock = c.bank pub s) (work : Work.Ready hw H rs base)
    (space : rs.length+2*c.block.val ≤ 4*H) (bound : ∀ j vs, vs.length ≤ c.cap.val → (lib j).bounded fuel (vs : List (Word w)))
    (bits : List Bool) (weight : Option Bool) (live : Option (Fin p)) {n b}
    (actual : StackRuns (replay (Loop.code P lib)) n (.clock sg (.enter s.pc),bits) base (.close weight live,[]) b) :
    ∃ es last fin, Chunk (P.fetch pub (macros lib fuel)) s c es last fin ∧
      bits = chunkBits es ∧ weight = chunkSign sg es ∧ Closed P pub last fin live ∧
      Work.Ready hw H (rs++chunkSlots (c.elapsed.val+1) es) b ∧ b ∘ Port.clock = fin.bank pub last ∧
      n ≤ Work.chunkBudget w m g fuel es + Work.closeBudget w := by
  let u := extend bits
  obtain ⟨es,last,fin,v,run⟩ := exists_run P pub lib fuel s c u safe bound
  obtain ⟨t,q,b',ht,model,out,good⟩ := run.replay P pub lib fuel sg rs base [] safe clock work space
  rw [List.append_nil] at model
  obtain ⟨acc,halt⟩ := halts_of_outcome P lib out
  obtain ⟨eq,time,label,bank⟩ := TeamSiteWitness.prefix_unique u (x := bits) (y := chunkBits es)
    (prefix_extend bits) run.prefix actual model (h₁ := rfl) halt
  subst q b' t
  have success : v ≠ .reject := by intro hv; subst v; exact out.2 weight live rfl
  obtain ⟨wr,cr⟩ := good success
  refine ⟨es,last,fin,run.chunk,eq,?_,?_,wr,cr,ht⟩
  · cases v with
    | accepted | handoff => exact (Loop.Label.close.inj out).1
    | reject => contradiction
  · cases v with
    | accepted => exact Or.inl ⟨(Loop.Label.close.inj out).2,terminal_accept run.stopped⟩
    | handoff => exact Or.inr ⟨(Loop.Label.close.inj out).2,terminal_handoff run.stopped⟩
    | reject => contradiction

/-- Conversely every complete guarded native chunk has its own exact physical close
witness at the specified weight, including a valid weight-zero chunk. -/
theorem close_complete (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w) (lib : Fin a → Macro Q Γ m g)
    (fuel : ℕ) {s last : TeamOpcode.State w p r} {c fin : Window w} {es : List (Event w)}
    (chunk : Chunk (P.fetch pub (macros lib fuel)) s c es last fin) (live : Option (Fin p))
    (closed : Closed P pub last fin live) (sg : Option Bool) (rs : List (WordRecord (w+1)))
    (base : Stacks (Port r k (m*g))) (suffix : List Bool) (safe : c.Safe)
    (clock : base ∘ Port.clock = c.bank pub s) (work : Work.Ready hw H rs base) (space : rs.length+2*c.block.val ≤ 4*H) :
    ∃ n b, n ≤ Work.chunkBudget w m g fuel es + Work.closeBudget w ∧
      StackRuns (replay (Loop.code P lib)) n (.clock sg (.enter s.pc),chunkBits es++suffix) base
        (.close (chunkSign sg es) live,suffix) b ∧
      Work.Ready hw H (rs++chunkSlots (c.elapsed.val+1) es) b ∧ b ∘ Port.clock = fin.bank pub last := by
  let u := extend (chunkBits es)
  have hp : Prefix u (chunkBits es) := prefix_extend _
  rcases closed with ⟨rfl,endGuard⟩ | ⟨rfl,endGuard⟩
  · have run := of_chunk chunk hp (Run.accept endGuard)
    obtain ⟨t,q,b,ht,body,outcome,good⟩ := run.replay P pub lib fuel sg rs base suffix safe clock work space
    rw [show q = .close (chunkSign sg es) none from outcome] at body
    exact ⟨t,b,ht,body,good (by decide)⟩
  · have run := of_chunk chunk hp (Run.handoff endGuard)
    obtain ⟨t,q,b,ht,body,outcome,good⟩ := run.replay P pub lib fuel sg rs base suffix safe clock work space
    rw [show q = .close (chunkSign sg es) (some last.pc) from outcome] at body
    exact ⟨t,b,ht,body,good (by decide)⟩

end TeamSite

end BorderVNP
end Computability
end OAI
