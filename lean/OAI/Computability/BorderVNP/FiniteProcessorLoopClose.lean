import OAI.Computability.BorderVNP.FiniteProcessorChunk
import OAI.Computability.BorderVNP.TeamSiteInverse

/-! # The field product at the physical halt or handoff of a charged chunk -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP RAMTape TeamSite TeamSiteEvents SupplyRun TeamPrivateFragment
open BurstRAM (Word)
open RAMSerialization (WordRecord)
open TeamRAM (Event)

variable {Q Γ : Type} {p r k a m g w H : ℕ} {F : Type*} [Field F] [Fintype F] {hw : 2 ≤ w+1}

/-- A complete guarded chunk carries its field product into the physical close or
handoff, on the actual chronological record bank and with its original clock. -/
theorem close_complete (P : TeamOpcode.Program p r k a) (pub : Fin k → Word w) (lib : Fin a → Macro Q Γ m g)
    (weights : Returns Q Γ F m a) (fuel : ℕ) {s last : TeamOpcode.State w p r} {c fin : Window w} {es : List (Event w)}
    (chunk : Chunk (P.fetch pub (macros lib fuel)) s c es last fin) (live : Option (Fin p)) (closed : Closed P pub last fin live)
    (sg : Option Bool) (acc : F) (rs : List (WordRecord (w+1))) (base : Stacks (Port r k (m*g))) (suffix : List Bool)
    (safe : c.Safe) (clock : base ∘ Port.clock = c.bank pub s) (work : Work.Ready hw H rs base) (space : rs.length+2*c.block.val ≤ 4*H) :
    let endAcc := acc*foldEvents P pub lib fuel (eventAdjustment lib weights fuel) s es
    ∃ n b, n ≤ Work.chunkBudget w m g fuel es+Work.closeBudget w ∧
      StackRuns (replay (loopCode P lib weights)) n
        ((.clock sg (.enter s.pc),Fintype.equivFin F acc),chunkBits es++suffix) base
        ((.close (chunkSign sg es) live,Fintype.equivFin F endAcc),suffix) b ∧
      Work.Ready hw H (rs++chunkSlots (c.elapsed.val+1) es) b ∧ b ∘ Port.clock = fin.bank pub last := by
  intro endAcc
  obtain ⟨n,b,hn,path,ready,hclock,_⟩ := chunk_run P lib fuel weights pub chunk sg acc rs base suffix safe clock work space
  obtain ⟨t,ht,guard⟩ := clock_run P lib weights (chunkSign sg es) endAcc pub last fin.block fin.global fin.elapsed fin.cap
    (chunk.clock safe).2.2.1 b hclock suffix
  change StackRuns (replay (loopCode P lib weights)) _ _ _
    ((.clock (chunkSign sg es) (.exit (exit P pub last fin)),Fintype.equivFin F endAcc),suffix)
    (installStacks Port.clock b (outputBank P pub last fin)) at guard
  have noCall : ∀ o, exit P pub last fin ≠ .callback o := by
    rcases closed with ⟨_,h⟩ | ⟨_,h⟩ <;> simp [h]
  rw [noncallback_bank P pub last fin noCall,installStacks_eq (fun _ _ he => Port.clock.inj he) b _ (congrFun hclock)] at guard
  have finalStep : StackRuns (replay (loopCode P lib weights)) 1
      ((.clock (chunkSign sg es) (.exit (exit P pub last fin)),Fintype.equivFin F endAcc),suffix) b
      ((.close (chunkSign sg es) live,Fintype.equivFin F endAcc),suffix) b := by
    rcases closed with ⟨rfl,h⟩ | ⟨rfl,h⟩ <;> rw [h] <;> apply StackRuns.cons _ (StackRuns.nil ..) <;>
      exact .goto (by simp [replay,loopCode,FieldStack.productCode,Loop.code,loopFactor,StackOp.rename])
  exact ⟨_,_,by unfold Work.closeBudget; omega,(path.trans guard).trans finalStep,ready,hclock⟩

end FieldProcessor

end BorderVNP
end Computability
end OAI
