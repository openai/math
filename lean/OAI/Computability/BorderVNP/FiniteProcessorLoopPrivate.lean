import OAI.Computability.BorderVNP.FiniteProcessorLoopBurst

/-! # Physical read interval and native finite-field callback

The ordinary RAM loop passes the previous words directly to the private
interpreter. The original burst, native choices, cleanup and sign continuation
use exactly their existing bounded elementary time.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FieldProcessor

open VPVNP BurstRAM RAMTape TeamSite TeamSite.Work TeamPrivateFragment
open RAMSerialization (WordRecord)
variable {Q Γ : Type} {p r k a m g w H : ℕ} {F : Type*} [Field F] [Fintype F] {hw : 2 ≤ w+1}
variable {rs : List (WordRecord (w+1))}

/-- The actual weighted callback from the charged register bank, through each probe
and the bounded native path, back to the next RAM instruction's reset label. -/
theorem loop_private_run (P : TeamOpcode.Program p r k a) (lib : Fin a → Macro Q Γ m g)
    (weights : Returns Q Γ F m a) (acc : F) (sg : Option Bool) (j : Fin a) (addr len : Fin r) (pc : Fin p)
    {s : Stacks (TeamSite.Port r k (m*g))} (h : Ready hw H rs s) (start length tick cap : Word w)
    (address : s (isa (.reg addr)) = wordBits start) (count : s (isa (.reg len)) = wordBits length)
    (stamp : s (.clock .stamp) = wordBits tick) (maxBurst : s (.clock .maxBurst) = wordBits cap)
    (legal : length.val ≤ cap.val ∧ start.val+length.val ≤ 2^w)
    (free : rs.length+2*length.val ≤ 4*H) (vs : List (Word w)) (hv : vs.length = length.val)
    {n choices sign u} (native : Run (TeamPrivateTape.trackTable (lib j).alphabet (lib j).table)
      n (lib j).start ((lib j).initial vs) choices sign u) (fuel : ℕ) (hf : n < fuel) (suffix : List Bool) :
    let ret := FieldSelect.nativeReturn (lib j).table (lib j).alphabet.blank (weights j) fuel (lib j).start
      (TeamPrivateTape.input (lib j).alphabet.blank (lib j).digit (lib j).inputTape (TeamPrivateCall.inputBits vs)) choices
    ∃ t out, t ≤ 1+TeamBurstCallback.entryCost w length.val+TeamBurstProbe.loopTime w length.val 0 +
        ((2*g+4)*(vs.length*w)+n*(3*(m*g)+2)+2*(m*g)+6) ∧
      StackRuns (replay (loopCode P lib weights)) t
        ((.clock sg (.exit (.callback (.call j addr len pc))),Fintype.equivFin F acc),TeamBurstProbe.choices vs++(choices++suffix)) s
        ((Loop.resume (Loop.times sg sign) pc,Fintype.equivFin F (acc * adjustment sign ret)),suffix) out ∧
      Ready hw H (rs++TeamBurstProbe.records start tick vs) out ∧ out ∘ TeamSite.Port.clock = s ∘ TeamSite.Port.clock := by
  intro ret
  obtain ⟨t,b,ht,burst,ready,clock⟩ := burst_run P lib weights acc sg j addr len pc h start length tick cap
    address count stamp maxBurst legal free vs hv (choices++suffix)
  let raw := TeamPrivateCall.inputBits vs
  let label := fun q : FieldStack.ProductState (TeamPrivateCompiler.Control Q m g) F =>
    (Loop.Label.privateCall (P := P) sg j pc q.1,q.2)
  have run := FieldProcessor.private_run (lib j) (weights j) raw native fuel hf acc suffix
  have path := TeamLink.replay_lift run (loopCode P lib weights) privateTape privateTape_injective label b (by
    rintro ⟨q,i⟩ hc
    cases q with
    | result sg => simp [privateCode,FieldStack.productCode,TeamPrivateCompiler.code,StackOp.returns] at hc
    | load z | run z =>
      simp only [loopCode,FieldStack.productCode,label,loopFactor,Loop.code,Macro.rows,privateCode]
      generalize TeamPrivateCompiler.code (lib j).alphabet (lib j).digit (lib j).inputTape (lib j).table (lib j).start _ = op
      cases op <;> rfl)
  rw [installStacks_eq privateTape_injective b (TeamPrivateInput.initial raw) (congrFun ready.privateInput),installPrivate] at path
  let after := Fintype.equivFin F (acc*adjustment sign ret)
  have last : StackRuns (replay (loopCode P lib weights)) 1 ((.privateCall sg j pc (.result sign),after),suffix) (clearPrivate b)
      ((Loop.resume (Loop.times sg sign) pc,after),suffix) (clearPrivate b) := by
    apply StackRuns.cons _ (StackRuns.nil ..)
    exact .goto (by simp [replay,loopCode,FieldStack.productCode,Loop.code,loopFactor,privateFactor,StackOp.rename])
  have time := TeamPrivateCompiler.run_input_cost_le (lib j).alphabet (lib j).digit (lib j).inputTape
    (lib j).table (lib j).start raw native
  rw [show raw.length = vs.length*w from TeamPrivateCall.inputBits_length vs] at time
  exact ⟨_,_,by omega,(burst.trans path).trans last,ready.clearPrivate,clock⟩

end FieldProcessor

end BorderVNP
end Computability
end OAI
