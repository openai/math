import OAI.Computability.BorderVNP.TeamSiteTimedRowStart

/-! # Checked physical closure and sorting of a native timed row -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamSite.TimedProcessor.Row

open VPVNP RAMTape BurstRAM TeamLocalClock TeamPrivateFragment TeamTapeHandoff Layout
variable {Q Γ : Type} {p r k a m g n d e w : ℕ} {P : TeamOpcode.Program p r k a}
variable {lib : Fin a → Macro Q Γ m g} {mark : Fin a → Γ}
variable (X : Site P lib mark n d e w)
local notation "oldLib" => fun j => extend (lib j) (mark j)
local notation "initial" => TrustedClock.installed (Layout.input (r:=r) (k:=k) (d:=(m+1)*g)) X.raw
local notation "Full" => Stacks (TeamClocked.Port (Layout.Port r k ((m+1)*g)))

/-- Extending a real timed run through the physical sorter retains its actual sign,
including a valid row whose native private table returned zero. -/
theorem finish (es : List (TeamRAM.Event w)) (sg : Option Bool) (ok : Bool) (body : ℕ)
    {ticks : ℕ} {out : Full} (bound : ticks+1 ≤ X.preludeTicks+Processor.Budget.endpoint r w body)
    (path : StackRuns (replay (code P lib mark)) ticks (.site Processor.start,chunkBits es) initial
      (.site (.block (TeamSite.Endpoint.finishLabel sg ok)),[]) out)
    (route : Processor.RouteReady n X.fields X.primary X.secondary (out ∘ TeamClocked.Port.user))
    (buffered : RecordBuffer.Holds X.hw₂ (2^e) (X.slots es) (out ∘ TeamClocked.Port.user ∘ buffer)) :
    Model X (chunkBits es) sg (ok = true ∧ X.sorted es) (X.cost body es) := by
  cases ok with
  | false =>
    refine ⟨ticks,?_,_,_,false,path,rfl,by simp,fun z => by simp [Checked,TeamSite.Endpoint.finishLabel],by simp⟩
    unfold Processor.Row.Context.cost
    have pos : 0 < Processor.Budget.sort n d e w := by unfold Processor.Budget.sort; omega
    omega
  | true =>
    let view := out ∘ TeamClocked.Port.user
    have hb : RecordBuffer.Holds X.hw₂ (2^e) (X.rows es X.primary) (view ∘ buffer) := X.rows_primary es ▸ buffered
    obtain ⟨t,ht,q,b,sorted,go,unmasked,check,row⟩ := Processor.closeSort_replay P oldLib sg n X.hw₂ X.capacity
      X.fields X.primary X.secondary (X.rows es) (fun u h => by simp [Processor.Row.Context.rows,X.distinct u h])
      view route X.hd X.hw X.hB X.hL hb (Processor.Budget.sort n d e w) (by rfl)
    have run := postlude_run P lib mark ((Processor.endpoint_done P oldLib sg view []).trans (go [])) (by trivial) out
    rw [installStacks_eq (fun _ _ => TeamClocked.Port.user.inj) out view (fun _ => rfl)] at run
    have physical : code P lib mark (.site (.sort sg (some q))) = .halt (sorted && sg.isSome) := by
      change (Processor.code P _ _).rename _ _ = _
      rw [row]; rfl
    refine ⟨_,?_,_,_,_,path.trans run,physical,?_,?_,?_⟩
    · change t < Processor.Budget.sort n d e w+Processor.Budget.close w (2^e) (X.rows es X.primary).length at ht
      rw [X.rows_primary] at ht
      unfold Processor.Row.Context.cost; omega
    · simp only [Bool.and_eq_true_iff,true_and,Processor.Row.Context.sorted]
      exact and_congr_left (fun _ => check)
    · intro z
      constructor
      · rintro ⟨st,e,yes⟩
        obtain ⟨rfl,h⟩ := Processor.Label.sort.inj (Label.site.inj e)
        obtain rfl := Option.some.inj h
        exact ⟨⟨rfl,check.mp (StackOp.halt.inj (unmasked.symm.trans yes))⟩,rfl⟩
      · rintro ⟨⟨_,good⟩,rfl⟩
        exact ⟨q,rfl,check.mpr good ▸ unmasked⟩
    · intro _; rfl

/-- Outside the endpoint every physical stack still agrees with the literal
prelude after a complete native block, including every proposed sorter stream. -/
theorem endpoint_frame {out : Full} (fr : Framed (startBank X) out) :
    installStacks Processor.endpoint X.base (out ∘ TeamClocked.Port.user ∘ Processor.endpoint) =
      out ∘ TeamClocked.Port.user := by
  apply installStacks_frame (target:=out ∘ TeamClocked.Port.user) Processor.endpoint_injective (fun _ => rfl)
  intro j absent
  have outside : ∀ i, loopPort i ≠ TeamClocked.Port.user j := fun i eq =>
    absent (.site i) (TeamClocked.Port.user.inj eq)
  exact (fr _ outside).trans ((installStacks_at (fun _ _ => TeamClocked.Port.user.inj) initial (decodedSite X) j).trans
    (installStacks_outside X.base _ absent))

/-- The RAM block cannot alter the outgoing stream or the empty frame-generation
scratch prepared by the real predecessor decoder. -/
theorem endpoint_streams {out : Full} (fr : Framed (startBank X) out) :
    out (.user .outgoing) = X.base .outgoing ∧ out (.user .payload) = [] ∧ out (.user .tmp) = [] := by
  let ep := X.base ∘ Processor.endpoint
  let desc := Startup.decoded X.pub X.frame X.block (Startup.remaining p X.frame X.limit) X.cap []
  let mid := installStacks TeamSite.Endpoint.startup ep desc
  have get (i : TeamSite.Endpoint.Port r k ((m+1)*g)) (apart : ∀ j, TeamSite.Endpoint.Port.site j ≠ i) :
      out (.user (Processor.endpoint i)) = mid i := by
    have absent : ∀ j, loopPort j ≠ TeamClocked.Port.user (Processor.endpoint i) := fun j eq =>
      apart j (Processor.endpoint_injective (TeamClocked.Port.user.inj eq))
    exact (fr _ absent).trans ((installStacks_at (fun _ _ => TeamClocked.Port.user.inj) initial (decodedSite X) _).trans
      (installStacks_at Processor.endpoint_injective X.base mid i))
  exact ⟨(get .outgoing (by simp)).trans (installStacks_outside ep desc (fun j => by cases j <;> simp [TeamSite.Endpoint.startup])),
    (get .payload (by simp)).trans ((installStacks_outside ep desc (fun j => by cases j <;> simp [TeamSite.Endpoint.startup])).trans X.payload),
    (get .tmp (by simp)).trans (installStacks_at TeamSite.Endpoint.startup_injective ep desc Startup.Port.tmp)⟩

end TeamSite.TimedProcessor.Row

end BorderVNP
end Computability
end OAI
