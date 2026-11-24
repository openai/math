import OAI.Computability.VPVNP.LiveStagePaths

/-! # Recovering an accepting source segment from an accepting linked run -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveStageLink

open BurstRAM BurstRAM.PrivateRAM

variable {d r k w : ℕ} {pcs : Fin d → ℕ}
variable (T : (s : Fin d) → Template (pcs s) r k) (next : Fin d → Option (Fin d))
variable (pub : Fin k → Word w) (addr : Word w)

/-- Every successful call at a valid stage tag arises from its actual source
table on the same bit string. This direction uses exactly the remaining fuel. -/
theorem recover_call {cap : ℕ} (s : Fin d) (hfits : d ≤ 2^w) (hcap : 2*d+2 ≤ cap)
    (st : Word w) (m : Memory w) (bits : List Bool) (out : Report w)
    (htag : m addr.val = tagWord w s)
    (he : execute (machine T next pub addr).program cap ((machine T next pub addr).program.start st) m bits = some out) :
    ∃ rep, execute ((T s).instantiate w pub).program (cap-(dispatchEvents addr s).length)
      (((T s).instantiate w pub).program.start st) m bits = some rep ∧ out = linkedReport next addr s rep := by
  have hlen : (dispatchEvents addr s).length ≤ cap := by simp [dispatchEvents]; have := s.isLt; omega
  have h := execute_linked T next pub addr s hfits st (cap-(dispatchEvents addr s).length) m htag bits
  dsimp only at h
  rw [Nat.sub_add_cancel hlen, he] at h
  obtain ⟨ex, hb, hr⟩ := Option.map_eq_some_iff.mp h.symm
  obtain ⟨rep, hs, hx⟩ := Option.bind_eq_some_iff.mp hb
  refine ⟨rep, hs, ?_⟩
  dsimp only [boundedExit] at hx
  split at hx <;> simp_all [linkedReport]

/-- An accepting run beginning at a known tag contains a complete accepting
source segment for that tag before any later component can execute. -/
theorem recover_accepting_stage {cap : ℕ} (s : Fin d) (hfits : d ≤ 2^w) (hcap : 2*d+2 ≤ cap)
    (st : Word w) (m : Memory w) (bits : List (List Bool)) (out : List (Report w))
    (htag : m addr.val = tagWord w s)
    (hframe : ∀ (cursor : Word w) mem b rep,
      execute ((T s).instantiate w pub).program (cap-(dispatchEvents addr s).length)
        (((T s).instantiate w pub).program.start cursor) mem b = some rep →
      rep.result.isSome → after mem rep.events addr.val = mem addr.val)
    (hr : runSegment (machine T next pub addr).program cap (some st) m bits = some out)
    (he : endState (some st) out = none) :
    ∃ before rest rs, bits = before ++ rest ∧
      runSegment ((T s).instantiate w pub).program (cap-(dispatchEvents addr s).length) (some st) m before = some rs ∧
      endState (some st) rs = none := by
  let fuel := cap-(dispatchEvents addr s).length
  have hlen : (dispatchEvents addr s).length ≤ cap := by simp [dispatchEvents]; have := s.isLt; omega
  have hfuel : fuel+(dispatchEvents addr s).length = cap := Nat.sub_add_cancel hlen
  have hstable : TagFrame T pub addr s fuel (fun _ _ => True) := by
    intro cursor mem b rep st' _ ht hc hv
    exact ⟨trivial,(hframe cursor mem b rep hc (by simp [hv])).trans ht⟩
  rw [← hfuel] at hr
  obtain ⟨before,rest,rs,_,_,hbits,_,completion,_,_⟩ := split_halted hfits hstable trivial htag hr he
  exact ⟨before,rest,rs,hbits,completion.spec.1,completion.spec.2.1⟩

end LiveStageLink

end VPVNP
end Computability
end OAI
