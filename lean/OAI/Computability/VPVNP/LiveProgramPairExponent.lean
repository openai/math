import OAI.Computability.VPVNP.LiveProgramTerminalStage
import OAI.Computability.VPVNP.LiveExponentOperands
import OAI.Computability.VPVNP.LivePairExponentCount

/-! # The terminal exponent test in the linked first-half group

Its ordinary digit calls write only to the addressed counter word. The outer
dispatcher therefore continues to read the exponent-stage tag. All physical
dispatch probes occur in the capped count.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group
open BurstRAM BurstRAM.PrivateRAM LiveStageLink LiveExponent
open scoped Classical

variable (G : Group) {t Z : ℕ}

/-- The exponent-check stage’s public operand words evaluated at this group’s constants and
geometry. -/
abbrev exponentPub := ExponentStage.words G.constants G.g

theorem exponent_frame (L : BufferLayout G.exponentPub t Z) (hZ : 0 < Z)
    (hf : 31 ≤ G.clockAt Stage.exponents)
    (fresh : ∀ a : Fin t, counterAddr G.exponentPub a ≠ G.addr) :
    TagFrame G.T G.pub G.addr Stage.exponents (G.clockAt Stage.exponents)
      (fun s _ => s ≤ G.exponentPub 4) := by
  intro s mem bits rep s' hstate htag hc hret
  have hx := (Pieces.component_eq G.components G.g G.lit Stage.exponents (G.clockAt Stage.exponents)
    s mem bits).symm.trans hc
  change execute (digitTemplate.instantiate G.w G.exponentPub).program (G.clockAt Stage.exponents)
    ((digitTemplate.instantiate G.w G.exponentPub).program.start s) mem bits = some rep at hx
  let f := G.clockAt Stage.exponents - 31
  have htime : G.clockAt Stage.exponents = f+31 := (Nat.sub_add_cancel hf).symm
  rw [htime] at hx
  rcases lt_or_eq_of_le hstate with hs | he
  · have hrep := (data_result hs hx).2
    have hs' : s' = s+1 := Option.some.inj (hret.symm.trans (congrArg Report.result hrep))
    have hnext : (s+1).val = s.val+1 := Fin.val_add_one_of_lt' (by have ht := (G.exponentPub 4).isLt; change s.val < (G.exponentPub 4).val at hs; omega)
    change s.val < (G.exponentPub 4).val at hs
    have hd : s.val / Z < t := (Nat.div_lt_iff_lt_mul hZ).mpr (L.size ▸ hs)
    let a : Fin t := ⟨s.val / Z,hd⟩
    have haddr : carryAddress G.exponentPub s = counterAddr G.exponentPub a := by
      unfold carryAddress counterAddr
      congr 1
      change Fin.ofNat _ (s.val / (G.exponentPub 3).val) = _
      rw [L.width]
    refine ⟨by change s'.val ≤ _; rw [hs',hnext]; omega,?_⟩
    rw [hrep,digitReport_after,haddr]
    change (if G.addr.val = (counterAddr G.exponentPub a).val then _ else _) = _
    rw [ite_eq_right (fun h => fresh a (Fin.ext h.symm))]
    exact htag
  · rw [show f+31=(f+26)+5 by omega,execute_done _ _ _ _ _ he] at hx
    split at hx
    · have := congrArg Report.result (Option.some.inj hx)
      simp_all
    · contradiction

/-- At a physically tagged exponent entry the linked count is either one or
zero. The test includes the cap on the reports of all preceding stages. -/
theorem exponent_count (L : BufferLayout G.exponentPub t Z) (hZ : 0 < Z) (hw : 2 ≤ G.w)
    (hf : 31 ≤ G.clockAt Stage.exponents) (fresh : ∀ a : Fin t, counterAddr G.exponentPub a ≠ G.addr)
    (m : Memory G.w) (tag : G.tagged Stage.exponents m)
    (x y : Fin t → Word Z) (v : BufferValues G.exponentPub x y m) (inc : Fin t → Word G.w)
    (read : ∀ a, m (counterAddr G.exponentPub a).val = inc a) (small : ∀ a, (inc a).val+1 < 2^G.w)
    (cap : List (Report G.w) → Prop) :
    Nat.card (ActualPaths G.P G.clock 0 m cap) =
      if (∀ a, (y a).val = (x a).val+(inc a).val) ∧
        cap ((stageReports G.exponentPub t Z m).map (linkedReport G.nextStage G.addr Stage.exponents))
      then 1 else 0 := by
  let entry : Entry G Stage.exponents m := ⟨_,G.exponent_frame L hZ hf fresh,Fin.zero_le _,tag⟩
  rw [← Nat.card_congr (terminalEquiv entry (by rfl) cap)]
  change Nat.card (ActualPaths (digitTemplate.instantiate G.w G.exponentPub).program (G.clockAt Stage.exponents)
    0 m (fun rs => cap (rs.map (linkedReport G.nextStage G.addr Stage.exponents)))) = _
  rw [show G.clockAt Stage.exponents = G.clockAt Stage.exponents-31+31 by omega]
  exact pathCount L hZ hw v inc read small _ _

end LiveProgram.PairStages.Group

end VPVNP
end Computability
end OAI
