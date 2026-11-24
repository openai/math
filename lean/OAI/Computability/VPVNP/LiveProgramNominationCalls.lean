import OAI.Computability.VPVNP.LiveProgramPairStages
import OAI.Computability.VPVNP.LiveAuxiliaryStages
import OAI.Computability.VPVNP.LiveHeaderProtectedCore

/-! # Actual nomination calls in the linked first-half group -/

namespace OAI
namespace Computability
namespace VPVNP

namespace LiveProgram.PairStages.Group.Nominations

open BurstRAM BurstRAM.PrivateRAM LiveStageLink LiveAuxiliaryStages
open scoped Fin.CommRing

variable (G : Group)

/-- Width in bits of each nominated grammar-production count, twice the site-address width. -/
abbrev width := 2*G.g.d
/-- Number of grammar-production positions visited by the nomination stage. -/
abbrev labels := G.constants.grammarLabels.eval G.g
/-- RAM word addressing the first counter to which a nominated production count is written. -/
abbrev base := Pieces.word G.g G.lit (.geometry (Layout.counter G.constants))
/-- Grammar-label count encoded as the terminating cursor value in the group’s word width. -/
abbrev limit : Word G.w := Fin.ofNat _ (labels G)
/-- Instruction fuel available to a nomination call after outer dispatch. -/
abbrev fuel := G.clockAt Stage.nominations
/-- Nomination-stage source program with the linked table’s actual public operands. -/
abbrev P := sourceProgram G.T G.pub Stage.nominations

private theorem pub_eq :
    (fun j => Pieces.word G.g G.lit (.geometry (StageOperands.nomination G.constants j))) =
      nominationData (width G) (base G) (limit G) := by
  funext j
  fin_cases j <;> rfl

theorem execute_eq (f : ℕ) (s : Word G.w) (m : Memory G.w) (bs : List Bool) :
    let Q := (nomination.instantiate G.w (nominationData (width G) (base G) (limit G))).program
    execute (P G) f ((P G).start s) m bs = execute Q f (Q.start s) m bs := by
  have h := Pieces.component_eq G.components G.g G.lit Stage.nominations f s m bs
  change execute (P G) f ((P G).start s) m bs =
    execute (nomination.instantiate G.w _).program f ((nomination.instantiate G.w _).program.start s) m bs at h
  rw [← pub_eq]
  exact h

/-- A forward component and its unique successful decoding, with the actual
common outer clock after deducting dispatch. -/
theorem active (hb : width G ≤ G.w) (hf : 5*width G+15 ≤ fuel G) (s : Word G.w) (hs : s < limit G)
    (m : Memory G.w) (v : Word (width G)) :
    ∃ r, execute (P G) (fuel G) ((P G).start s) m (wordBits v) = some r ∧
      r.result = some (s+1) ∧ after m r.events = writeMemory m (base G+s) (Fin.ofNat _ v.val) ∧
      r.events.length = 5*width G+14 ∧ countProbes r.events = 1 := by
  obtain ⟨es,he,hm,hl,hp,_⟩ := nomination_active hb (base G) (limit G) s hs m v
  refine ⟨⟨es,some (s+1)⟩, ?_, rfl, hm, hl, hp⟩
  rw [execute_eq]
  simpa only [Nat.add_sub_of_le hf] using execute_extend he (fuel G-(5*width G+15))

theorem active_only (hb : width G ≤ G.w) (hf : 3 ≤ fuel G) (s : Word G.w) (hs : s < limit G)
    (m : Memory G.w) {bs : List Bool} {r : Report G.w}
    (hc : execute (P G) (fuel G) ((P G).start s) m bs = some r) :
    ∃ v : Word (width G), bs = wordBits v ∧ r.result = some (s+1) ∧
      after m r.events = writeMemory m (base G+s) (Fin.ofNat _ v.val) := by
  rw [execute_eq] at hc
  have eq := LiveHeaderBounded.execute_active (LiveNominations.flow.template (some 7))
    (LiveNominations.data (width G) (base G)) (limit G) (fuel G-3) s hs m bs
  rw [Nat.sub_add_cancel hf] at eq
  obtain ⟨rep, he, rfl⟩ := Option.map_eq_some_iff.mp (eq.symm.trans hc)
  obtain ⟨v,hv,hr,hm,_⟩ := LiveNominations.component_only hb (base G) s m he
  exact ⟨v,hv,hr,hm⟩

/-- Three-tick closing nomination report with no returned state. -/
def closing (w : ℕ) : Report w := ⟨[.tick,.tick,.tick],none⟩

theorem closed (hf : 4 ≤ fuel G) (s : Word G.w) (hs : limit G ≤ s) (m : Memory G.w) (bs : List Bool) :
    execute (P G) (fuel G) ((P G).start s) m bs = if bs=[] then some (closing G.w) else none := by
  rw [execute_eq]
  have h := nomination_closed (width G) (fuel G-4) (base G) (limit G) s hs m bs
  rw [Nat.sub_add_cancel hf] at h
  cases bs <;> simpa [closing] using h

theorem limit_val (hT : labels G < 2^G.w) : (limit G).val = labels G := Nat.mod_eq_of_lt hT

theorem base_add (fit : (base G).val + labels G ≤ 2^G.w) (i : Fin (labels G)) :
    base G + (i.val : Word G.w) = PrimedInputRAM.scratchAddress (base G).val fit i := by
  have ha := (Nat.add_lt_add_left i.isLt (base G).val).trans_le fit
  have hv : ((i.val : Word G.w) : ℕ) = i.val := by rw [Fin.val_natCast, Nat.mod_eq_of_lt (by omega)]
  apply Fin.ext
  rw [Fin.val_add_eq_of_add_lt (by simpa only [hv] using ha), hv]
  rfl

theorem frame (hb : width G ≤ G.w) (hT : labels G < 2^G.w) (hf : 5*width G+15 ≤ fuel G)
    (fit : (base G).val + labels G ≤ 2^G.w)
    (fresh : G.addr.val < (base G).val ∨ (base G).val+labels G ≤ G.addr.val) :
    TagFrame G.T G.pub G.addr Stage.nominations (fuel G) (fun s _ => s ≤ limit G) := by
  intro s m bs r next hs tag call ret
  rcases lt_or_eq_of_le hs with h | rfl
  · obtain ⟨v,_,hv,hm⟩ := active_only G hb (by omega) s h m call
    have hr := Option.some.inj (ret.symm.trans hv)
    have hval : s.val < labels G := (show s.val < (limit G).val from h).trans_eq (limit_val G hT)
    have room : (base G).val + s.val < 2^G.w := by omega
    refine ⟨?_, ?_⟩
    · change next.val ≤ (limit G).val
      rw [hr,Fin.val_add_one_of_lt' (show s.val+1 < 2^G.w by omega), limit_val G hT]
      omega
    · rw [hm]
      change (if G.addr.val=(base G+s).val then _ else _) = _
      rw [Fin.val_add_eq_of_add_lt room, ite_eq_right (by omega)]
      exact tag
  · rw [closed G (by omega) _ le_rfl] at call
    split at call
    · simp [← Option.some.inj call, closing] at ret
    · contradiction

end LiveProgram.PairStages.Group.Nominations

end VPVNP
end Computability
end OAI
