import OAI.Optimization.LinearProgramming.Geometry.BorderWire
import OAI.Optimization.LinearProgramming.Geometry.OracleSegments
import OAI.Optimization.LinearProgramming.RAM.Array

/-! The actual minor-query instruction, including its memory update and per-word charge. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM RAM.Block Matrix Compression Contract OracleSpec Contraction.Machine OracleSegments

variable {r s n k : ℕ}

/-- A total history encoding; the machine calls this key only if its sorted minor is nonzero. -/
def keyPacket (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ) (key : ℕ × Finset (Fin n)) : List ℚ :=
  ((Canonical.checkedPrimalMinor D E key).map (fun u => packet (interfaceIndex D E u).val)).getD []

/-- A compression oracle may interrupt at every valid minor. This premise grants
only the input packet, the two possible reply layouts, and a bound on a continuing value. -/
def Responds (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ)
    (P : ℚ → Prop) (o : ScalarOracle ℚ) : Prop :=
    ∀ (history : Contract.History ℚ) (u : MinorLog.Index D E), ∃ ans : Option ℚ,
      o history (packet u.val)=reply ans ∧ ∀ q, ans=some q → P q

private theorem reply_safe (m : Memory ℚ) (P : ℚ → Prop) (hm : ∀a,P (m.data a)) (hz : P 0) (ho : P 1)
    (ans : Option ℚ) (hq : ∀q,ans=some q→P q) : ∀a,P ((received m 82 83 (reply ans)).data a) := by
  intro a
  change P (if m.index 82 ≤ a then (reply ans)[a-m.index 82]?.getD (m.data a) else m.data a)
  split
  · cases ans with
    | none =>
      cases a-m.index 82 with
      | zero => exact ho
      | succ _ => exact hm a
    | some q =>
      cases a-m.index 82 with
      | zero => exact hz
      | succ v => cases v with
        | zero => exact hq q rfl
        | succ w => exact hm a
  · exact hm a

/-- A successful exchange carries the actual value at scratch+1; a restart carries tag 1. -/
structure ExchangeOutput (m t : Memory ℚ) (ans : Option ℚ) (base : ℕ) : Prop where
  tag : t.data base=if ans.isNone then 1 else 0
  value : ∀ q,ans=some q → t.data (base+1)=q
  destination : t.index 82=base
  replySize : t.index 83=(reply ans).length
  data (a) : 2 ≤ a → (a < 30 ∨ 31 < a) → a < base → t.data a=m.data a
  index (a) : a ≠ 80 → a ≠ 81 → a ≠ 82 → a ≠ 83 → (a < 91 ∨ 99 < a) → t.index a=m.index a

/-- Read the response using the prescribed scalar/register ABI; the request can occur
inside a larger program, and its scalar packet can have any legal minor order. -/
theorem send_query (b : Memory ℚ) (P A : ℚ → Prop) (o : ScalarOracle ℚ) (history : Contract.History ℚ)
    (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ) (u : MinorLog.Index D E)
    (source : sentPacket b 80 81=packet u.val) (base : ℕ) (dst : b.index 82=base)
    (hb : b.AllData P) (hz : P 0) (ho : P 1) (hAP : ∀q,A q → P q) (responds : Responds D E A o) :
    ∃ ans : Option ℚ, ∃ t c, c ≤ 2*n+5 ∧ Runs (.query 80 81 82 83) o (Memory.AllData P) b history c t
      ((packet u.val,reply ans)::history) ∧ ExchangeOutput b t ans base ∧ (∀ q, ans=some q → A q) := by
  obtain ⟨ans,ha,hans⟩ := responds history u
  have actual : o history (sentPacket b 80 81)=reply ans := source ▸ ha
  let t := received b 82 83 (reply ans)
  have hs : t.AllData P := reply_safe b P hb hz ho ans (fun q eq => hAP q (hans q eq))
  have eq := Runs.query 80 81 82 83 o history b hb (actual ▸ hs)
  dsimp only at eq
  rw [actual,source] at eq
  refine ⟨ans,t,1+(packet u.val).length+(reply ans).length,?_,eq,?_,hans⟩
  · rcases u.val with z | z <;> cases ans <;> simp [packet,MinorLog.words,MinorLog.squareWords,reply] <;> omega
  · refine ⟨?_,?_,?_,?_,?_,?_⟩
    · rw [← dst]
      cases ans <;> simp [t,received,receivePacket,State.memory,Memory.atPC,reply]
    · rintro q rfl
      rw [← dst]
      exact receivePacket_entry (b.atPC 0) 82 83 [0,q] 1 q rfl
    · simpa [t,received,receivePacket,Memory.atPC,State.memory] using dst
    · simp [t,received,receivePacket,Memory.atPC,State.memory]
    · intro a _ _ hab
      have hlt : ¬ b.index 82 ≤ a := by rw [dst]; omega
      simp [t,received,receivePacket,Memory.atPC,State.memory,hlt]
    · intro a _ _ _ a83 _
      simp [t,received,receivePacket,Memory.atPC,State.memory,a83]

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
