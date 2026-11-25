import OAI.Optimization.LinearProgramming.Geometry.MinorDirectWord
import OAI.Optimization.LinearProgramming.RAM.CallablePrepareBase

/-! Decode the fixed first two or four request words directly from the scalar packet.
The first tag is supplied by the dispatch branch after its scalar word has been parked. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace MinorInstall
namespace DirectCopy

open RAM RAM.Block RAM.Callable

/-- Physical input of the direct scalar-to-native copy. The logical caller's first
packet token is available for parking, and the tag comes from the dispatch branch. -/
structure ScalarPacket (m : Memory ℚ) (sb : ℕ) (xs : List ℕ) : Prop where
  base : m.index (Odd.slot 80)=Odd.slot sb
  length : m.index (Odd.slot 81)=Odd.slot xs.length
  token (j) : 1 ≤ j → j < xs.length → m.data (Odd.slot (sb+j))=(xs[j]?.getD 0 : ℕ)
  zero2 : m.data (Odd.slot 2)=0
  zero29 : m.data (Odd.slot 29)=0
  one3 : m.data (Odd.slot 3)=1

theorem ScalarPacket.frame {m t : Memory ℚ} {sb xs} (h : ScalarPacket m sb xs) (data : t.data=m.data)
    (odd : ∀ j,t.index (Odd.slot j)=m.index (Odd.slot j)) : ScalarPacket t sb xs :=
  ⟨(odd _).trans h.base,(odd _).trans h.length,fun j hn hj => (congrFun data _).trans (h.token j hn hj),
    (congrFun data _).trans h.zero2,(congrFun data _).trans h.zero29,(congrFun data _).trans h.one3⟩

theorem digit_le {xs : List ℕ} {B : ℕ} (digits : ∀ v∈xs,v ≤ B) (j : ℕ) (hj : j < xs.length) : xs[j]?.getD 0 ≤ B := by
  simpa only [List.getElem?_eq_getElem hj,Option.getD_some] using digits xs[j] (List.getElem_mem ..)

/-- Each even output is also the pointer used to decode its own scalar. -/
def headWord (tag j : ℕ) : Block := if j=0 then .op (.addrConst 0 (2*tag)) else
  .seq (copyIndexPlus (2*j) (Odd.slot 80) (2*j)) (decodeScalarWord (2*j) (2*j))

private theorem headWord_eval (m : Memory ℚ) (P : ℚ → Prop) (sb tag B j : ℕ) (xs : List ℕ)
    (packet : ScalarPacket m sb xs) (hj : j < xs.length) (tagged : xs[0]?=some tag)
    (digits : ∀ v∈xs,v ≤ B) (small : ∀ i ≤ B,P (i:ℚ)) (hm : m.AllData P) :
    ∃ k ≤ 5*B+2*j+6, Eval (Memory.AllData P) (headWord tag j) m k (m.putIndex (2*j) (2*(xs[j]?.getD 0))) := by
  by_cases zero : j=0
  · subst j
    refine ⟨1,by omega,?_⟩
    simpa [headWord,tagged] using Eval.op_addrConst (safe := Memory.AllData P) m 0 (2*tag) hm hm
  · let v := xs[j]?.getD 0
    let a := m.putIndex (2*j) (m.index (Odd.slot 80)+2*j)
    have move := copyIndexPlus_spec m (2*j) (Odd.slot 80) (2*j) hm
    have pointer : a.index (2*j)=Odd.slot (sb+j) := by
      calc a.index (2*j) = m.index (Odd.slot 80)+2*j := Memory.putIndex_same ..
           _ = Odd.slot sb+2*j := congrArg (fun v=>v+2*j) packet.base
           _ = Odd.slot (sb+j) := by unfold Odd.slot; omega
    have raw : a.data (a.index (2*j))=(v:ℚ) := by rw [pointer]; exact packet.token j (by omega) hj
    have lim := digit_le digits j hj
    have read := decodeScalarWord_eval a P (2*j) (2*j) v hm raw packet.zero2 packet.zero29 packet.one3
      (fun i hi => small i (hi.trans lim))
    have final : a.putIndex (2*j) (2*v)=m.putIndex (2*j) (2*v) := by simp [a,Memory.putIndex,Function.update_idem]
    rw [final] at read
    refine ⟨1+2*j+(5*v+5),by dsimp [v]; omega,?_⟩
    simpa only [headWord,ite_eq_right zero] using move.seq read

def head (tag : ℕ) : ℕ → Block
  | 0 => .skip
  | k+1 => .seq (head tag k) (headWord tag k)

/-- Rebuild each requested prefix cell and provide exact frames on all remaining
registers, also covering scalars used temporarily by the decoder. -/
theorem head_eval (m : Memory ℚ) (P : ℚ → Prop) (sb tag B k : ℕ) (xs : List ℕ)
    (hk : k ≤ 4) (hkx : k ≤ xs.length) (packet : ScalarPacket m sb xs) (tagged : xs[0]?=some tag)
    (digits : ∀ v∈xs,v ≤ B) (small : ∀ i ≤ B,P (i:ℚ)) (hm : m.AllData P) :
    ∃ t c, c ≤ k*(5*B+12) ∧ Eval (Memory.AllData P) (head tag k) m c t ∧ t.data=m.data ∧
      (∀ j, j < k → t.index (2*j)=2*(xs[j]?.getD 0)) ∧ ∀ p, (∀ j,j < k → p≠2*j) → t.index p=m.index p := by
  induction k with
  | zero => exact ⟨m,0,by simp,.skip hm,rfl,fun j h => (Nat.not_lt_zero j h).elim,fun _ _ => rfl⟩
  | succ k ih =>
    obtain ⟨a,c,hc,prior,hd,written,outside⟩ := ih (by omega) (by omega)
    have packetA := packet.frame hd (fun i => outside _ (fun j _ => by unfold Odd.slot; omega))
    obtain ⟨d,hc',more⟩ := headWord_eval a P sb tag B k xs packetA (by omega) tagged digits small prior.safe_end
    refine ⟨_,c+d,?_,prior.seq more,hd,?_,?_⟩
    · rw [Nat.succ_mul]; omega
    · intro j hj
      rcases lt_or_eq_of_le (Nat.le_of_lt_succ hj) with low|rfl
      · simpa [show 2*j≠2*k by omega] using written j low
      · simp
    · intro p frame
      simpa [frame k (by omega)] using outside p (fun j hj => frame j (by omega))

end DirectCopy
end MinorInstall
end Geometry
end LinearProgramming
end Optimization
end OAI
