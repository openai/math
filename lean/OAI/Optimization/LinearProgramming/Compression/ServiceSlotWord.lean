import OAI.Optimization.LinearProgramming.Compression.ServiceSlotPair
import OAI.Optimization.LinearProgramming.Compression.ServiceSlotLex
import OAI.Optimization.LinearProgramming.Compression.ServiceSlotCursor

/-! Physical comparison of two words, with an existing suffix result in address register 23. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable
open RAM

structure Compared (s t : Memory ℚ) (a b : ℕ) : Prop where
  result : t.index 23 = prependCode a b (s.index 23)
  index : ∀ i, i≠23 → t.index i = s.index i
  data : ∀ i, i≠0 → i≠5 → i≠6 → t.data i=s.data i

theorem Compared.frame {s t : Memory ℚ} {a b : ℕ} (h : Compared s t a b) : SlotFrame s t :=
  ⟨fun i hi => h.index i (by omega),h.data⟩

def prependRegs : Block := .branch (.scalarLT 5 6) (.op (.addrConst 23 0))
  (.branch (.scalarLT 6 5) (.op (.addrConst 23 2)) .skip)

theorem prependRegs_spec (P : ℚ → Prop) (s : Memory ℚ) (a b : ℕ)
    (ha : s.data 5=(a:ℚ)) (hb : s.data 6=(b:ℚ)) (hs : SlotSafe P s) :
    ∃ t k, k≤4 ∧ Block.Eval (SlotSafe P) prependRegs s k t ∧
      t.index 23=prependCode a b (s.index 23) ∧ t.data=s.data ∧ ∀ i, i≠23 → t.index i=s.index i := by
  rcases lt_trichotomy a b with h|h|h
  · have test : (Cond.scalarLT 5 6).test s=true := by simp [Cond.test,ha,hb,h]
    exact ⟨s.putIndex 23 0,3,by decide,.branchTrue test (Block.Eval.op_addrConst _ _ _ hs hs),
      by simp [prependCode,h],rfl,fun i hi => Memory.putIndex_ne _ hi _⟩
  · subst b
    have test : (Cond.scalarLT 5 6).test s=false := by simp [Cond.test,ha,hb]
    have test' : (Cond.scalarLT 6 5).test s=false := by simp [Cond.test,ha,hb]
    exact ⟨s,2,by decide,.branchFalse test (.branchFalse test' (.skip hs)),by simp [prependCode],
      rfl,fun _ _ => rfl⟩
  · have test : (Cond.scalarLT 5 6).test s=false := by simp [Cond.test,ha,hb,h.not_gt]
    have test' : (Cond.scalarLT 6 5).test s=true := by simp [Cond.test,ha,hb,h]
    exact ⟨s.putIndex 23 2,4,by decide,.branchFalse test (.branchTrue test' (Block.Eval.op_addrConst _ _ _ hs hs)),
      by simp [prependCode,h,h.not_gt],rfl,fun i hi => Memory.putIndex_ne _ hi _⟩

/-- Compute both paired keys, then prepend the result to the already compared suffix. -/
def comparePairs : Block := .seq (loadPairedSlot 5 24 25) (.seq (loadPairedSlot 6 26 27) prependRegs)

theorem comparePairs_spec (P : ℚ → Prop) (s : Memory ℚ) (n a b c d : ℕ)
    (h24 : s.data (s.index 24)=(a:ℚ)) (h25 : s.data (s.index 25)=(b:ℚ))
    (h26 : s.data (s.index 26)=(c:ℚ)) (h27 : s.data (s.index 27)=(d:ℚ))
    (h25' : 7≤ s.index 25) (h26' : 7≤ s.index 26) (h27' : 7≤ s.index 27)
    (ha : a≤ n) (hb : b≤ n) (hc : c≤ n) (hd : d≤ n)
    (hs : SlotSafe P s) (hp : ∀ x≤4*(n+1)^2,P (x:ℚ)) :
    ∃ t k, k≤18 ∧ Block.Eval (SlotSafe P) comparePairs s k t ∧ Compared s t (Nat.pair a b) (Nat.pair c d) := by
  obtain ⟨s₁,k₁,hk₁,e₁,v₁,i₁,f₁⟩ := loadPairedSlot_spec P s n 5 24 25 a b (by decide)
    (by omega) h24 h25 ha hb hs hp
  obtain ⟨s₂,k₂,hk₂,e₂,v₂,i₂,f₂⟩ := loadPairedSlot_spec P s₁ n 6 26 27 c d (by decide)
    (by rw [i₁]; omega) (by rw [i₁,f₁ _ (by omega) (by omega)]; exact h26)
    (by rw [i₁,f₁ _ (by omega) (by omega)]; exact h27) hc hd e₁.safe_end hp
  obtain ⟨t,k,hk,run,hr,data,idx⟩ := prependRegs_spec P s₂ _ _
    ((f₂ 5 (by decide) (by decide)).trans v₁) v₂ e₂.safe_end
  exact ⟨t,k₁+(k₂+k),by omega,e₁.seq (e₂.seq run),
    ⟨by simpa only [i₂,i₁] using hr,fun j hj => by simpa only [i₂,i₁] using idx j hj,
     fun j h0 h5 h6 => by rw [data,f₂ j h0 h6,f₁ j h0 h5]⟩⟩

/-- Read two ordinary integer header words and compare them ahead of the previous suffix. -/
def compareHeaders : Block := .seq (.op (.load 5 24)) (.seq (.op (.load 6 26)) prependRegs)

theorem compareHeaders_spec (P : ℚ → Prop) (s : Memory ℚ) (a b : ℕ)
    (h24 : s.data (s.index 24)=(a:ℚ)) (h26 : s.data (s.index 26)=(b:ℚ))
    (h26' : 7≤ s.index 26) (hs : SlotSafe P s) :
    ∃ t k, k≤6 ∧ Block.Eval (SlotSafe P) compareHeaders s k t ∧ Compared s t a b := by
  let s₁ := s.putData 5 (s.data (s.index 24))
  let s₂ := s₁.putData 6 (s₁.data (s₁.index 26))
  have hs₁ : SlotSafe P s₁ := fun i => by by_cases hi : i=5 <;> simp [s₁,hi,hs]
  have hs₂ : SlotSafe P s₂ := fun i => by by_cases hi : i=6 <;> simp [s₂,hi,hs₁]
  have ea := Block.Eval.op_load s 5 24 hs hs₁
  have eb := Block.Eval.op_load s₁ 6 26 hs₁ hs₂
  obtain ⟨t,k,hk,ec,hr,data,idx⟩ := prependRegs_spec P s₂ a b
    (by simp [s₂,s₁,h24]) (by
      change (s₁.putData 6 _).data 6 = _
      rw [Memory.putData_same]
      change (s.putData 5 _).data (s.index 26) = _
      rw [Memory.putData_ne _ (by omega : s.index 26 ≠ 5)]
      exact h26) hs₂
  exact ⟨t,1+(1+k),by omega,ea.seq (eb.seq ec),⟨hr,idx,
    fun j h0 h5 h6 => by rw [data]; simp [s₂,s₁,h5,h6]⟩⟩

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
