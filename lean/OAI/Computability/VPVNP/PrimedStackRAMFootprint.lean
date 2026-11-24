import OAI.Computability.VPVNP.PrimedStackRAMNative

/-!
# Header preservation by the complete parser visit

Successful scratch writes target the depth word, a guarded stack index, a
guarded mark or a guarded production index. The header words below the
rectangle, including the nominated histogram, are therefore available at
their original addresses for the final comparison.
-/

namespace OAI
namespace Computability
namespace VPVNP

namespace PrimedStackRAM

open BurstRAM
open scoped Fin.CommRing

variable {base R n m H w : ℕ}

/-- Agreement of two external memories at every address strictly below the scratch base,
including header words stored there. -/
def Below (base : ℕ) (m₀ m₁ : Memory w) : Prop := ∀ a < base, m₁ a = m₀ a

private theorem Below.trans {m₀ m₁ m₂ : Memory w} (h₀ : Below base m₀ m₁) (h₁ : Below base m₁ m₂) :
    Below base m₀ m₂ := fun a ha => (h₁ a ha).trans (h₀ a ha)

private theorem below_write (mem : Memory w) (v a : Word w) (h : base ≤ a.val) :
    Below base mem (writeMemory mem a v) := by
  intro b hb
  simp [writeMemory, show b ≠ a.val by omega]

private theorem cell_lower (c : Locations R n m H) (hf : base + size R n m (labelCount n m H) ≤ 2^w) :
    base ≤ (address base c : Word w).val := by
  rw [Fin.val_natCast, Nat.mod_eq_of_lt (address_lt hf c)]
  exact Nat.le_add_right ..

private structure Protects (base : ℕ) (pub : Fin 11 → Word w) (ops : List Line) : Prop where
  run : ∀ {st rs mem es rs' m'}, trace pub st ops rs mem = some (es,rs',m') → Below base mem m'

private theorem Protects.append {pub : Fin 11 → Word w} {xs ys : List Line}
    (hx : Protects base pub xs) (hy : Protects base pub ys) : Protects base pub (xs ++ ys) := by
  constructor
  intro st rs mem es rs' m' ht
  rw [trace_append] at ht
  obtain ⟨⟨ea,ra,ma⟩,ha,h⟩ := Option.bind_eq_some_iff.mp ht
  obtain ⟨⟨eb,rb,mb⟩,hb,he⟩ := Option.map_eq_some_iff.mp h
  cases he
  exact (hx.run ha).trans (hy.run hb)

/-- The non-writing opcode blocks retain all external memory words. -/
private theorem protects_readOnly {pub : Fin 11 → Word w} {ops : List Line}
    (ho : ∀ op ∈ ops, ∀ a b, op ≠ .write a b) : Protects base pub ops := by
  constructor
  intro st rs mem es rs' m' ht
  induction ops generalizing rs mem es with
  | nil => simp [trace] at ht; rw [← ht.2.2]; exact fun _ _ => rfl
  | cons op ops ih =>
    cases he : op.effect pub st rs mem with
    | none => simp [trace, he] at ht
    | some t =>
      obtain ⟨e,ra,ma⟩ := t
      cases htail : trace pub st ops ra ma with
      | none => simp [trace, he, htail] at ht
      | some z =>
        obtain ⟨eb,rb,mb⟩ := z
        simp [trace, he, htail] at ht
        obtain ⟨rfl,rfl,rfl⟩ := ht
        have hm : ma = mem := by
          cases op <;> simp [Op.effect] at he
          all_goals first
            | exact he.2.2.symm
            | exact he.2.2.2.symm
            | exact (ho _ (List.mem_cons_self ..) _ _ rfl).elim
        subst ma
        exact ih (fun a h => ho a (List.mem_cons_of_mem _ h)) htail

private theorem pop_protects (hf : base + size R n m (labelCount n m H) ≤ 2^w) :
    Protects base (publicData w base R n m H) pop := by
  let pub := publicData w base R n m H
  constructor
  intro st rs mem es rs' m' ht
  by_cases hz : 0 < mem (pub 4).val
  · obtain ⟨_,_,h,_⟩ := pop_spec pub st rs mem hz
    have hm := congrArg (fun x : List (Event w) × Regs w 16 × Memory w => x.2.2) (Option.some.inj (ht.symm.trans h))
    dsimp only at hm
    rw [hm]
    exact below_write _ _ _ (by rw [show (pub 4).val = _ from public_depth_val base hf]; exact Nat.le_add_right ..)
  · have h := pop_empty pub st rs mem (le_antisymm (not_lt.mp hz) (Fin.zero_le _))
    rw [ht] at h
    contradiction

private theorem push_protects (hf : base + size R n m (labelCount n m H) ≤ 2^w) :
    Protects base (publicData w base R n m H) push := by
  let pub := publicData w base R n m H
  constructor
  intro st rs mem es rs' m' ht
  by_cases hz : mem (pub 4).val < pub 5
  · obtain ⟨_,_,h,_⟩ := push_spec pub st rs mem hz
    have hm := congrArg (fun x : List (Event w) × Regs w 16 × Memory w => x.2.2) (Option.some.inj (ht.symm.trans h))
    dsimp only at hm
    rw [hm]
    have hd : (mem (pub 4).val).val < n := by
      change (mem _).val < (n : Word w).val at hz
      simpa only [Fin.val_natCast, Nat.mod_eq_of_lt (capacity_fit base hf)] using hz
    let i : Fin n := ⟨(mem (pub 4).val).val,hd⟩
    have hi : mem (pub 4).val = (i.val : Word w) := (Fin.cast_val_eq_self _).symm
    have hd₀ : base ≤ (pub 0 + mem (pub 4).val).val := by
      rw [hi, show pub 0 + (i.val : Word w) = _ from public_degree base i]
      exact cell_lower _ hf
    have hd₁ : base ≤ (pub 1 + mem (pub 4).val).val := by
      rw [hi, show pub 1 + (i.val : Word w) = _ from public_state base i]
      exact cell_lower _ hf
    exact (below_write mem _ _ hd₀).trans ((below_write _ _ _ hd₁).trans
      (below_write _ _ _ (by rw [show (pub 4).val = _ from public_depth_val base hf]; exact Nat.le_add_right ..)))
  · rw [push_full pub st rs mem hz] at ht
    contradiction

private theorem mark_protects (hf : base + size R n m (labelCount n m H) ≤ 2^w) :
    Protects base (publicData w base R n m H) mark := by
  let pub := publicData w base R n m H
  constructor
  intro st rs mem es rs' m' ht
  by_cases hi : rs 2 < pub 6
  · by_cases hnew : mem (pub 2 + rs 2).val = 0
    · obtain ⟨_,_,h,_⟩ := mark_spec pub st rs mem hi hnew
      have hm := congrArg (fun x : List (Event w) × Regs w 16 × Memory w => x.2.2) (Option.some.inj (ht.symm.trans h))
      dsimp only at hm
      rw [hm]
      have hw : m < 2^w := by unfold size at hf; omega
      have hj : (rs 2).val < m := by
        change (rs 2).val < (m : Word w).val at hi
        simpa only [Fin.val_natCast, Nat.mod_eq_of_lt hw] using hi
      let i : Fin m := ⟨(rs 2).val,hj⟩
      apply below_write
      rw [show rs 2 = (i.val : Word w) from (Fin.cast_val_eq_self _).symm,
        show pub 2 + (i.val : Word w) = _ from public_mark base i]
      exact cell_lower _ hf
    · rw [mark_reject pub st rs mem (Or.inr hnew)] at ht
      contradiction
  · rw [mark_reject pub st rs mem (Or.inl hi)] at ht
    contradiction

private theorem increment_protects (hf : base + size R n m (labelCount n m H) ≤ 2^w) :
    Protects base (publicData w base R n m H) increment := by
  let pub := publicData w base R n m H
  constructor
  intro st rs mem es rs' m' ht
  change trace pub st increment rs mem = _ at ht
  by_cases hi : rs 7 < pub 10
  · by_cases hval : mem (pub 3 + rs 7).val < mem (pub 3 + rs 7).val + Fin.ofNat (2^w) 1
    · simp at hval
      simp (config := {decide := true}) [increment,trace,Op.effect,PrivateRAM.BinaryOp.eval,Function.update,hi,hval] at ht
      rw [← ht.2.2]
      apply below_write
      have hw : labelCount n m H < 2^w := by unfold size at hf; omega
      have hj : (rs 7).val < labelCount n m H := by
        change (rs 7).val < (labelCount n m H : Word w).val at hi
        simpa only [Fin.val_natCast, Nat.mod_eq_of_lt hw] using hi
      let i : Fin (labelCount n m H) := ⟨(rs 7).val,hj⟩
      rw [show rs 7 = (i.val : Word w) from (Fin.cast_val_eq_self _).symm,
        show pub 3 + (i.val : Word w) = _ from public_count base i]
      exact cell_lower _ hf
    · simp at hval
      simp (config := {decide := true}) [increment,trace,Op.effect,PrivateRAM.BinaryOp.eval,Function.update,hi,not_lt.mpr hval] at ht
  · simp (config := {decide := true}) [increment,trace,Op.effect,Function.update,hi] at ht

private theorem choice_protects (c : RawChoice w) (hf : base + size R n m (labelCount n m H) ≤ 2^w) :
    Protects base (publicData w base R n m H) c.lines := by
  cases c with
  | leaf v =>
    change Protects _ _ ((mark ++ leafBit ++ terminalIndex) ++ increment)
    apply Protects.append _ (increment_protects hf)
    apply Protects.append _ (protects_readOnly (ops := terminalIndex) (by simp [terminalIndex]))
    exact Protects.append (mark_protects hf) (protects_readOnly (by simp [leafBit]))
  | binary b i j =>
    apply Protects.append
    · apply Protects.append _ (increment_protects hf)
      exact Protects.append (protects_readOnly (by simp [binaryChecks])) (protects_readOnly (by simp [binaryIndex]))
    · apply Protects.append (protects_readOnly (ops := rightFrame) (by simp [rightFrame]))
      exact Protects.append (push_protects hf) (Protects.append (protects_readOnly (by simp [leftFrame])) (push_protects hf))

/-- The final nomination comparison can read every original header word. This
also holds for an arbitrary initial memory whenever the physical call succeeds. -/
theorem completeNode_below {st : Word w} {rs : Regs w 16} {mem : Memory w} {bits : List Bool} {o : Output w 16}
    (hf : base + size R n m (labelCount n m H) ≤ 2^w)
    (hc : completeNode (publicData w base R n m H) st rs mem bits = some o) :
    ∀ a < base, o.mem a = mem a := by
  let pub := publicData w base R n m H
  cases hp : trace pub st pop rs mem with
  | none => simp [completeNode,nodeKernel,seqKernel,lineKernel,pub,hp] at hc
  | some z =>
    obtain ⟨es₀,r₀,m₀⟩ := z
    rw [completeNode_pop pub st rs r₀ mem m₀ es₀ bits hp] at hc
    obtain ⟨c,_,hc⟩ := Option.bind_eq_some_iff.mp hc
    obtain ⟨⟨_,_,m'⟩,ht,rfl⟩ := Option.map_eq_some_iff.mp hc
    exact ((pop_protects hf).run hp).trans ((choice_protects c hf).run ht)

end PrimedStackRAM

end VPVNP
end Computability
end OAI
