import OAI.Computability.MultitapeWeakETH.TraceTables

/-! # Gluing the three parts of a physical trace history -/

namespace OAI.Computability.MultitapeWeakETH.PhysicalBlocks

open scoped Classical
noncomputable section

variable {M : Machine} {n b T : ℕ}

structure Stages (hb : 0 < b) (T : ℕ) (base : ℕ → M.Tapes → ℤ) (allowed : ℕ → M.Choice → Prop)
    (x y out : Word n) (mem : ℕ → Memory M b) : Prop where
  startMem : mem 0 = store hb (.running (MultitapeWeakETH.initial M (fun _ => false) y))
  load : ∀ j < n ⌈/⌉ b, ∀ k, mem (j+1) k = insertBits hb j x k (mem j k)
  epoch : ∀ j < epochs T b, let t := n ⌈/⌉ b + j
    EpochStep hb T base allowed j (mem t) (mem (t+1)) ∧
      ∀ k ∉ epochKeys M (base j), mem (t+1) k = mem t k
  output : ∀ j < n ⌈/⌉ b, let t := n ⌈/⌉ b + epochs T b + j
    mem (t+1) = mem t ∧ ∀ i : Fin n, block b i = j →
      readCell hb (mem t) M.output (M.offset n+i.val) = M.bit (out i)

theorem history_iff_stages (hb : 0 < b) (T : ℕ) (base : ℕ → M.Tapes → ℤ)
    (allowed : ℕ → M.Choice → Prop) (x y out : Word n) :
    History hb T base allowed x y out ↔ ∃ mem, Stages hb T base allowed x y out mem := by
  let m := n ⌈/⌉ b
  let e := epochs T b
  have hm : n ⌈/⌉ b = m := rfl
  have he : epochs T b = e := rfl
  constructor
  · rintro ⟨mem,start,h⟩
    refine ⟨mem,start,?_,?_,?_⟩
    · intro j hj k
      let v := inVertex n b T ⟨j,hj⟩
      have test := h v
      change testStage hb T base allowed v (mem j) (mem (j+1)) x out ∧ _ at test
      have eq : v.val = j := rfl
      simp only [testStage,schedule,eq,hj,ite_true,InputStep] at test
      by_cases hk : k ∈ ioKeys M (leftTape M) (leftStart M n) n b j
      · exact test.1 k hk
      · exact (test.2 k hk).trans (insertBits_outside hb j x k hk _).symm
    · intro j hj
      let v : Fin (vertices n b T) := ⟨m+j,by change m+j < m+e+m; dsimp [e] at *; omega⟩
      have test := h v
      have eq : v.val = m+j := rfl
      have m₁ : ¬ m+j < m := by omega
      have m₂ : m+j < m+e := by dsimp [e]; omega
      simpa only [testStage,schedule,eq,hm,he,
        m₁,m₂,ite_false,ite_true,Nat.add_sub_cancel_left] using test
    · intro j hj
      let v := outVertex n b T ⟨j,hj⟩
      have test := h v
      have eq : v.val = m+e+j := rfl
      have m₁ : ¬ m+e+j < m := by omega
      have m₂ : ¬ m+e+j < m+e := by omega
      change (if v.val < m then _ else if v.val < m+e then _ else _) ∧ _ at test
      simp only [schedule,eq,m₁,m₂,ite_false,Nat.add_sub_cancel_left,OutputStep,
        hm,he] at test
      refine ⟨funext (fun k => ?_),test.1.2⟩
      by_cases hk : k ∈ ioKeys M M.output (M.offset n) n b j
      · exact (test.1.1 k hk).symm
      · exact test.2 k hk
  · rintro ⟨mem,st⟩
    refine ⟨mem,st.startMem,fun v => ?_⟩
    change (if v.val < m then _ else if v.val < m+e then _ else _) ∧ _
    by_cases iv : v.val < m
    · simp only [iv,ite_true,schedule,hm]
      refine ⟨fun k _ => st.load v.val iv k,fun k hk => ?_⟩
      exact (st.load v.val iv k).trans (insertBits_outside hb _ x k hk _)
    · by_cases ev : v.val < m+e
      · have hj : v.val - m < e := by omega
        have add : m+(v.val-m) = v.val := by omega
        simpa only [testStage,schedule,hm,he,
          iv,ev,ite_true,ite_false,add] using st.epoch (v.val-m) hj
      · have hv : v.val < m+e+m := v.isLt
        have hj : v.val - (m+e) < m := by omega
        have add : m+e+(v.val-(m+e)) = v.val := by omega
        obtain ⟨eq,reads⟩ := st.output (v.val-(m+e)) hj
        change mem (m+e+(v.val-(m+e))+1) = mem (m+e+(v.val-(m+e))) at eq
        rw [add] at eq
        simp only [schedule,hm,he,
          iv,ev,ite_false,OutputStep]
        exact ⟨⟨fun k _ => congrFun eq.symm k,by simpa only [hm,
          he,add] using reads⟩,fun k _ => congrFun eq k⟩

theorem Stages.loaded {hb : 0 < b} {base : ℕ → M.Tapes → ℤ} {allowed : ℕ → M.Choice → Prop}
    {x y out : Word n} {mem : ℕ → Memory M b} (st : Stages hb T base allowed x y out mem) :
    mem (n ⌈/⌉ b) = store hb (.running (initial M x y)) := by
  have track (j : ℕ) (hj : j ≤ n ⌈/⌉ b) :
      mem j = store hb (.running (initial M (loadedPrefix x b j) y)) := by
    induction j with
    | zero => simpa only [prefix_zero] using st.startMem
    | succ j ih =>
      funext k
      rw [st.load j (by omega),ih (by omega),prefix_succ]
  simpa [prefix_all hb] using track (n ⌈/⌉ b) le_rfl

theorem Stages.written {hb : 0 < b} {base : ℕ → M.Tapes → ℤ} {allowed : ℕ → M.Choice → Prop}
    {x y out : Word n} {mem : ℕ → Memory M b} (st : Stages hb T base allowed x y out mem)
    (i : Fin n) : readCell hb (mem (n ⌈/⌉ b + epochs T b)) M.output (M.offset n+i.val) = M.bit (out i) := by
  let endTime := n ⌈/⌉ b + epochs T b
  have same (j : ℕ) (hj : j ≤ n ⌈/⌉ b) : mem (endTime+j) = mem endTime := by
    induction j with
    | zero => rfl
    | succ j ih => exact ((st.output j (by omega)).1).trans (ih (by omega))
  have small : n-1-i.val < b*(n ⌈/⌉ b) :=
    lt_of_lt_of_le (by omega : n-1-i.val < n) ((ceilDiv_le_iff_le_mul hb).mp le_rfl)
  have hj : block b i < n ⌈/⌉ b := (Nat.div_lt_iff_lt_mul hb).mpr (by simpa [mul_comm] using small)
  exact (congrArg (fun a => readCell hb a M.output (M.offset n+i.val)) (same _ hj.le).symm).trans
    ((st.output _ hj).2 i rfl)

end
end OAI.Computability.MultitapeWeakETH.PhysicalBlocks
