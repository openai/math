import OAI.ThreeFlat.Diagonal.TraceSourceDigits

namespace OAI
/-! # Partially occupied rectangular hidden-variable slots in each physical lane -/

namespace ThreeFlat.Diagonal.TraceSourceOwner

/-- Candidate hidden ordinal for a rectangular reservation in a physical row. -/
def unplace (s : Shape) (v : ℕ) : ℕ → ℕ :=
  appendAt (2*s.cpu)
    (fun j => (2*v+j/s.cpu-s.header)*s.cpu+j%s.cpu)
    (fun a => s.ticks*s.cpu+appendAt (s.layers*s.track)
      (fun j => (j/s.track)*(s.rows*s.track)+(v*s.track+j%s.track))
      (fun b => s.layers*(s.rows*s.track)+appendAt s.edge (fun j => v*s.edge+j)
        (fun c => (s.rows-1)*s.edge+appendAt s.copy (fun j => v*s.copy+j)
          (fun j => s.rows*s.copy+(v*s.gates+j)) c) b) a)

private theorem split_sum {P : ℕ → Prop} {a b j : ℕ} (hj : j<a+b)
    (left : ∀ x<a, P x) (right : ∀ y<b, P (a+y)) : P j := by
  by_cases h : j<a
  · exact left _ h
  · obtain ⟨y,rfl⟩ := Nat.exists_eq_add_of_le (Nat.le_of_not_gt h)
    exact right _ (by omega)

private theorem split_prod {P : ℕ → Prop} {a b j : ℕ} (hj : j<a*b)
    (prod : ∀ x<a, ∀ y<b, P (x*b+y)) : P j := by
  have hb : 0<b := by by_contra! he; simp [show b=0 by omega] at hj
  have h := prod (j/b) ((Nat.div_lt_iff_lt_mul hb).2 hj) (j%b) (Nat.mod_lt _ hb)
  rwa [Nat.mul_comm (j/b) b,Nat.div_add_mod] at h

theorem cases_hidden (s : Shape) (P : ℕ → Prop)
    (cpu : ∀ t<s.ticks, ∀ j<s.cpu, P (t*s.cpu+j))
    (sort : ∀ l<s.layers, ∀ v<s.rows, ∀ j<s.track,
      P (s.ticks*s.cpu+(l*(s.rows*s.track)+(v*s.track+j))))
    (edge : ∀ v<s.rows-1, ∀ j<s.edge,
      P (s.ticks*s.cpu+(s.layers*(s.rows*s.track)+(v*s.edge+j))))
    (copy : ∀ v<s.rows, ∀ j<s.copy,
      P (s.ticks*s.cpu+(s.layers*(s.rows*s.track)+((s.rows-1)*s.edge+(v*s.copy+j)))))
    (gate : ∀ v<s.rows, ∀ j<s.gates,
      P (s.ticks*s.cpu+(s.layers*(s.rows*s.track)+((s.rows-1)*s.edge+(s.rows*s.copy+(v*s.gates+j))))))
    {i : ℕ} (hi : i<s.count) : P i := by
  let C := s.ticks*s.cpu
  let T := s.layers*(s.rows*s.track)
  let E := (s.rows-1)*s.edge
  let B := s.rows*s.copy
  refine split_sum (P:=P) hi (fun _ h => split_prod (P:=P) h cpu) ?_
  intro u hu
  refine split_sum (P:=fun z => P (C+z)) hu ?_ ?_
  · intro x hx
    refine split_prod (P:=fun z => P (C+z)) hx ?_
    intro l hl z hz
    exact split_prod (P:=fun a => P (C+(l*(s.rows*s.track)+a))) hz (sort l hl)
  · intro x hx
    refine split_sum (P:=fun z => P (C+(T+z))) hx ?_ ?_
    · intro j hj
      exact split_prod (P:=fun z => P (C+(T+z))) hj edge
    · intro j hj
      refine split_sum (P:=fun z => P (C+(T+(E+z)))) hj ?_ ?_
      · intro u hu
        exact split_prod (P:=fun z => P (C+(T+(E+z)))) hu copy
      · intro u hu
        exact split_prod (P:=fun z => P (C+(T+(E+(B+z))))) hu gate

theorem locate_spec (s : Shape) (fits : s.header+s.ticks ≤ 2*s.rows) {i : ℕ} (hi : i<s.count) :
    (locate s i).1<s.rows ∧ (locate s i).2<s.stride ∧ unplace s (locate s i).1 (locate s i).2=i := by
  refine cases_hidden s (fun z => (locate s z).1<s.rows ∧ (locate s z).2<s.stride ∧
    unplace s (locate s z).1 (locate s z).2=z) ?_ ?_ ?_ ?_ ?_ hi
  · intro t ht j hj
    rw [locate_cpu s ht hj]
    have hmod := Nat.mod_lt (s.header+t) (by decide : 0<2)
    have hslot := pack_lt hj hmod
    refine ⟨by dsimp only; omega,by dsimp only; unfold Shape.stride; omega,?_⟩
    simp only [unplace,appendAt_left _ _ hslot,pack_div hj,pack_mod hj]
    rw [Nat.div_add_mod,Nat.add_sub_cancel_left]
  · intro l hl v hv j hj
    rw [locate_sort s hl hv hj]
    have hslot := pack_lt hj hl
    refine ⟨hv,by dsimp only; unfold Shape.stride; omega,?_⟩
    simp only [unplace,appendAt_right,appendAt_left _ _ hslot,pack_div hj,pack_mod hj]
  · intro v hv j hj
    rw [locate_edge s hv hj]
    refine ⟨by dsimp only; omega,by dsimp only; unfold Shape.stride; omega,?_⟩
    simp only [unplace,appendAt_right,appendAt_left _ _ hj]
  · intro v hv j hj
    rw [locate_copy s hv hj]
    refine ⟨hv,by dsimp only; unfold Shape.stride; omega,?_⟩
    simp only [unplace,appendAt_right,appendAt_left _ _ hj]
  · intro v hv j hj
    rw [locate_gate s hj]
    refine ⟨hv,by dsimp only; unfold Shape.stride; omega,?_⟩
    simp only [unplace,appendAt_right]

/-- The partial inverse verifies its candidate's ordinal and forward image.
A failed test identifies a padding bit to be fixed to zero. -/
def decode (s : Shape) (v j : ℕ) : Option ℕ :=
  let h := unplace s v j
  if h<s.count ∧ locate s h=(v,j) then some h else none

theorem decode_some_iff (s : Shape) (fits : s.header+s.ticks ≤ 2*s.rows) (v j h : ℕ) :
    decode s v j = some h ↔ h<s.count ∧ locate s h=(v,j) := by
  constructor
  · intro hit
    unfold decode at hit
    dsimp only at hit
    split at hit
    · rename_i valid
      exact (Option.some.inj hit) ▸ valid
    · cases hit
  · rintro ⟨hi,hp⟩
    have u := (locate_spec s fits hi).2.2
    rw [hp] at u
    simp [decode,u,hi,hp]

def rowSlots (s : Shape) (fits : s.header+s.ticks ≤ 2*s.rows) :
    Fin s.count ↪ Fin s.rows × Fin s.stride where
  toFun i := (⟨(locate s i.val).1,(locate_spec s fits i.isLt).1⟩,
    ⟨(locate s i.val).2,(locate_spec s fits i.isLt).2.1⟩)
  inj' := by
    intro i j h
    have a := congrArg (fun p : Fin s.rows × Fin s.stride => unplace s p.1.val p.2.val) h
    exact Fin.ext (((locate_spec s fits i.isLt).2.2).symm.trans (a.trans (locate_spec s fits j.isLt).2.2))

end ThreeFlat.Diagonal.TraceSourceOwner

end OAI
