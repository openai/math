import OAI.LinearAlgebra.SpectralBooks.SignedWitness

/-! # Unique prefix witnesses for a padded sequence of unary fields

Each enabled slot consumes a run of ones and its terminating zero. Disabled
slots leave the input cursor fixed. The last cursor is the first payload bit.
-/

namespace OAI
namespace LinearAlgebra
namespace SpectralBooks

namespace SignedProgram.Unary

variable {n s : ℕ}

abbrev Slot (n : ℕ) := Option (Fin (n+1))

def emit : Slot n → List Bool
  | none => []
  | some v => ProgramCode.unary v.val

def serialize (f : Fin s → Slot n) := (List.ofFn f).flatMap emit

/-- One enabled or disabled field at the cursor. -/
def Step (x : Fin n → Bool) (b e : Fin (n+1)) (f : Slot n) : Prop :=
  e.val = b.val + (emit f).length ∧ emit f <+: (List.ofFn x).drop b.val

/-- One local cursor transition for each slot and a prescribed first cursor. -/
def Trace (x : Fin n → Bool) (b : Fin (n+1)) (f : Fin s → Slot n)
    (e : Fin (s+1) → Fin (n+1)) : Prop :=
  e 0 = b ∧ ∀ i, Step x (e i.castSucc) (e i.succ) (f i)

private theorem prefix_append {α : Type*} {l m x : List α} :
    l ++ m <+: x ↔ l <+: x ∧ m <+: x.drop l.length := by
  constructor
  · rintro ⟨t,rfl⟩
    rw [List.append_assoc, List.drop_left]
    exact ⟨List.prefix_append _ _, List.prefix_append _ _⟩
  · rintro ⟨⟨t,rfl⟩, ht⟩
    rw [List.drop_left] at ht
    obtain ⟨u,rfl⟩ := ht
    exact ⟨u, List.append_assoc _ _ _⟩

private theorem split_trace (x : Fin n → Bool) (b : Fin (n+1)) (f : Fin (s+1) → Slot n)
    (e : Fin (s+2) → Fin (n+1)) :
    Trace x b f e ↔ e 0 = b ∧ Step x b (Fin.tail e 0) (f 0) ∧
      Trace x (Fin.tail e 0) (Fin.tail f) (Fin.tail e) := by
  constructor
  · rintro ⟨h,hs⟩
    exact ⟨h, by simpa [Fin.tail, ← h] using hs 0, rfl, fun i => hs i.succ⟩
  · rintro ⟨h,hs,ht⟩
    refine ⟨h, Fin.cases ?_ (fun i => ht.2 i)⟩
    simpa [h, Fin.tail] using hs

theorem serialize_succ (f : Fin (s+1) → Slot n) :
    serialize f = emit (f 0) ++ serialize (Fin.tail f) := by
  unfold serialize
  rw [List.ofFn_succ (f := f), List.flatMap_cons]
  rfl

/-- The final cursor records the header and body length consumed so far. -/
theorem last_cursor {x : Fin n → Bool} {b : Fin (n+1)} {f : Fin s → Slot n}
    {e : Fin (s+1) → Fin (n+1)} (h : Trace x b f e) :
    (e (Fin.last s)).val = b.val + (serialize f).length := by
  induction s generalizing b with
  | zero => simpa [serialize] using congrArg Fin.val h.1
  | succ s ih =>
    obtain ⟨_, hf, ht⟩ := (split_trace x b f e).mp h
    have hh := ih ht
    change (e (Fin.last (s+1))).val = _ at hh
    rw [serialize_succ, List.length_append, ← Nat.add_assoc, ← hf.1]
    exact hh

theorem trace_unique {x : Fin n → Bool} {b : Fin (n+1)} {f : Fin s → Slot n}
    {e e' : Fin (s+1) → Fin (n+1)} (h : Trace x b f e) (h' : Trace x b f e') : e = e' := by
  induction s generalizing b with
  | zero => funext i; simpa [Fin.eq_zero i] using h.1.trans h'.1.symm
  | succ s ih =>
    obtain ⟨e0,hf,ht⟩ := (split_trace x b f e).mp h
    obtain ⟨e0',hf',ht'⟩ := (split_trace x b f e').mp h'
    have hstep : Fin.tail e' 0 = Fin.tail e 0 := Fin.ext (hf'.1.trans hf.1.symm)
    rw [hstep] at ht'
    have hh := ih ht ht'
    funext j
    exact Fin.cases (e0.trans e0'.symm) (fun i => congrFun hh i) j

theorem exists_trace_iff (x : Fin n → Bool) (b : Fin (n+1)) (f : Fin s → Slot n) :
    (∃ e, Trace x b f e) ↔ serialize f <+: (List.ofFn x).drop b.val := by
  induction s generalizing b with
  | zero => exact ⟨fun _ => by simp [serialize], fun _ => ⟨fun _ => b, rfl, fun i => i.elim0⟩⟩
  | succ s ih =>
    rw [serialize_succ, prefix_append]
    constructor
    · rintro ⟨e,he⟩
      obtain ⟨_, ⟨hlen,hpre⟩, htail⟩ := (split_trace x b f e).mp he
      refine ⟨hpre, ?_⟩
      rw [List.drop_drop, ← hlen]
      exact (ih _ _).mp ⟨_, htail⟩
    · rintro ⟨hpre,ht⟩
      have hbound := hpre.length_le
      simp only [List.length_drop, List.length_ofFn] at hbound
      let nxt : Fin (n+1) := ⟨b.val + (emit (f 0)).length, by have := b.isLt; omega⟩
      rw [List.drop_drop] at ht
      obtain ⟨es,hes⟩ := (ih nxt (Fin.tail f)).mpr ht
      refine ⟨Fin.cons b es, (split_trace x b f _).mpr ?_⟩
      simp only [Fin.tail_cons, Fin.cons_zero, hes.1]
      exact ⟨trivial, ⟨rfl,hpre⟩, hes⟩

/-- For any initial offset the cursor witnesses exist exactly when the serialization
is a prefix of the remaining input. When they exist every cursor is determined. -/
theorem existsUnique_trace_iff (x : Fin n → Bool) (b : Fin (n+1)) (f : Fin s → Slot n) :
    (∃! e, Trace x b f e) ↔ serialize f <+: (List.ofFn x).drop b.val := by
  rw [← exists_trace_iff]
  exact ⟨ExistsUnique.exists, fun ⟨e,he⟩ => ⟨e,he,fun _ h' => trace_unique h' he⟩⟩

theorem existsUnique_prefix (x : Fin n → Bool) (f : Fin s → Slot n) :
    (∃! e, Trace x 0 f e) ↔ serialize f <+: List.ofFn x := by
  simpa only [Fin.val_zero, List.drop_zero] using existsUnique_trace_iff x 0 f

/-- A one-hot cursor row starts at zero. An active current cursor reads a
matching field and forces every bit of its successor row. -/
def LocalCheck (x : Fin n → Bool) (f : Fin s → Slot n)
    (mark : Fin (s+1) → Fin (n+1) → Prop) : Prop :=
  (∀ j, mark 0 j ↔ j = 0) ∧ ∀ i, ∃ b e, mark i.castSucc b ∧ Step x b e (f i) ∧
    ∀ j, mark i.succ j ↔ j = e

theorem localCheck_iff (x : Fin n → Bool) (f : Fin s → Slot n)
    (mark : Fin (s+1) → Fin (n+1) → Prop) :
    LocalCheck x f mark ↔ ∃ e, Trace x 0 f e ∧ ∀ i j, mark i j ↔ j = e i := by
  constructor
  · rintro ⟨hz, hs⟩
    have h : ∀ i, ∃ b, ∀ j, mark i j ↔ j = b := by
      refine Fin.cases ⟨0,hz⟩ (fun i => ?_)
      obtain ⟨_,e,_,_,he⟩ := hs i
      exact ⟨e,he⟩
    choose e he using h
    refine ⟨e, ⟨?_, fun i => ?_⟩, he⟩
    · exact ((he 0 0).mp ((hz 0).mpr rfl)).symm
    · obtain ⟨b,e',hb,hstep,he'⟩ := hs i
      rwa [← (he _ b).mp hb, ← (he _ e').mp ((he' e').mpr rfl)]
  · rintro ⟨e,ht,he⟩
    refine ⟨fun j => by simpa only [ht.1] using he 0 j, fun i =>
      ⟨_, _, (he _ _).mpr rfl, ht.2 i, he _⟩⟩

/-- Among all Boolean endpoint arrays, precisely the canonical one can pass. -/
theorem existsUnique_marks_iff (x : Fin n → Bool) (f : Fin s → Slot n) :
    (∃! m : Fin (s+1) → Fin (n+1) → Bool, LocalCheck x f (fun i j => m i j = true)) ↔
      serialize f <+: List.ofFn x := by
  constructor
  · rintro ⟨m,hm,_⟩
    obtain ⟨e,he,_⟩ := (localCheck_iff _ _ _).mp hm
    simpa only [Fin.val_zero, List.drop_zero] using (exists_trace_iff x 0 f).mp ⟨e,he⟩
  · intro hp
    obtain ⟨e,he,hu⟩ := (existsUnique_prefix x f).mpr hp
    refine ⟨fun i j => decide (j = e i), (localCheck_iff _ _ _).mpr ⟨e,he,by simp⟩, ?_⟩
    intro m hm
    obtain ⟨e',he',hh⟩ := (localCheck_iff _ _ _).mp hm
    obtain rfl := hu _ he'
    funext i j
    apply Bool.eq_iff_iff.mpr
    simpa only [decide_eq_true_eq] using hh i j

end SignedProgram.Unary

end SpectralBooks
end LinearAlgebra
end OAI
