import OAI.Optimization.LinearProgramming.Compression.CircuitMachineTrace

/-! A register invariant for the entire scalar RAM trace of an arithmetic expression. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression

open RAM

/-- Every value computed at any node of the arithmetic expression satisfies the predicate. -/
def ArithExpr.AllValues {ι K : Type*} [Ring K] (v : ι → K) (P : K → Prop) :
    ArithExpr ι → Prop
  | .zero => P 0
  | .one => P 1
  | .read i => P (v i)
  | .neg a => P (-(a.eval v)) ∧ a.AllValues v P
  | .add a b => P (a.eval v + b.eval v) ∧ a.AllValues v P ∧ b.AllValues v P
  | .mul a b => P (a.eval v * b.eval v) ∧ a.AllValues v P ∧ b.AllValues v P

theorem ArithExpr.AllValues.mono {ι K : Type*} [Ring K] {v : ι → K} {P Q : K → Prop}
    (h : ∀ x, P x → Q x) {e : ArithExpr ι} (he : e.AllValues v P) : e.AllValues v Q := by
  induction e with
  | zero | one | read => exact h _ he
  | neg a ih => exact ⟨h _ he.1, ih he.2⟩
  | add a b ia ib | mul a b ia ib => exact ⟨h _ he.1, ia he.2.1, ib he.2.2⟩

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem BlockExec.deterministic {p : Program} {s t t' : State K}
    (h : BlockExec p s t) (h' : BlockExec p s t') : t = t' := by
  induction h generalizing t' with
  | nil => cases h'; rfl
  | cons _ hi _ _ ih =>
    cases h' with
    | cons _ hi' _ htail =>
      rw [hi] at hi'
      cases Option.some.inj hi'
      exact ih htail

/-- An execution in which the register predicate holds before and after every step. -/
inductive SafeBlock (P : K → Prop) : Program → State K → State K → Prop
  | nil (s) (safe : ∀ j, P (s.data j)) : SafeBlock P [] s s
  | cons {i is s u t} (safe : ∀ j, P (s.data j)) (hlive : s.output = none)
      (hi : execInstr i s = some u) (hpc : u.pc = s.pc+1) (tail : SafeBlock P is u t) :
      SafeBlock P (i::is) s t

namespace SafeBlock

variable {P : K → Prop}

theorem toBlockExec {p : Program} {s t : State K} (h : SafeBlock P p s t) : BlockExec p s t := by
  induction h with
  | nil => exact .nil _
  | cons _ hlive hi hpc _ ih => exact .cons hlive hi hpc ih

theorem last_ok {p : Program} {s t : State K} (h : SafeBlock P p s t) : ∀ j, P (t.data j) := by
  induction h with
  | nil _ hs => exact hs
  | cons _ _ _ _ _ ih => exact ih

theorem single {i : Instr} {s u : State K} (hs : ∀ j, P (s.data j))
    (hlive : s.output = none) (hi : execInstr i s = some u) (hpc : u.pc = s.pc+1)
    (hu : ∀ j, P (u.data j)) : SafeBlock P [i] s u :=
  .cons hs hlive hi hpc (.nil u hu)

theorem append {a b : Program} {s u t : State K}
    (h : SafeBlock P a s u) (g : SafeBlock P b u t) : SafeBlock P (a ++ b) s t := by
  induction h with
  | nil => exact g
  | cons hs hlive hi hpc _ ih => exact .cons hs hlive hi hpc (ih g)

omit [Field K] [LinearOrder K] [IsStrictOrderedRing K] in
/-- A single scalar write preserves the register predicate exactly when the new scalar also
satisfies it. -/
theorem put_ok (s : State K) (hs : ∀ j, P (s.data j)) (d : ℕ) (x : K) (hx : P x) :
    ∀ j, P ((s.putData d x).data j) := by
  intro j
  by_cases hj : j = d
  · subst j
    simpa [State.putData] using hx
  · simpa [State.putData, Function.update_of_ne hj] using hs j

/-- The invariant covers each register at every position of the actual ambient-program trace. -/
theorem trace_of_layout {code p : Program} {s t : State K} (h : SafeBlock P code s t)
    (layout : ∀ j : Fin code.length, p[s.pc + j.val]? = some code[j.val]) :
    ∃ v : Fin (code.length+1) → State K, Trace p s code.length v ∧
      v (Fin.last _) = t ∧ ∀ i j, P ((v i).data j) := by
  induction h with
  | nil s hs =>
    exact ⟨fun _ => s, ⟨rfl, fun i => Fin.elim0 i⟩, rfl, fun _ => hs⟩
  | @cons i is s u t hs hlive hi hpc tail ih =>
    have suffixLayout (j : Fin is.length) : p[u.pc + j.val]? = some is[j.val] := by
      have hj := layout j.succ
      rw [hpc]
      simpa [Nat.add_assoc, Nat.add_left_comm, Nat.add_comm] using hj
    obtain ⟨v, ⟨hv0, hvstep⟩, hvlast, hsafe⟩ := ih suffixLayout
    let w : Fin ((i::is).length+1) → State K := Fin.cons s v
    refine ⟨w, ⟨by simp [w], ?_⟩, (Fin.cons_last ..).trans hvlast, ?_⟩
    · intro j
      refine Fin.cases ?_ (fun k => ?_) j
      · have hlookup : p[s.pc]? = some i := by simpa using layout 0
        change step p s = some (v 0)
        rw [hv0]
        simpa [step, hlive, hlookup] using hi
      · exact hvstep k
    · intro j
      exact Fin.cases (by simpa [w] using hs) (fun k => by simpa [w] using hsafe k) j

theorem trace_append {code : Program} {s t : State K} (h : SafeBlock P code s t)
    (pre suffix : Program) (hpc : s.pc = pre.length) :
    ∃ v : Fin (code.length+1) → State K, Trace (pre ++ code ++ suffix) s code.length v ∧
      v (Fin.last _) = t ∧ ∀ i j, P ((v i).data j) := by
  apply h.trace_of_layout
  intro j
  rw [List.append_assoc, hpc, List.getElem?_append_right (by omega)]
  simp [List.getElem?_append_left j.isLt, j.isLt]

end SafeBlock

namespace ArithExpr

variable {ι : Type*}

theorem spec_of_block (e : ArithExpr ι) (addr : ι → ℕ) (base : ℕ) (s t : State K)
    (hlive : s.output = none) (hfresh : ∀ i, addr i < base)
    (h : BlockExec (e.compile addr base) s t) :
    t.data base = e.eval (fun i => s.data (addr i)) ∧
      (∀ j < base, t.data j = s.data j) ∧ t.index = s.index ∧ t.output = none := by
  obtain ⟨u, hu, hrest⟩ := e.compile_spec addr base s hlive hfresh
  rwa [← hu.deterministic h]

private theorem binary_safe (s : State K) (addr : ι → ℕ) (base : ℕ)
    (a b : ArithExpr ι) (op : ℕ → ℕ → ℕ → Instr) (f : K → K → K) {P : K → Prop}
    (hop : ∀ (w : State K) (d i j : ℕ),
      execInstr (op d i j) w = some (w.putData d (f (w.data i) (w.data j))))
    (hlive : s.output = none) (hfresh : ∀ i, addr i < base)
    (hval : P (f (a.eval (fun i => s.data (addr i))) (b.eval (fun i => s.data (addr i)))))
    (ha : ∃ u, SafeBlock P (a.compile addr base) s u)
    (hb : ∀ u : State K, u.output = none → (∀ j, P (u.data j)) →
      (fun i => u.data (addr i)) = (fun i => s.data (addr i)) →
      ∃ v, SafeBlock P (b.compile addr (base+1)) u v) :
    ∃ t, SafeBlock P (a.compile addr base ++ b.compile addr (base+1) ++
      [op base base (base+1)]) s t := by
  obtain ⟨u, hu⟩ := ha
  obtain ⟨huval, huf, _, huo⟩ := a.spec_of_block addr base s u hlive hfresh hu.toBlockExec
  have hin : (fun i => u.data (addr i)) = (fun i => s.data (addr i)) := funext fun i => huf _ (hfresh i)
  obtain ⟨v, hv⟩ := hb u huo hu.last_ok hin
  obtain ⟨hvval, hvf, _, hvo⟩ := b.spec_of_block addr (base+1) u v huo
    (fun i => Nat.lt_succ_of_lt (hfresh i)) hv.toBlockExec
  have hres : P (f (v.data base) (v.data (base+1))) := by
    rwa [hvf base (Nat.lt_succ_self _), huval, hvval, hin]
  exact ⟨_, (hu.append hv).append (.single hv.last_ok hvo (hop ..) rfl
    (SafeBlock.put_ok v hv.last_ok base _ hres))⟩

/-- All intermediate scalar registers satisfy any bound on the inputs, zero, and the
values of every subexpression. -/
theorem compile_safe (e : ArithExpr ι) (addr : ι → ℕ) (base : ℕ) (s : State K)
    (hlive : s.output = none) (hfresh : ∀ i, addr i < base) {P : K → Prop}
    (initial : ∀ j, P (s.data j)) (hzero : P 0)
    (h : e.AllValues (fun i => s.data (addr i)) P) :
    ∃ t, SafeBlock P (e.compile addr base) s t := by
  induction e generalizing base s with
  | zero =>
    exact ⟨_, .single initial hlive (by simp [execInstr]) rfl (SafeBlock.put_ok s initial base 0 hzero)⟩
  | one =>
    exact ⟨_, .single initial hlive (by simp [execInstr]) rfl (SafeBlock.put_ok s initial base 1 h)⟩
  | read i =>
    exact ⟨_, .single initial hlive rfl rfl (SafeBlock.put_ok s initial base _ h)⟩
  | neg a ih =>
    obtain ⟨u, hu⟩ := ih (base+1) s hlive (fun i => Nat.lt_succ_of_lt (hfresh i)) initial h.2
    obtain ⟨huval, _, _, huo⟩ := a.spec_of_block addr (base+1) s u hlive
      (fun i => Nat.lt_succ_of_lt (hfresh i)) hu.toBlockExec
    let v := u.putData base 0
    have hvs : ∀ j, P (v.data j) := SafeBlock.put_ok u hu.last_ok base 0 hzero
    have hv : SafeBlock P [.const base 0] u v := .single hu.last_ok huo (by simp [execInstr, v]) rfl hvs
    have hsub : P (v.data base - v.data (base+1)) := by simpa [v, State.putData, huval] using h.1
    have hw : SafeBlock P [.sub base base (base+1)] v _ := .single hvs huo rfl rfl
      (SafeBlock.put_ok v hvs base _ hsub)
    exact ⟨_, hu.append (hv.append hw)⟩
  | add a b iha ihb =>
    apply binary_safe s addr base a b Instr.add (· + ·) (fun _ _ _ _ => rfl) hlive hfresh h.1
      (iha base s hlive hfresh initial h.2.1)
    intro u huo hus hin
    exact ihb (base+1) u huo (fun i => Nat.lt_succ_of_lt (hfresh i)) hus (hin ▸ h.2.2)
  | mul a b iha ihb =>
    apply binary_safe s addr base a b Instr.mul (· * ·) (fun _ _ _ _ => rfl) hlive hfresh h.1
      (iha base s hlive hfresh initial h.2.1)
    intro u huo hus hin
    exact ihb (base+1) u huo (fun i => Nat.lt_succ_of_lt (hfresh i)) hus (hin ▸ h.2.2)

end ArithExpr

end Compression
end LinearProgramming
end Optimization
end OAI
