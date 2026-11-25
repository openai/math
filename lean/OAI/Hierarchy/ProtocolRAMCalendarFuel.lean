import OAI.Hierarchy.ProtocolRAMCalendar

namespace OAI
/-! # Reading a completely paid epoch from the chronological mode words -/

namespace Hierarchy.ProtocolRAM.Calendar
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing Classical
noncomputable section

def externalCap (c : Mesh) (H : Attempt→ℕ) (p : ℕ) : Prop :=
  c.outerFuel=0 ∨ ∃ i<p,H (.outer i (c.outerFuel-1))=2 ∨ H (.outer i (c.outerFuel-1))=3

def reserveCap (c : Mesh) (H : Attempt→ℕ) (p a j : ℕ) : Prop :=
  c.innerFuel=0 ∨ ∃ i<j,H (.inner p a i (c.innerFuel-1))=2

def disabled (c : Mesh) (H : Attempt→ℕ) : Attempt→Prop
  | .outer p a => externalCap c H p ∨ ∃ i<a,H (.outer p i)=1
  | .inner p a j b => H (.outer p a)≠3 ∨ reserveCap c H p a j ∨ ∃ i<b,H (.inner p a j i)=1

def archive {w : ℕ} (addr : Attempt→ℕ) (m : Memory w) : Attempt→ℕ := fun a=>(m (addr a)).val

private theorem past {w : ℕ} (m : Memory w) (r : Word w) (f : ℕ→ℕ) (n v : ℕ)
    (yes no : Expr) (small : v<2^w) :
    (anyMode ((List.range n).map f) v yes no).eval m r =
      if ∃ j<n,(m (f j)).val=v then yes.eval m r else no.eval m r := by
  rw [anyMode_eval]
  congr 1
  ext
  constructor
  · rintro ⟨a,ha,eqv⟩
    obtain ⟨j,mem,rfl⟩ := List.mem_map.mp ha
    exact ⟨j,List.mem_range.mp mem,by simpa [Fin.val_cast_of_lt small] using congrArg Fin.val eqv⟩
  · rintro ⟨j,hj,eqv⟩
    exact ⟨f j,List.mem_map.mpr ⟨j,List.mem_range.mpr hj,rfl⟩,
      Fin.ext (by simpa [Fin.val_cast_of_lt small] using eqv)⟩

theorem stop_snapshot {w : ℕ} (c : Mesh) (addr : Attempt→ℕ) (a : Attempt)
    (m : Memory w) (r : Word w) (wide : 4≤2^w) :
    (stop c addr a).eval m r = if disabled c (archive addr m) a then 1 else 0 := by
  have one : 1<2^w := by omega
  have two : 2<2^w := by omega
  have three : 3<2^w := by omega
  cases a with
  | outer p i =>
    by_cases fuel : c.outerFuel=0
    · simp [stop,outerSaturated,disabled,externalCap,fuel,Expr.eval]
    · simp only [stop,outerSaturated,fuel,ite_false,past _ _ _ _ 2 _ _ two,past _ _ _ _ 3 _ _ three,
        closed,past _ _ _ _ 1 _ _ one,disabled,externalCap,archive,Expr.eval,Nat.cast_zero,Nat.cast_one]
      split_ifs <;> first | rfl | exfalso; grind
  | inner p i j b =>
    have eqv : m (addr (.outer p i))=(3:Word w) ↔ (m (addr (.outer p i))).val=3 := by
      rw [Fin.ext_iff,show (3:Word w).val=3 from Fin.val_cast_of_lt three]
    by_cases fuel : c.innerFuel=0
    · simp [stop,disabled,reserveCap,innerSaturated,archive,word_eval,Expr.eval,Comparison.test,fuel]
    · simp only [stop,innerSaturated,fuel,ite_false,innerClosed,Expr.eval,word_eval,Comparison.test,
        beq_iff_eq,past _ _ _ _ 2 _ _ two,past _ _ _ _ 1 _ _ one,disabled,reserveCap,archive,
        Nat.cast_zero,Nat.cast_one]
      split_ifs <;> first | rfl | exfalso; grind

/-- A chronological guard certifies either a zero mode or one of the active
modes. For reserve ticks purchase is excluded by the mode circuit itself. -/
def innerLaw (c : Mesh) (H : Attempt→ℕ) (p a j : ℕ) : Prop :=
  ∀ b<c.innerFuel, let x := Attempt.inner p a j b
    if disabled c H x then H x=0 else H x=1 ∨ H x=2

def outerLaw (c : Mesh) (H : Attempt→ℕ) (p : ℕ) : Prop :=
  ∀ a<c.outerFuel, let x := Attempt.outer p a
    if disabled c H x then H x=0 else H x=1 ∨ H x=2 ∨ H x=3

theorem all_inner_repairs_of_last (c : Mesh) (H : Attempt→ℕ) (p a j : ℕ)
    (positive : 0<c.innerFuel) (law : innerLaw c H p a j)
    (last : H (.inner p a j (c.innerFuel-1))=2) :
    ∀ b<c.innerFuel,H (.inner p a j b)=2 := by
  let n := c.innerFuel-1
  have lt : n<c.innerFuel := by dsimp [n]; omega
  have endActive : ¬disabled c H (.inner p a j n) := by
    intro hd
    have hz := law n lt
    rw [ite_eq_left hd] at hz
    change H (.inner p a j n)=0 at hz
    exact (by decide : (0:ℕ) ≠ 2) (hz.symm.trans last)
  intro b hb
  by_cases eqn : b=n
  · simpa [eqn,n] using last
  have before : b<n := by dsimp [n] at *; omega
  have active : ¬disabled c H (.inner p a j b) := by
    rintro (bad|bad|⟨i,hi,done⟩)
    · exact endActive (Or.inl bad)
    · exact endActive (Or.inr (Or.inl bad))
    · exact endActive (Or.inr (Or.inr ⟨i,hi.trans before,done⟩))
  have modes := law b hb
  rw [ite_eq_right active] at modes
  exact modes.resolve_left (fun done=>endActive (Or.inr (Or.inr ⟨b,before,done⟩)))

theorem innerSaturated_paid (c : Mesh) (H : Attempt→ℕ) (p a j : ℕ)
    (positive : 0<c.innerFuel) (law : ∀ i<j,innerLaw c H p a i) (cap : reserveCap c H p a j) :
    ∃ i<j,∀ b<c.innerFuel,H (.inner p a i b)=2 := by
  obtain h | ⟨i,hi,last⟩ := cap
  · omega
  exact ⟨i,hi,all_inner_repairs_of_last c H p a i positive (law i hi) last⟩

theorem all_outer_paid_of_last (c : Mesh) (H : Attempt→ℕ) (p : ℕ) (positive : 0<c.outerFuel)
    (law : outerLaw c H p) (last : H (.outer p (c.outerFuel-1))=2 ∨ H (.outer p (c.outerFuel-1))=3) :
    ∀ a<c.outerFuel,H (.outer p a)=2 ∨ H (.outer p a)=3 := by
  let n := c.outerFuel-1
  have lt : n<c.outerFuel := by dsimp [n]; omega
  have endActive : ¬disabled c H (.outer p n) := by
    intro hd
    have hz := law n lt
    rw [ite_eq_left hd] at hz
    change H (.outer p n)=0 at hz
    rcases last with two | three
    · exact (by decide : (0:ℕ) ≠ 2) (hz.symm.trans two)
    · exact (by decide : (0:ℕ) ≠ 3) (hz.symm.trans three)
  intro a ha
  by_cases eqn : a=n
  · simpa [eqn,n] using last
  have before : a<n := by dsimp [n] at *; omega
  have active : ¬disabled c H (.outer p a) := by
    rintro (bad|⟨i,hi,done⟩)
    · exact endActive (Or.inl bad)
    · exact endActive (Or.inr ⟨i,hi.trans before,done⟩)
  have modes := law a ha
  rw [ite_eq_right active] at modes
  exact modes.resolve_left (fun done=>endActive (Or.inr ⟨a,before,done⟩))

end
end Hierarchy.ProtocolRAM.Calendar

end OAI
