import OAI.Hierarchy.ProtocolRAMSchedule

namespace OAI
/-! # Native column-major scans of the subdivision rows -/

namespace Hierarchy.ProbeStage.Native
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing

def columns (n : ℕ) : (base : ℕ) → List Expr → List Pass
  | _,[] => []
  | base,e::es => ⟨base,n,e⟩ :: columns n (base+n) es

theorem columns_below {n base : ℕ} (es : List Expr) : ∀ p ∈ columns n base es, base ≤ p.out := by
  induction es generalizing base with
  | nil => simp [columns]
  | cons e es ih =>
    intro p hp
    rcases List.mem_cons.mp hp with eq | tail
    · subst p; exact le_rfl
    · exact (Nat.le_add_right base n).trans (ih p tail)

private theorem fits_later {w a b : ℕ} (e : Expr) (late : a≤b) (hf : e.Fits w a) : e.Fits w b := by
  induction e with
  | row | lit => trivial
  | lookup t i ih =>
    exact ⟨⟨hf.1.1,hf.1.2.1,hf.1.2.2.trans late⟩,ih hf.2⟩
  | op _ _ _ ih jh => exact ⟨ih hf.1,jh hf.2⟩
  | branch _ _ _ _ _ h₁ h₂ h₃ h₄ => exact ⟨h₁ hf.1,h₂ hf.2.1,h₃ hf.2.2.1,h₄ hf.2.2.2⟩

theorem columns_safe {n src base w : ℕ} (es : List Expr) (before : src≤base)
    (readers : ∀ e ∈ es,e.Fits w src) (room : base + es.length*n < 2^w) :
    ∀ p ∈ columns n base es, p.Fits w := by
  induction es generalizing base with
  | nil => simp [columns]
  | cons e es ih =>
    intro p hp
    rw [List.length_cons,Nat.succ_mul] at room
    rcases List.mem_cons.mp hp with eq | tail
    · subst p
      exact ⟨fits_later e before (readers e (.head _)),show base+n<2^w by omega⟩
    · exact ih (before.trans (Nat.le_add_right _ _)) (fun v hv => readers v (.tail _ hv))
        (by omega) p tail

theorem columns_exec {w n base : ℕ} (es : List Expr) (m : Memory w)
    (fits : ∀ p ∈ columns n base es, p.Fits w) :
    (program w (columns n base es)).Exec m (result (columns n base es) m) (clock (columns n base es)) :=
  program_exec _ _ fits

/-- The count only depends on the number and sizes of the expressions. -/
theorem columns_clock (n base W : ℕ) (es : List Expr) (hW : ∀ e∈es, e.work≤W) :
    clock (columns n base es) ≤ 4+es.length*(4+n*(2*W+4)) := by
  induction es generalizing base with
  | nil => simp [columns,clock]
  | cons e es ih =>
    have head := hW e (.head _)
    have tail := ih (base+n) (fun a ha => hW a (.tail _ ha))
    have cost := Nat.mul_le_mul_left n (show 2*e.work+4≤2*W+4 by omega)
    simp only [columns,clock,Pass.clock,List.length_cons,Nat.succ_mul es.length]
    omega

/-- Every output column evaluates against the original inputs. All columns
are later in memory than the banks read by the expressions. -/
theorem columns_read {w n src base : ℕ} (es : List Expr) (m : Memory w)
    (before : src≤base) (reader : ∀ e∈es, e.Fits w src)
    (j : ℕ) (hj : j<es.length) (r : Fin n) :
    result (columns n base es) m (base+j*n+r.val) = (es[j]'hj).eval m (r.val : Word w) := by
  induction es generalizing base m j with
  | nil => simp at hj
  | cons e es ih =>
    cases j with
    | zero =>
      have low : ∀ p∈columns n (base+n) es, base+r.val<p.out := fun p hp =>
        (Nat.add_lt_add_left r.isLt base).trans_le (columns_below es p hp)
      simp only [columns,result,Nat.zero_mul,Nat.add_zero,List.getElem_cons_zero]
      rw [result_below _ _ _ low]
      have inside : base≤base+r.val ∧ base+r.val<base+n := ⟨by omega,by omega⟩
      simp only [Pass.apply,image,fillSegment,ite_eq_left inside,Nat.cast_add]
      congr 1
      abel
    | succ j =>
      have jr : j<es.length := by simpa using hj
      have loc : base+(j+1)*n+r.val=(base+n)+j*n+r.val := by ring
      rw [loc]
      simp only [columns,result,List.getElem_cons_succ]
      let after := (show Pass from ⟨base,n,e⟩).apply m
      change result (columns n (base+n) es) after _ = _
      rw [ih (m:=after) (before.trans (Nat.le_add_right _ _)) (fun v hv => reader v (.tail _ hv)) j jr]
      apply eval_below _ _ _ _ (reader _ (.tail _ (List.getElem_mem ..)))
      intro a ha
      simp [after,Pass.apply,image,fillSegment,not_le.mpr (ha.trans_le before)]

/-- The native pass writes only its own contiguous output area. This
preserves both earlier live rows and the immutable directories assigned
to later levels on the same original tape. -/
theorem columns_frame {w n base address : ℕ} (es : List Expr) (m : Memory w)
    (outside : address<base ∨ base+es.length*n≤address) :
    result (columns n base es) m address=m address := by
  induction es generalizing base m with
  | nil => rfl
  | cons e es ih =>
    simp only [List.length_cons,Nat.succ_mul] at outside
    let head : Pass := ⟨base,n,e⟩
    change result (columns n (base+n) es) (head.apply m) address=m address
    rw [ih (base:=base+n) (head.apply m) (by rcases outside with low|high;exact Or.inl (by omega);exact Or.inr (by omega))]
    have skip : ¬(base≤address ∧ address<base+n) := by rcases outside with low|high <;> omega
    simp [head,Pass.apply,image,fillSegment,skip]

end Hierarchy.ProbeStage.Native

end OAI
