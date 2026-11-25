import OAI.Hierarchy.DescentCorrelationRAM
import OAI.Hierarchy.DescentMixingIntegerWeights

namespace OAI
/-! # Publishing a chosen depth's true integer estimator coefficients -/

namespace Hierarchy.DescentWeightColumnRAM
open DescentGL DescentGLScoreRAM DescentCorrelationRAM DescentIntegerScale ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped BigOperators Fin.CommRing Classical
noncomputable section

/-- In a position there is one measured difference vector for each load stream.
The other two cells hold the depth and integer factor of the same occurrence. -/
structure Row where
  correlation : ℕ
  depth : ℕ
  factor : ℕ

def singleton (ptr : ℕ) : Expr := .lookup ⟨ptr,0⟩ (.lit 0)

def selected (k depth : ℕ) (row : Row) : Expr :=
  .branch .eq (singleton row.depth) (.lit depth) (.lookup ⟨row.correlation,k⟩ .row) (.lit 0)

def word (k w out depth precision : ℕ) (row : Row) : Term w 0 1 :=
  mulTerm precision ((selected k depth row).compile w out) ((singleton row.factor).compile w out)

def vector (k w out depth precision : ℕ) {N : ℕ} (rows : Fin N→Row) : Term w 0 1 :=
  addTerms N (fun i=>word k w out depth precision (rows i))

def pass (k w out depth precision : ℕ) {N : ℕ} (rows : Fin N→Row) : Procedure w :=
  PhysicalInputPhases.writing (vector k w out depth precision rows) Fin.elim0 out (2^k)

structure Fits (w out k : ℕ) (row : Row) : Prop where
  table : (Bank.mk row.correlation k).Fits w out
  depth : row.depth<out
  factor : row.factor<out

def money {k N : ℕ} (depth : ℕ) (atLevel gain : Fin N→ℕ) (corr : Fin N→DescentGL.Bits k→ℕ)
    (d : DescentGL.Bits k) : ℕ := ∑i,if atLevel i=depth then gain i*corr i d else 0

def after {w k N : ℕ} (m : Memory w) (out depth : ℕ) (atLevel gain : Fin N→ℕ)
    (corr : Fin N→DescentGL.Bits k→ℕ) : Memory w :=
  fillSegment out (2^k) (fun a=>(money depth atLevel gain corr
    (vec ⟨(a-out)%2^k,Nat.mod_lt _ (Nat.two_pow_pos _)⟩):Word w)) m

theorem run {w k N out depth precision : ℕ} (m : Memory w) (rows : Fin N→Row)
    (atLevel gain : Fin N→ℕ) (corr : Fin N→DescentGL.Bits k→ℕ)
    (room : out+2^k<2^w) (levels : depth<2^w) (measure : precision≤w)
    (fit : ∀i,Fits w out k (rows i)) (bounded : ∀i,atLevel i<2^w ∧ gain i<2^precision)
    (headers : ∀i,m (rows i).depth=(atLevel i:Word w) ∧ m (rows i).factor=(gain i:Word w))
    (tables : ∀i (j : Fin (2^k)),m ((rows i).correlation+j.val)=(corr i (vec j):Word w)) :
    (pass k w out depth precision rows).Exec m (after m out depth atLevel gain corr)
      (4+2^k*(2*(vector k w out depth precision rows).binds+4)) := by
  let field := fun a : ℕ=>(money depth atLevel gain corr
    (vec ⟨(a-out)%2^k,Nat.mod_lt _ (Nat.two_pow_pos _)⟩):Word w)
  have spec : (pass k w out depth precision rows).Spec (·=m)
      (fun src dst=>dst=fillSegment out (2^k) field src)
      (4+2^k*(2*(vector k w out depth precision rows).binds+4)) :=
    PhysicalInputPhases.writing_spec (vector k w out depth precision rows) Fin.elim0 out (2^k) room (·=m) field (by
      intro first eq addr now lo stop same
      subst first
      let j : Fin (2^k) := ⟨addr.val-out,by omega⟩
      have index : addr-(out:Word w)=(j.val:Word w) := by simp [j,Nat.cast_sub lo]
      have pos : 1<2^w := by have := Nat.two_pow_pos k;omega
      have singletonFits {s : ℕ} (low : s<out) : (singleton s).Fits w out :=
        ⟨⟨Nat.zero_lt_one,pos,show s+1≤out from low⟩,trivial⟩
      have readSingleton {s : ℕ} (low : s<out) :
          (singleton s).eval now (j.val:Word w)=m s := by
        simpa [singleton,Expr.eval,Bank.read,Bank.size] using same s (.inl low)
      have fixed {s : ℕ} (low : s<out) :
          ((singleton s).compile w out).eval Fin.elim0 now (fun _=>addr)=m s := by
        rw [eval_compile (singleton s) now addr (singletonFits low) (by omega),index]
        exact readSingleton low
      have termVal (i : Fin N) : (word k w out depth precision (rows i)).eval Fin.elim0 now (fun _=>addr)=
          ((if atLevel i=depth then gain i*corr i (vec j) else 0:ℕ):Word w) := by
        have chosen : ((selected k depth (rows i)).compile w out).eval Fin.elim0 now (fun _=>addr)=
            if atLevel i=depth then (corr i (vec j):Word w) else 0 := by
          have safe : (selected k depth (rows i)).Fits w out :=
            ⟨singletonFits (fit i).depth,trivial,⟨(fit i).table,trivial⟩,trivial⟩
          rw [eval_compile (selected k depth (rows i)) now addr safe (by omega),index]
          change (if Comparison.eq.test ((singleton (rows i).depth).eval now (j.val:Word w)) (depth:Word w)
            then (Bank.mk (rows i).correlation k).read now (j.val:Word w) else (0:Word w))=_
          rw [readSingleton (fit i).depth,(headers i).1]
          have tag : ((atLevel i:ℕ):Word w)=(depth:Word w) ↔ atLevel i=depth := by
            rw [Fin.ext_iff,Fin.val_cast_of_lt (bounded i).1,Fin.val_cast_of_lt levels]
          simp only [Comparison.test,beq_iff_eq,tag]
          by_cases active : atLevel i=depth
          · simp only [ite_eq_left active]
            have cellFit : j.val<2^w := j.isLt.trans (fit i).table.2.1
            have bankEnd : (rows i).correlation+2^k≤out := (fit i).table.2.2
            have early : (rows i).correlation+j.val<out :=
              (Nat.add_lt_add_left j.isLt _).trans_le bankEnd
            simpa only [Bank.read,Bank.size,Fin.val_cast_of_lt cellFit,Nat.mod_eq_of_lt j.isLt] using
              (same _ (.inl early)).trans (tables i j)
          · simp only [ite_eq_right active]
        have fact := (fixed (fit i).factor).trans (headers i).2
        have noWrap : gain i<2^w := (bounded i).2.trans_le (Nat.pow_le_pow_right (by decide) measure)
        have carry : (((singleton (rows i).factor).compile w out).eval Fin.elim0 now (fun _=>addr)).val<2^precision := by
          rw [fact,Fin.val_cast_of_lt noWrap]
          exact (bounded i).2
        rw [word,mulTerm_eval _ _ _ measure _ _ carry,chosen,fact]
        by_cases active : atLevel i=depth <;> simp [active,Nat.cast_mul,mul_comm]
      rw [vector,addTerms_eval]
      have offset : addr.val-out<2^k := j.isLt
      simpa only [field,money,Nat.mod_eq_of_lt offset,Nat.cast_sum,j] using
        Finset.sum_congr (s₂:=Finset.univ) rfl (fun i _=>termVal i))
  intro P R K M pc reg pub exit installed data cfg start entry eq
  subst start
  exact spec M pc reg pub exit installed data cfg m entry rfl

/-- The stages' measured integer rows are the actual two lists of terms in
the joint estimator, including their distinct level and overflow factors. -/
theorem mixing {A C : Type} [Fintype A] [Fintype C] {k : ℕ}
    (levels : A→ℕ) (j : (a:A)→Fin (levels a)→ℕ) (cj : C→ℕ)
    (x : A→DescentGL.Bits k→ℕ) (y : C→DescentGL.Bits k→ℕ) (a B K : ℕ)
    (level : Fin (k+1)) (d : DescentGL.Bits k) :
    let U := (Σ z,Fin (levels z)) ⊕ C
    let id := (Fintype.equivFin U).symm
    money level.val (fun i=>Sum.elim (fun z=>j z.1 z.2) cj (id i))
      (fun i=>(2^a*B)*Sum.elim (fun z=>4*2^((z.2.val+7)/8)) (fun _=>K^2) (id i))
      (fun i=>Sum.elim (fun z=>natCorrelation (x z.1)) (fun c=>natCorrelation (y c)) (id i)) d =
      mixingWeightNumerator levels j cj x y a B K level d := by
  classical
  let S := Σ z : A, Fin (levels z)
  let U := S ⊕ C
  let f (p : U) : ℕ := if Sum.elim (fun z : S=>j z.1 z.2) cj p=level.val then
      (2^a*B)*Sum.elim (fun z : S=>4*2^((z.2.val+7)/8)) (fun _=>K^2) p *
        (Sum.elim (fun z : S=>natCorrelation (x z.1)) (fun c=>natCorrelation (y c)) p) d
    else 0
  change (∑ i, f ((Fintype.equivFin U).symm i)) = _
  rw [(Fintype.equivFin U).symm.sum_comp f,Fintype.sum_sum_type,Fintype.sum_sigma]
  simp only [f,Sum.elim_inl,Sum.elim_inr,mixingWeightNumerator,Nat.mul_add,Finset.mul_sum]
  apply congrArg₂ (fun l r : ℕ=>l+r)
  · apply Finset.sum_congr rfl
    intro z _
    apply Finset.sum_congr rfl
    intro t _
    by_cases hit : j z t=level.val
    · simp only [ite_eq_left hit,ite_eq_left hit.symm,Nat.mul_assoc]
    · simp only [ite_eq_right (Ne.symm hit),Nat.mul_zero]; exact ite_eq_right hit
  · apply Finset.sum_congr rfl
    intro c _
    by_cases hit : cj c=level.val
    · simp only [ite_eq_left hit,ite_eq_left hit.symm,Nat.mul_assoc]
    · simp only [ite_eq_right (Ne.symm hit),Nat.mul_zero]; exact ite_eq_right hit

end
end Hierarchy.DescentWeightColumnRAM

end OAI
