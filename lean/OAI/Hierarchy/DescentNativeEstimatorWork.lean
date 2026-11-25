import OAI.Hierarchy.DescentNativeColumns

namespace OAI
/-! # Physical costs of computing and aggregating the collision data -/

namespace Hierarchy.DescentNativeColumns
open DescentGL DescentGLScoreRAM DescentCorrelationRAM DescentWeightColumnRAM ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped BigOperators Fin.CommRing Classical
noncomputable section

theorem mul_binds {w n : ℕ} (prec : ℕ) (x y : Term w 0 n) :
    (mulTerm prec x y).binds≤x.binds+y.binds+(1+prec*(prec+10)) := by
  simp only [mulTerm,Term.binds_letThen,Term.binds_rename]
  have := DescentWordProduct.binds w prec
  omega

theorem mul_allowed {w n : ℕ} (prec : ℕ) (x y : Term w 0 n) (hx : admissible x) (hy : admissible y) :
    admissible (mulTerm prec x y) := by simp [mulTerm,hx,hy,DescentWordProduct.cheap]

theorem add_binds {w n : ℕ} (j U : ℕ) (f : Fin j→Term w 0 n) (small : ∀i,(f i).binds≤U) :
    (addTerms j f).binds≤1+j*(1+U) := by
  induction j with
  | zero=>simp [addTerms, Term.literal, Term.binds]
  | succ j ih=>
    have step := ih (fun i=>f i.castSucc) (fun i=>small i.castSucc)
    have last := small (Fin.last j)
    simp only [addTerms,Term.binary,Term.binds_letThen,Term.binds_rename,Term.binds,Nat.succ_mul]
    omega

theorem add_allowed {w n : ℕ} (j : ℕ) (f : Fin j→Term w 0 n) (ok : ∀i,admissible (f i)) :
    admissible (addTerms j f) := by
  induction j with
  | zero=>exact ⟨trivial,trivial⟩
  | succ j ih=>simp [addTerms,Term.binary,admissible,opAllowed,allowed,ok,ih _ (fun i=>ok i.castSucc)]

theorem correlation_cheap (w k base out p : ℕ) : CheapCode (machine w k base out p) :=
  writing_cheap _ _ _ _ (add_allowed _ _ fun _i=>mul_allowed _ _ _ (good_compile ..) (good_compile ..))

theorem weight_cheap (w k out l p : ℕ) {N : ℕ} (rows : Fin N→Row) : CheapCode (pass k w out l p rows) :=
  writing_cheap _ _ _ _ (add_allowed _ _ fun _i=>mul_allowed _ _ _ (good_compile ..) (good_compile ..))

theorem correlation_binds (w k src out p : ℕ) :
    (term w k src out p).binds≤1+2^k*(15+5*2^k+p*(p+10)) := by
  apply (add_binds (2^k) (14+5*2^k+p*(p+10)) _ ?_).trans
  · exact le_of_eq (by ring)
  · intro i
    have b := mul_binds p ((left k src i).compile w out) ((right k src i).compile w out)
    apply b.trans
    simp only [compile_binds,left,right,Expr.work,lookupRow_work]; omega

theorem weight_binds (k w out l p : ℕ) {N : ℕ} (rows : Fin N→Row) :
    (vector k w out l p rows).binds≤1+N*(24+p*(p+10)) := by
  apply (add_binds N (23+p*(p+10)) _ ?_).trans
  · exact le_of_eq (by ring)
  · intro i
    have b := mul_binds p ((selected k l (rows i)).compile w out) ((DescentWeightColumnRAM.singleton (rows i).factor).compile w out)
    unfold DescentWeightColumnRAM.word
    apply b.trans
    simp only [compile_binds,selected,DescentWeightColumnRAM.singleton,Expr.work]; omega

theorem prefix_cheap (w k base : ℕ) (cpu : ℕ→Procedure w) (N : ℕ) (ok : ∀i<N,CheapCode (cpu i)) :
    CheapCode (code w k base cpu N) := by
  induction N with
  | zero=>exact @scan_cheap _ _ _ _
  | succ j ih=>exact cheap_seq (ih (fun i hi=>ok i (by omega))) (ok _ (by omega))

theorem prefix_cost {timer : ℕ→ℕ} {N K : ℕ} (bounds : ∀i<N,timer i≤K) :
    cost timer N≤4+N*K := by
  induction N with
  | zero=>simp [cost]
  | succ j ih=>
    have before := ih (fun i hi=>bounds i (by omega))
    have now := bounds j (by omega)
    simp only [cost,Nat.succ_mul]
    omega

end
end Hierarchy.DescentNativeColumns

end OAI
