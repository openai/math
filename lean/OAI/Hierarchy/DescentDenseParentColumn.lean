import OAI.Hierarchy.DescentSparseHubBits

namespace OAI
/-! # Native compaction of a natural-valued public column along occupied rows -/
namespace Hierarchy.DescentHubBits
open DescentCensusRAM DescentIssuedTerminalId ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical BigOperators Fin.CommRing
noncomputable section
variable {V : Type} [Fintype V] {n H w : ℕ}
variable (sparse : V↪Fin n) (rank : V↪Fin H)

omit [Fintype V] in
theorem emit_values (banks : Banks w n (H+1)) (flags ids codes : Bank) (tag : Fin n→ℕ)
    (m : Memory w) (ff : flags.Fits w banks.first) (ifit : ids.Fits w banks.first)
    (cf : codes.Fits w banks.first) (nr : n ≤ flags.size) (ir : n ≤ ids.size) (cr : n ≤ codes.size)
    (live : ∀i : Fin n,m (flags.base+i.val)=(if active sparse i then 1 else 0))
    (idRead : ∀v,m (ids.base+(sparse v).val)=((rank v).val:Word w))
    (shape : ∀i : Fin n,m (codes.base+i.val)=(tag i:Word w)) :
    let key:=destination banks.bins H flags ids
    let val:=Expr.lookup codes .row
    ∃out : Memory w,(tally banks key val).Exec m out (tallyCost banks key val) ∧
      (∀v,out (banks.bins+(rank v).val)=(tag (sparse v):Word w)) ∧
      (∀a : Fin H,(¬∃v,rank v=a)→ out (banks.bins+a.val)=0) ∧ ∀a < banks.first,out a=m a := by
  let key:=destination banks.bins H flags ids
  let val:=Expr.lookup codes .row
  have one : 1<2^w:=lt_of_le_of_lt ff.1 ff.2.1
  have nonzero : (1:Word w)≠0 := by
    intro eq
    have v:=congrArg Fin.val eq
    simp [Nat.mod_eq_of_lt one] at v
  have digit (i : Fin n) : key.eval m (i.val:Word w)=((banks.bins+(target sparse rank i).val:ℕ):Word w) := by
    have seen : flags.read m (i.val:Word w)=(if active sparse i then 1 else 0) :=
      (lookup_nat flags m _ .row i.val rfl (i.isLt.trans_le nr) ff.2.1).trans (live i)
    change (banks.bins : Word w) + (if (flags.read m (i.val:Word w) == 0) then (H:Word w)
      else ids.read m (i.val:Word w)) = _
    by_cases h : active sparse i
    · have found : ids.read m (i.val:Word w)=((rank h.choose).val:Word w) :=
        (lookup_nat ids m _ .row i.val rfl (i.isLt.trans_le ir) ifit.2.1).trans
          ((congrArg (fun r : Fin n => m (ids.base+r.val)) h.choose_spec).symm.trans (idRead h.choose))
      rw [seen,ite_eq_left h,beq_eq_false_iff_ne.mpr nonzero]
      simp only [Bool.false_eq_true,ite_false,found,target,dite_eq_left h,Fin.val_castSucc,Nat.cast_add]
    · rw [seen,ite_eq_right h]
      simp only [beq_self_eq_true,ite_true,target,dite_eq_right h,Fin.val_last,Nat.cast_add]
  obtain ⟨out,exec,read,keep⟩:=tally_exec banks key val (target sparse rank) (fun i=>tag i) m
    ⟨trivial,⟨ff,trivial⟩,trivial,trivial,ifit,trivial⟩ ⟨cf,trivial⟩ digit
    (fun i=>(lookup_nat codes m (i.val:Word w) .row i.val rfl (i.isLt.trans_le cr) cf.2.1).trans (shape i))
  refine ⟨out,exec,?_,?_,keep⟩
  · intro v
    simpa [sumAt,target_at] using read (rank v).castSucc
  · intro a none
    have different (j : Fin n) : target sparse rank j≠a.castSucc := by
      by_cases h : active sparse j
      · simpa [target,h] using (show rank h.choose≠a from fun eqn=>none ⟨_,eqn⟩)
      · intro he
        rw [target,dite_eq_right h] at he
        exact (Nat.ne_of_lt a.isLt) (congrArg Fin.val he).symm
    simpa [sumAt,different] using read a.castSucc


end
end Hierarchy.DescentHubBits

end OAI
