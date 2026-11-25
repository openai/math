import OAI.Computability.BorderVNP.PackedInheritedExtent

/-! # Shared permanent work and extent columns

One shared work circuit and one virtual endpoint scan feed all row additions.
Their old-work outputs are retained directly alongside the computed extent.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.Inherited.WorkWords

open Crossing CellAddressCircuit ParseBatchSort VPVNP.VerifierNetwork Word
open private operands from OAI.Computability.BorderVNP.PackedInheritedExtent
open scoped Classical

variable {s m n C d k w : ℕ} {σ : Type*} [Fintype σ]
variable (F : Fields s m n C d k w σ) (work : Frame σ (Fin s × Fin w))

/-- The current generation stores the work prefix and full extent in each
named site row. The work gates and incidence scan are run only once. -/
theorem exists_directory :
    ∃ f : Frame σ (Fin s × Bool × Fin w),
      f.size ≤ work.size + (Views.frame F).size + 1 + s*3*(100*(w+1)^2) ∧
      (∀ x i j, f.eval x (i,false,j) = work.eval x (i,j)) ∧
      ∀ x i, let a := value (fun j => work.eval x (i,j))
        let b := value (fun j => (Views.frame F).eval x (.inr (.inr (2,i)),j))
        a+b < 2^w → value (fun j => f.eval x (i,true,j)) = a+b := by
  let args := operands F work
  let expr : WidthExpr Bool := .binary .add (.field false) (.field true)
  obtain ⟨add,hs,hf⟩ := exists_words (Frame.initial (id : Fin s × Bool × Fin w → _)) id (fun _ => expr)
  let pick (z : Fin s × Bool × Fin w) : (Fin s × Bool × Fin w) ⊕ (Fin s × Fin w) :=
    if z.2.1 then .inr (z.1,z.2.2) else .inl z
  let f := (add.withInput.select pick).subst args
  have cost : add.size ≤ 1+s*3*(100*(w+1)^2) := by simpa [expr,WidthExpr.nodes] using hs
  refine ⟨f,?_,?_,?_⟩
  · simp only [f,args,operands,Frame.subst_size,Frame.select_size,Frame.withInput_size,parallelFrame_size]
    omega
  · intro x i j
    simp [f,pick,args,operands]
  · intro x i a b fit
    let env (t : Bool) := value (fun j => args.eval x (i,t,j))
    have ha : env false = a := by simp [env,args,a,operands]
    have hb : env true = b := by simp [env,args,b,operands]
    have he : expr.eval env = a+b := by simp [expr,WidthExpr.eval,Op.apply,ha,hb]
    have h := hf (args.eval x) i
    simp only [Frame.initial_eval,id_eq] at h
    have hg : expr.Fits w env := ⟨value_lt _,value_lt _,he.trans_lt fit⟩
    simpa only [f,pick,Frame.subst_eval,Frame.select_eval,ite_true,Frame.withInput_eval_inr] using (h hg).trans he

/-- Read the two stored fields as separate gate outputs without recompiling them. -/
noncomputable def column (f : Frame σ (Fin s × Bool × Fin w)) (extent : Bool) : Frame σ (Fin s × Fin w) :=
  f.select fun z => (z.1,extent,z.2)

variable {D : ℕ} {P : Type*} [Fintype P] {bits : P → ℕ} (N : Network D P bits)
variable (siteID : N.Site ↪ Fin s) (edgeID : N.Edge ↪ Fin m) (portID : P ↪ Fin n)

/-- Live and vacant words of both columns agree with the actual sparse site
program and physical endpoints. -/
theorem directory_covers {x : σ → Bool} (rep : Views.EndpointData N F siteID edgeID portID x)
    (state : N.Site → Site) (hin : ∀ v, (state v).incoming = incoming N v)
    (old : Covers siteID (fun v => (state v).work) work x) (room : ∀ v, (state v).size < 2^w)
    (f : Frame σ (Fin s × Bool × Fin w)) (hw : ∀ i j, f.eval x (i,false,j) = work.eval x (i,j))
    (he : ∀ i, let a := value (fun j => work.eval x (i,j))
      let b := value (fun j => (Views.frame F).eval x (.inr (.inr (2,i)),j))
      a+b < 2^w → value (fun j => f.eval x (i,true,j)) = a+b) :
    Covers siteID (fun v => (state v).work) (column f false) x ∧
      Covers siteID (fun v => (state v).size) (column f true) x := by
  constructor
  · constructor
    · intro v; simpa only [column,Frame.select_eval,hw] using old.live v
    · intro i hi; simpa only [column,Frame.select_eval,hw] using old.hole i hi
  · exact extent_covers N F siteID edgeID portID work rep state hin old room (column f true)
      (by simpa only [column,Frame.select_eval] using he)

end Packing.Inherited.WorkWords

end BorderVNP
end Computability
end OAI
