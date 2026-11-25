import OAI.ThreeFlat.RAM.SelectedPadHeader

namespace OAI
/-! # Exact physical dimensions of the four-word terminal header writer -/

namespace ThreeFlat.RAM.SelectedPadHeader
open Computability.VPVNP.BurstRAM PrivateRAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing
open private col term from OAI.ThreeFlat.RAM.SelectedPadHeader

private theorem chooser {w : ℕ} (x y yes no : Term w 0 1) :
    (Term.select .eq x y yes no).binds = x.binds+y.binds+yes.binds+no.binds+1 := by
  simp [Term.select,Term.binds_letThen,Term.binds_rename,Term.binds,Nat.add_assoc]

private theorem writer_registers {w : ℕ} (f : ℕ → Term w 0 1) (base : Word w)
    (c₀ : (f 0).binds=6) (c₁ : (f 1).binds=4) (c₂ : (f 2).binds=4) (c₃ : (f 3).binds=1) :
    4 + ((LiteralTable.dispatch (0:Fin 1) f 4).instantiate
      (fun _ => Term.binary .sub (.result 0) (.literal base) : Fin 1 → Term w 0 1)).binds=30 := by
  rw [Term.binds_instantiate,Fin.sum_univ_one]
  simp only [LiteralTable.dispatch,chooser,Term.binary,Term.binds_letThen,Term.binds_rename,
    Term.binds,Term.literal,c₀,c₁,c₂,c₃]

private theorem writer_labels {w : ℕ} (e : Term w 0 1) (base : ℕ)
    (r : (PhysicalInputPhases.writing e Fin.elim0 base 4).registers=30) :
    (PhysicalInputPhases.writing e Fin.elim0 base 4).labels=85 := by
  change 4+e.binds=30 at r
  change 6+e.labels=85
  rw [Term.labels_eq]
  omega

theorem dimensions (w control header metaBase pins hidden tag : ℕ) :
    let p:=program w control header metaBase pins hidden tag
    p.labels=85 ∧ p.registers=30 ∧ p.slots=0 := by
  let f := col (w:=w) control metaBase pins hidden tag
  let e := term (w:=w) control header metaBase pins hidden tag
  have c₀ : (f 0).binds=6 := by
    simp only [f,col,Term.binary,Term.load,Term.literal,Term.binds_letThen,Term.binds_rename,Term.binds]
  have c₁ : (f 1).binds=4 := by
    simp only [f,col,Term.binary,Term.load,Term.literal,Term.binds_letThen,Term.binds_rename,Term.binds]
  have c₂ : (f 2).binds=4 := by
    simp only [f,col,Term.binary,Term.load,Term.literal,Term.binds_letThen,Term.binds_rename,Term.binds]
  have c₃ : (f 3).binds=1 := by simp only [f,col,Term.literal,Term.binds]
  have registers : (PhysicalInputPhases.writing e Fin.elim0 header 4).registers=30 :=
    writer_registers f (header:Word w) c₀ c₁ c₂ c₃
  exact ⟨writer_labels e header registers,registers,rfl⟩

end ThreeFlat.RAM.SelectedPadHeader

end OAI
