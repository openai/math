import OAI.ThreeFlat.Diagonal.SlotImage

namespace OAI
/-! # Base-vertex charts for graph images retained by a physical history -/

namespace ThreeFlat.Diagonal.SlotImage

open Computability.VPVNP.Compression
variable {B C L : Type} {d v lanes : ℕ}

def baseSlots (f : B ≃ C) : B × Fin d ≃ C × Fin d := f.prodCongr (Equiv.refl _)

def baseEdges (f : B ≃ C) : Edge B L d ≃ Edge C L d := (baseSlots f).prodCongr (Equiv.refl _)

def inBaseChart (G : LiftedSlots B d L) (f : B ≃ C) : LiftedSlots C d L where
  base := {
    target := (baseSlots f).symm.trans (G.base.target.trans (baseSlots f))
    ends_ne := by
      intro p h
      apply G.base.ends_ne ((baseSlots f).symm p)
      apply f.injective
      simpa [baseSlots] using h }
  displacement p := G.displacement ((baseSlots f).symm p)

theorem chart_target (G : LiftedSlots B d L) (f : B ≃ C) (q : B × Fin d) :
    (inBaseChart G f).base.target (baseSlots f q)=baseSlots f (G.base.target q) := by
  simp [inBaseChart]

theorem chart_reverse (G : LiftedSlots B d L) (f : B ≃ C) (q : B × Fin d) :
    (inBaseChart G f).base.target.symm (baseSlots f q)=baseSlots f (G.base.target.symm q) := by
  simp [inBaseChart]

theorem chart_fields (G : LiftedSlots B d L) (f : B ≃ C) (new : C ≃ Fin v)
    (lane : L ≃ Fin lanes) (p : B × Fin d) (b : Bool) (i : Fin 3) :
    fields (inBaseChart G f) new lane (baseSlots f p) b i=fields G (f.trans new) lane p b i := by
  have ori : oriented (inBaseChart G f) b (baseSlots f p)=baseSlots f (oriented G b p) := by
    cases b <;> first | exact chart_target G f p | exact chart_reverse G f p
  have dis : shift (inBaseChart G f) b (baseSlots f p)=shift G b p := by
    cases b <;> simp [shift,inBaseChart]
  unfold fields
  rw [ori,dis]; rfl

theorem inBaseChart_stored (G : LiftedSlots B d L) (f : B ≃ C) (base : C ≃ Fin v) (lane : L ≃ Fin lanes)
    (D : Columns) (mem : ℕ → ℕ) (w : Edge B L d → ℕ)
    (image : Stored G (f.trans base) lane D mem w) :
    Stored (inBaseChart G f) base lane D mem (w ∘ (baseEdges f).symm) where
  rowCount := image.rowCount
  graph := by
    intro p b i
    obtain ⟨q,rfl⟩ := (baseSlots f).surjective p
    rw [chart_fields]
    exact image.graph q b i
  widthWord := by
    intro p
    obtain ⟨q,rfl⟩ := (baseEdges f).surjective p
    simp only [Function.comp_apply,Equiv.symm_apply_apply]
    exact image.widthWord q


end ThreeFlat.Diagonal.SlotImage

end OAI
