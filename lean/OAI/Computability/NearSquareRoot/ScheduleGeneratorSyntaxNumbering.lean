import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntax
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxAddress

/-! # Program-dependent pointer and register numbers for the P192 compiler -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax
open IntegerMultiplication CommonAlphabet Generator.SyntaxAddress

variable {A : Type} [Fintype A] (letter : A ↪ ℕ)

noncomputable def ptrNumbering (U : List (Prog.Loc A)) : Numbering (Prog.Ptr U) :=
  numbering ⟨site letter, site_injective letter⟩ U

def idxNumbering (U : List (Prog.Loc A)) : Numbering (Prog.Idx U) :=
  numbering (Function.Embedding.refl ℕ) (Prog.used U)

/-- Register operand of a push, pop or look; all other instructions contribute zero. -/
def touchedKey (k : ℕ) : ℕ :=
  let fields := (Encodable.decode (α := List ℕ) k).getD []
  let tag := fields.getD 0 0
  if 1 ≤ tag ∧ tag ≤ 3 then fields.getD 1 0 else 0

theorem primrec_touchedKey : Primrec touchedKey := by
  have fields : Primrec (fun k : ℕ => (Encodable.decode (α := List ℕ) k).getD []) :=
    Primrec.option_getD.comp Primrec.decode (Primrec.const [])
  have tag := (Primrec.list_getD 0).comp fields (Primrec.const 0)
  exact Primrec.ite ((Primrec.nat_le.comp (Primrec.const 1) tag).and
    (Primrec.nat_le.comp tag (Primrec.const 3)))
    ((Primrec.list_getD 0).comp fields (Primrec.const 1)) (Primrec.const 0)

theorem touchedKey_key (p : Prog A) : touchedKey (key letter p) = Prog.touched p := by
  cases p <;> simp [key, touchedKey, Prog.touched]

def registerNames (sites : List Site) : List ℕ := 0 :: sites.map (fun u => touchedKey u.2)

theorem primrec_registerNames : Primrec registerNames :=
  Primrec.list_cons.comp (Primrec.const 0)
    (Primrec.list_map Primrec.id (primrec_touchedKey.comp (Primrec.snd.comp Primrec.snd)).to₂)

theorem registerNames_sites (U : List (Prog.Loc A)) :
    registerNames (U.map (site letter)) = Prog.used U := by
  simp [registerNames, Prog.used, site, Function.comp_def, touchedKey_key]

@[simp] theorem ptr_size (U : List (Prog.Loc A)) :
    (ptrNumbering letter U).size = size (U.map (site letter)) := rfl

@[simp] theorem ptr_rank (U : List (Prog.Loc A)) (p : Prog.Ptr U) :
    ((ptrNumbering letter U).equiv p).val = rank (U.map (site letter)) (site letter p.val) := rfl

theorem ptr_read (U : List (Prog.Loc A)) (i : Fin (ptrNumbering letter U).size) :
    read (U.map (site letter)) i.val =
      some (site letter (((ptrNumbering letter U).equiv.symm i).val)) :=
  numbering_read ⟨site letter, site_injective letter⟩ U i

omit [Fintype A] in
@[simp] theorem idx_size (U : List (Prog.Loc A)) :
    (idxNumbering U).size = size (Prog.used U) := by
  change size ((Prog.used U).map id) = _
  simp

omit [Fintype A] in
@[simp] theorem idx_rank (U : List (Prog.Loc A)) (p : Prog.Idx U) :
    ((idxNumbering U).equiv p).val = rank (Prog.used U) p.val := by
  change rank ((Prog.used U).map id) p.val = _
  simp

omit [Fintype A] in
theorem idx_read (U : List (Prog.Loc A)) (i : Fin (idxNumbering U).size) :
    read (Prog.used U) i.val = some (((idxNumbering U).equiv.symm i).val) := by
  have h := numbering_read (Function.Embedding.refl ℕ) (Prog.used U) i
  change read ((Prog.used U).map id) i.val = some (((idxNumbering U).equiv.symm i).val) at h
  simpa only [List.map_id] using h

namespace Effective

variable {X : Type} [Primcodable X] {p : X → Prog A} {letter}

theorem ptrSize (hp : Effective letter p) :
    Computable fun x => (ptrNumbering letter (Prog.sites [] (p x))).size :=
  primrec_size.to_comp.comp (Computable.snd.comp hp)

theorem used (hp : Effective letter p) : Computable fun x => Prog.used (Prog.sites [] (p x)) :=
  (primrec_registerNames.to_comp.comp (Computable.snd.comp hp)).of_eq
    (fun _ => registerNames_sites letter _)

theorem idxSize (hp : Effective letter p) :
    Computable fun x => (idxNumbering (Prog.sites [] (p x))).size :=
  (primrec_size.to_comp.comp hp.used).of_eq (fun _ => (idx_size _).symm)

end Effective
end GeneratorSyntax

end NearSquareRoot
end Computability
end OAI
