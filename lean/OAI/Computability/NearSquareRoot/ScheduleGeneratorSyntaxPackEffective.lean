import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxPack
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxPackInputEffective
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxPackOutputEffective
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxTransitionEffective

/-! # Numeric transition tables for computably varying P192 programs -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack
open IntegerMultiplication CommonAlphabet Generator.StackRows

variable {X : Type} [Primcodable X]

theorem primrec_sourceRow {aSize : X → ℕ} {opts : X → List (Option ℕ)} {sites : X → List Site}
    {adr : X → ℕ × ℕ} (ha : Primrec aSize) (ho : Primrec opts) (hs : Primrec sites)
    (hi : Primrec adr) : Primrec fun x => sourceRow (aSize x) (opts x) (sites x) (adr x) :=
  primrec_output ha hs (Transition.primrec_step ho hs (primrec_heads ha hs (Primrec.snd.comp hi))
    (primrec_decodePC.comp hs (Primrec.fst.comp hi)))

variable {A : Type} [Fintype A] (a : Numbering A)

/-- Uniform counts and packed rows for the native stack compilation of structured programs. -/
theorem source_family (p : X → Prog A) (hp : Effective (letter a) p) :
    let U := fun x => Prog.sites [] (p x)
    let orig := fun x => sourceRow a.size (Transition.options (letter a)) ((U x).map (site (letter a)))
    Computable (fun x => (symbols a (U x)).size) ∧ Computable (fun x => (pcs a (U x)).size) ∧
      Computable (fun x => (Pack.stacks (U x)).size) ∧ Computable₂ orig ∧
      ∀ x, Sources (symbols a (U x)) (pcs a (U x)) (Pack.stacks (U x)) (Prog.compile (U x)) (orig x) := by
  have numeric : Primrec₂ (fun l adr => sourceRow a.size (Transition.options (letter a)) l adr) :=
    primrec_sourceRow (Primrec.const _) (Primrec.const _) Primrec.fst Primrec.snd
  have sites : Computable fun x => ((Prog.sites [] (p x)).map (site (letter a))) :=
    Computable.snd.comp hp
  exact ⟨Primrec.nat_add.to_comp.comp (Computable.const a.size) hp.ptrSize,
    Computable.succ.comp hp.ptrSize, Computable.succ.comp hp.idxSize,
    numeric.to_comp.comp (sites.comp Computable.fst) Computable.snd, fun x => sources a (Prog.sites [] (p x))⟩

/-- The exact two-phase tape program produced from each input syntax tree has
computable alphabet and control sizes and a single effective row function. -/
theorem tape_family (p : ℕ → Prog A) (hp : Effective (letter a) p) :
    let U := fun j => Prog.sites [] (p j)
    let sy := fun j => symbols a (U j)
    let qs := fun j => pcs a (U j)
    let ix := fun j => Pack.stacks (U j)
    let state := fun j => pc (sy j) (qs j) (ix j)
    let orig := fun j => sourceRow a.size (Transition.options (letter a)) ((U j).map (site (letter a)))
    let rows := fun j => row (sy j).size (qs j).size (ix j).size (orig j)
    Computable (fun j => (state j).size) ∧ Computable (fun j => (sy j).option.size) ∧
      Computable (fun j => (ix j).size) ∧ Computable₂ rows ∧ ∀ j s top,
      rows j (((state j).equiv s).val,(((ix j).arrow (sy j).option).equiv top).val) =
        (SM.toTM (Prog.compile (U j)) s top).map (fun z => (((state j).equiv z.1).val,
          (((ix j).arrow ((sy j).option.prod Numbering.move)).equiv z.2).val)) := by
  obtain ⟨hs,hq,hi,ho,h⟩ := source_family a p hp
  obtain ⟨cs,ca,cr,ok⟩ := compile_family _ _ _ _ _ hs hq hi ho h
  exact ⟨cs,ca,hi,cr,ok⟩

/-- The four source symbols of literal tree-stack commands have contiguous numbers. -/
def ltrNumbering : Numbering Code.Ltr :=
  ⟨4, { toFun := fun v => ⟨ltr v, by rcases v with (⟨_ | _⟩ | _ | _) <;> decide⟩
        invFun := ![.bit false, .bit true, .node, .sep]
        left_inv := by rintro (⟨_ | _⟩ | _ | _) <;> rfl
        right_inv := by intro i; fin_cases i <;> rfl }⟩

@[simp] theorem letter_ltr : letter ltrNumbering = ltr := rfl

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI
