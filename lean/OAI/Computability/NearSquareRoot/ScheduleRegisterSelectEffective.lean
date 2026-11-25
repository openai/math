import OAI.Computability.NearSquareRoot.KernelEffectiveFamily
import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxFold
import OAI.Computability.IntegerMultiplication.Code.Slice

/-! # Effective compilation of tagged scalar actions

The dispatch consumes the unary tag on register zero. Each table entry
contributes a pair of inspections to the finite control, and an out-of-range
tag selects the supplied default action.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace EffectiveSelect
open IntegerMultiplication Code CommonRegisters GeneratorSyntax KernelEffectiveFamily
open RegisterWitness (splitRoot_within)

private def split (atom node : Cmd) := splitRoot 0 (fun _ => atom) node

private noncomputable def splitFile (atom node : File) : File :=
  lookFile 0 (Prog.options.map fun top : Option Ltr => joinFile (file ltr (.pop 0))
    (match top with
    | some (.bit _) => atom
    | some .node => node
    | _ => file ltr .pass))

private theorem split_file (atom node : Cmd) :
    splitFile (file ltr atom) (file ltr node) = file ltr (split atom node) := by
  unfold split splitRoot splitFile
  rw [← lookFile_file]
  apply congrArg (lookFile 0)
  apply List.map_congr_left
  rintro (_|(_|_|_)) _ <;> exact joinFile_file ..

private theorem split_computable : Computable₂ splitFile := by
  apply primrec_lookFile.to_comp.comp (Computable.const 0)
  apply computable_options_map
  intro top _
  rcases top with _|(_|_|_)
  all_goals apply primrec_joinFile.to_comp.comp (Computable.const _)
  all_goals first | exact Computable.fst | exact Computable.snd | exact Computable.const _

private def chooseCmd {P : Type} (action : P → Cmd) (default : P) : List P → Cmd
  | [] => .join (discard 0) (action default)
  | p::ps => split (action p) (split (chooseCmd action default ps) .pass)

private theorem choose_effective {P : Type} [Primcodable P] (action : P → Cmd) (default : P)
    (h : Effective ltr action) : Effective ltr (chooseCmd action default) := by
  let z := file ltr ((discard 0).join (action default))
  let step (p : P) (r : File) := splitFile (file ltr (action p)) (splitFile r (file ltr .pass))
  have hc : Computable (fun ps : List P => ps.foldr step z) := by
    apply computable_foldr (l := id) (f := fun _ v => step v.1 v.2) Computable.id (Computable.const _)
    exact split_computable.comp (h.comp (Computable.fst.comp Computable.snd))
      (split_computable.comp (Computable.snd.comp Computable.snd) (Computable.const _))
  apply hc.of_eq
  intro ps
  induction ps with
  | nil => rfl
  | cons p ps ih => simp only [List.foldr_cons,step,chooseCmd,ih,split_file]

private theorem choose_within {P : Type} {R : ℕ} (hR : 0 < R) (action : P → Cmd) (default : P)
    (h : ∀ p, Within R (action p)) (ps : List P) : Within R (chooseCmd action default ps) := by
  induction ps with
  | nil =>
    exact ⟨by simp [Code.discard,Code.forward,Code.forwardBody,Code.flood,Within,hR],h default⟩
  | cons p ps ih =>
    exact splitRoot_within.mpr ⟨hR,h _,h _,splitRoot_within.mpr ⟨hR,ih,ih,trivial⟩⟩

private theorem choose_fits {P X Y : Type} [Codec X] [Codec Y] (action : P → Cmd)
    (f : P → X → Y) (default : P) (h : ∀ p, Runs (action p) (f p)) (ps : List P) :
    ∃ C : ℕ, ∀ (tag : Tally) (x : X) env r,
      Fits env (chooseCmd action default ps) (pile 0 (send tag) (pile 0 (send x) r))
        (pile 0 (send (f (ps.getD tag.length default) x)) r) (C*(size tag+size x+1)) := by
  induction ps with
  | nil =>
    obtain ⟨C,hc⟩ := h default
    refine ⟨C+20,fun tag x env r => ?_⟩
    have drop := fits_discard 0 (send tag) env (pile 0 (send x) r)
    have b := (drop.join (hc x env r))
    have m := Nat.mul_le_mul_left C (by omega : size x+1 ≤ size tag+size x+1)
    change Fits _ _ _ (pile 0 (send (f default x)) r) _
    apply b.mono
    change 17*size tag+C*(size x+1)+2 ≤ _
    rw [Nat.add_mul]
    omega
  | cons p ps ih =>
    obtain ⟨C,hp⟩ := h p
    obtain ⟨D,hd⟩ := ih
    refine ⟨C+D+8,fun tag x env r => ?_⟩
    cases tag with
    | nil =>
      apply (fits_bit (c := fun _ => action p) (b := false) (hp x env r)).mono
      simp only [size_nil,Nat.add_mul]
      have := Nat.mul_le_mul_left C (by omega : size x+1 ≤ 1+size x+1)
      omega
    | cons u tag =>
      cases u
      apply (fits_pair (fits_bit (b := false) (c := fun _ => chooseCmd action default ps)
        (hd tag x env r))).mono
      simp only [size_tally,List.length_cons,Nat.add_mul]
      have := Nat.mul_le_mul_left D (by omega : 2*tag.length+1+size x+1 ≤ 2*(tag.length+1)+1+size x+1)
      omega

/-- Turn one effective scalar action into a whole finite table indexed by a
unary tag. Table length and contents affect only the generated code and clock. -/
theorem table {P X Y : Type} [Primcodable P] [Codec X] [Codec Y] {R : ℕ} (hR : 0 < R)
    {f : P → X → Y} (default : P) (h : Family R f) :
    Family R (fun ps : List P => fun s : Tally × X => f (ps.getD s.1.length default) s.2) := by
  obtain ⟨action,eff,sound⟩ := h
  let c := chooseCmd action default
  refine ⟨fun ps => split .pass (c ps),?_,fun ps => ⟨?_,?_⟩⟩
  · apply (split_computable.comp (Computable.const (file ltr .pass)) (choose_effective action default eff)).of_eq
    exact fun _ => split_file ..
  · exact splitRoot_within.mpr ⟨hR,trivial,trivial,choose_within hR action default (fun p => (sound p).1) ps⟩
  · obtain ⟨C,hc⟩ := choose_fits action f default (fun p => (sound p).2) ps
    refine ⟨C+4,fun ⟨tag,x⟩ env r => (fits_pair (hc tag x env r)).mono ?_⟩
    simp only [size_prod,Nat.add_mul]
    have := Nat.mul_le_mul_left C (by omega : size tag+size x+1 ≤ size tag+size x+1+1)
    omega

end EffectiveSelect

end NearSquareRoot
end Computability
end OAI
