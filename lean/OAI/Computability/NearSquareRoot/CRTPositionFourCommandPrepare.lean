import OAI.Computability.NearSquareRoot.CRTPositionFourCommand

/-! # Preparing the twelve keys of the four-stage position command

A single bounded command accepts the unary reserve widths and permutation
table next to an arbitrary data tree. It leaves the stage headers nested in
the order in which the four framed commands consume them.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionCmd

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
open NearSquareRoot.Space NearSquareRoot.CommonRegisters NearSquareRoot.GeneratorSyntax
open Reflections (Table table)

noncomputable section

/-- The ghost inputs for one fixed preparation command. All geometry and all
payload trees satisfying the common external volume bound belong to its domain. -/
structure PreCase where
  k : ℕ
  lo : ℕ
  hi : ℕ
  perm : Equiv.Perm (Fin k)
  cap : lo+hi ≤ k/2-2
  V : ℕ
  array : 2^k ≤ V
  data : Tree
  fits : data.count ≤ V

def PreCase.stage (x : PreCase) (j : Fin 4) : ReserveStage x.k x.lo x.hi :=
  ReserveProgram.atStage x.perm x.cap j

def PreCase.source (x : PreCase) : Tree := send (tally x.lo,tally x.hi,table x.perm)

def PreCase.input (x : PreCase) : Tree := .fork x.source x.data

def PreCase.output (x : PreCase) : Tree :=
  fullShell x.stage x.data

private def prepareRegime : Regime PreCase where
  scale := PreCase.k
  header := PreCase.source
  gauge := by
    refine ⟨2,8,?_⟩
    intro x
    change size (tally x.lo,tally x.hi,table x.perm) ≤ _
    simp only [size_prod,size_tally,tally_length]
    have h := x.cap
    have small : x.lo+x.hi ≤ x.k := by omega
    have ht := Reflections.table_size x.perm
    nlinarith

private theorem tableWidth {I : Type} {r : Regime I} {n : I → ℕ} (p : ∀ i, Equiv.Perm (Fin (n i)))
    (h : r.Has fun i => table (p i)) : r.Has fun i => tally (n i) := by
  have v := h.ez (Easy.ruler Easy.identity)
  have eq i : ruler (table (p i)) = tally (n i) := by
    rw [← recover_tally (ruler _), ruler_length]
    simp [Reflections.table]
  simpa only [id_eq, eq] using v

attribute [local irreducible] ReserveProgram.atStage ReserveStage.four Reflections.table

private theorem preparedKeys (j : Fin 4) :
    Carries (fun x : PreCase => (x.V : ℝ)) PreCase.source (fun x => swapKey (x.stage j)) ∧
    Carries (fun x : PreCase => (x.V : ℝ)) PreCase.source (fun x => middleKey (x.stage j)) := by
  have source : prepareRegime.Has (fun x => (tally x.lo,tally x.hi,table x.perm)) := Regime.self
  have lo := source.ez Easy.fst
  have hi := (source.ez Easy.snd).ez Easy.fst
  have tab := (source.ez Easy.snd).ez Easy.snd
  have all := ReserveProgram.compiler_uniform PreCase.k PreCase.lo PreCase.hi PreCase.perm PreCase.cap lo hi tab
  have desc : prepareRegime.Has (fun x => ReserveProgram.encode (x.stage j)) :=
    ReserveProgram.atStage_uniform (r := prepareRegime) PreCase.perm PreCase.cap all j
  have inner : prepareRegime.Has (fun x => table (x.stage j).inner) := desc.ez Easy.snd
  have sk : prepareRegime.Has (fun x => flatSwapInput x.k (x.stage j).moves) :=
    (tableWidth PreCase.perm tab).pair (desc.ez Easy.fst)
  have mk := hi.pair ((tableWidth (fun x => (x.stage j).inner) inner).pair (lo.pair inner))
  have ripe := ReserveStage.ripeOfWidth (r := prepareRegime) (k := PreCase.k)
    (V := PreCase.V) (fun _ => le_rfl) PreCase.array
  exact ⟨sk.cooked ripe, mk.cooked ripe⟩

/-- A uniform constant bounds every stored header on every runtime geometry. -/
theorem keys_count : ∃ C : ℕ, ∀ (x : PreCase) (j : Fin 4),
    (send (flatSwapInput x.k (x.stage j).moves)).count ≤ C*x.V ∧
    (send (tally x.hi,tally (x.k-x.lo-x.hi),tally x.lo,table (x.stage j).inner)).count ≤ C*x.V := by
  have bound (j : Fin 4) : ∃ C : ℕ, ∀ x : PreCase,
      (swapKey (x.stage j)).count + (middleKey (x.stage j)).count + 1 ≤ C*x.V := by
    obtain ⟨C,h⟩ := ((preparedKeys j).1.twice (preparedKeys j).2).out
    refine ⟨C,fun x => ?_⟩
    have hh := h x
    change (((swapKey (x.stage j)).count + (middleKey (x.stage j)).count + 1 : ℕ) : ℝ) ≤ C * (x.V : ℝ) at hh
    exact_mod_cast hh
  choose c hc using bound
  refine ⟨∑ j, c j,fun x j => ?_⟩
  have h := (hc j x).trans (Nat.mul_le_mul_right x.V (Finset.single_le_sum
    (f := c) (fun t _ => Nat.zero_le (c t)) (Finset.mem_univ j)))
  change (swapKey (x.stage j)).count ≤ _ ∧ (middleKey (x.stage j)).count ≤ _
  omega

theorem keyBound_on {I : Type} (select : I → PreCase) (j : Fin 4) :
    KeyBound (fun t => (select t).stage j) (PreCase.V ∘ select) := by
  obtain ⟨C,h⟩ := keys_count
  refine ⟨C,fun t => ?_⟩
  have s := h (select t) j
  have widen := Nat.mul_le_mul_left C (Nat.le_succ (select t).V)
  exact ⟨s.1.trans widen, s.2.trans widen⟩

theorem prepareTask : BoundedTask PreCase.V PreCase.V PreCase.input PreCase.output := by
  let w x := ((x : PreCase).V : ℝ)
  have base := (preparedKeys 0).1
  have vol : Volume w PreCase.data :=
    ⟨1,fun x => by simpa only [Nat.cast_one,one_mul] using Nat.cast_le.mpr x.fits⟩
  have source : Carries w PreCase.input PreCase.source := Carries.dropRight base.budget base.small vol
  have data : Carries w PreCase.input PreCase.data := Carries.dropLeft base.budget base.small vol
  have stage (j : Fin 4) {p : PreCase → Tree} (h : Carries w PreCase.input p) :
      Carries w PreCase.input (fun x => shell (x.stage j) (p x)) := by
    have get := source.chain (preparedKeys j).1
    exact get.twice ((source.chain (preparedKeys j).2).twice (get.twice h))
  exact boundedOfCarries (stage 3 (stage 2 (stage 1 (stage 0 data))))

def prepareCmd : Cmd := prepareTask.choose

theorem prepare_runs : EffectiveBoundedTask.Runs prepareCmd PreCase.V PreCase.V PreCase.input PreCase.output :=
  prepareTask.choose_spec

theorem prepare_within : ∀ᶠ R : ℕ in Filter.atTop, Within R prepareCmd :=
  RegisterSelect.within_eventually _

theorem prepare_effective {J : Type} [Primcodable J] : Effective ltr (fun _ : J => prepareCmd) :=
  effective_const _ _

end
end Controlled.PositionCmd

end NearSquareRoot
end Computability
end OAI
