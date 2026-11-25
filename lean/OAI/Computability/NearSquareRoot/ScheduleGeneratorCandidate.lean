import OAI.Computability.NearSquareRoot.ScheduleGeneratorIndexed
import OAI.Computability.NearSquareRoot.ScheduleUniversalReflect

/-! # The literal unary executor of an effective family of staged candidate programs -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorInputRun
open IntegerMultiplication TM Universal Turing.ToPartrec Turing.PartrecToTM2 ScheduleMachine
open Uniform.IndexedSlot
open scoped Classical
noncomputable section
variable {A I : Type} {M : ℕ}

/-- A candidate may have its own finite control. All candidates have the same tape
indices, physical symbols and read-vector order. -/
structure Programs (A I : Type) where
  Q : ℕ → Type
  count : ℕ → ℕ
  stateNumber : ∀ i, Q i ≃ Fin (count i)
  entry : ∀ i, Q i
  machine : ∀ i, Rule A (Q i) I
  reads : List (I → A)
  complete : ∀ r, r ∈ reads

structure Ports (A I : Type) where
  inp : I
  out : I
  blank : A
  sep : A
  bit : Bool → A
  decode : A → Option Bool
  distinct : out ≠ inp
  letters : Function.Injective bit ∧ (∀ b, bit b ≠ sep ∧ bit b ≠ blank) ∧ sep ≠ blank
  decoding : decode blank = none ∧ ∀ b, decode (bit b) = some b

def Programs.code (f : Programs A I) (i : ℕ) :=
  Reindex.encode (f.stateNumber i) (f.entry i) (f.machine i) f.reads

def Ports.bank (p : Ports A I) (n : ℕ) (x : Input n) :=
  packed p.inp p.blank p.sep p.bit (xbits x) (ybits x)

def Programs.start (f : Programs A I) (p : Ports A I) (i n : ℕ) (x : Input n) :
    Config A (f.Q i) I := ⟨f.entry i,p.bank n x⟩

def Ports.source [Finite A] [Finite I] (p : Ports A I) (c : Code) (enum : Tag A I ≃ Fin (M+1)) :=
  indexedSource c enum p.inp p.out p.blank p.sep p.bit p.decode

/-- For each candidate the generator contributes only a fixed additive number of
visited cells. Its finite code may add a fixed multiplicative factor to time. -/
structure Adapts [Fintype I] [DecidableEq I] {R : Type} (f : Programs A I) (p : Ports A I)
    (s : Source (Letter A I) R (Index I)) (i E : ℕ) : Prop where
  execute : ∀ n (x : Input n) {t S y}, Trace (advance (f.machine i)) (f.start p i n x) t y →
    advance (f.machine i) y = none → VisitsAtMost (f.machine i) (f.start p i n x) t S →
    ∃ u z, u+1 ≤ E*(t+1) ∧ Trace (advance s.m) (s.candidate n x i) u z ∧
      advance s.m z = none ∧ z.tape s.out = dataCell (y.tape p.out) ∧
      VisitsAtMost s.m (s.candidate n x i) u (S+E)
  forever : ∀ n (x : Input n), RunsForever (f.machine i) (f.start p i n x) →
    RunsForever s.m (s.candidate n x i)

private instance : Fintype K' := ⟨{.main,.rev,.aux,.stack},by intro k; cases k <;> simp⟩

theorem Programs.generate [Finite A] [Fintype I] [DecidableEq I]
    (f : Programs A I) (p : Ports A I) (enum : Tag A I ≃ Fin (M+1))
    (eff : Computable (fun i => GeneratorPipeline.symbolWord enum (f.code i))) :
    ∃ c : Code, ∀ i, ∃ E > 0, Adapts f p (p.source c enum) i E := by
  obtain ⟨c,hc⟩ := Generator.exists_unary_list_code _ eff
  refine ⟨c,fun i => ?_⟩
  have code := Part.eq_some_iff.mp (hc i)
  obtain ⟨C,hC,sim⟩ := GeneratorPipeline.run_numbered_sharp p.blank c enum
    (Generator.unaryInput i) (f.stateNumber i) (f.entry i) (f.machine i) f.reads f.complete code
  let E := C+8*i+24+2*(Fintype.card I+7)
  refine ⟨E,by dsimp [E]; omega,?_,?_⟩
  · intro n x t S y run halt space
    obtain ⟨s,z,ht,tr,stop,data,cells⟩ := sim (p.bank n x) run halt space
    obtain ⟨hr,hs,hv⟩ := GeneratorInputRun.run p.blank (.inr .origin) (by simp) c enum
      0 i (p.bank n x) tr stop cells
    have init := indexed_initial c enum p.inp p.out p.blank p.sep p.bit p.decode n x i
    change (p.source c enum).candidate n x i =
      initial p.blank (.inr .origin) c 0 i (p.bank n x) at init
    rw [init]
    refine ⟨_,_,?_,hr,hs,data p.out,?_⟩
    · calc
        2*i+5+s+1 ≤ (2*i+6)+C*(t+1) := by omega
        _ ≤ E*(t+1) := by dsimp [E]; nlinarith
    · obtain ⟨cells',card,contains⟩ := hv
      exact ⟨cells',card.trans (by dsimp [E]; omega),contains⟩
  · intro n x infinite
    have live := Reindex.install_numbered_forever (f.stateNumber i) (f.entry i) p.blank
      (f.machine i) f.reads f.complete (p.bank n x) infinite
    have gen := GeneratorPipeline.runsForever_of_loader p.blank c enum (Generator.unaryInput i)
      (f.code i) code (p.bank n x) live
    have init := indexed_initial c enum p.inp p.out p.blank p.sep p.bit p.decode n x i
    change (p.source c enum).candidate n x i =
      initial p.blank (.inr .origin) c 0 i (p.bank n x) at init
    rw [init]
    exact runsForever_of_pipeline p.blank (.inr .origin) (by simp) c enum 0 i (p.bank n x) gen

end
end GeneratorInputRun

end NearSquareRoot
end Computability
end OAI
