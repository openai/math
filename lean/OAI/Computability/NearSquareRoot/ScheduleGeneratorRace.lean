import OAI.Computability.NearSquareRoot.ScheduleGeneratorCandidate

/-! # A single literal multitape multiplier from effective staged candidates -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorInputRun
open IntegerMultiplication TM Universal ScheduleMachine Filter Uniform.IndexedSlot
open scoped Classical
noncomputable section
variable {A I : Type} {M : ℕ}

/-- This only charges the particular successful comparison. Other candidates may time
out at arbitrary widths or run forever. -/
def Programs.Completes (f : Programs A I) (p : Ports A I) (i n : ℕ) (x : Input n)
    (t S : ℕ) : Prop :=
  ∃ y, Trace (advance (f.machine i)) (f.start p i n x) t y ∧ advance (f.machine i) y = none ∧
    VisitsAtMost (f.machine i) (f.start p i n x) t S

/-- Soundness quantifies over all halting programs. Each target exponent may choose
any one index, which can encode a template, arbitrary majorants and a digit split. -/
structure Programs.Comparisons (f : Programs A I) (p : Ports A I) (D K b : ℕ) : Prop where
  sound : ∀ i n (x : Input n) {t y}, Trace (advance (f.machine i)) (f.start p i n x) t y →
    advance (f.machine i) y = none → ∃ z, Source.Valid n x z ∧ whole p.blank (z.map p.bit) (y.tape p.out)
  fallback : ∀ n (x : Input n), ∃ t, f.Completes p 0 n x t (D*(n+1)) ∧ t+1 ≤ K*(n+1)^b
  fast : ∀ j : ℕ, ∃ i : ℕ, ∃ H : ℝ, 0 ≤ H ∧ ∀ᶠ n in atTop, ∀ x : Input n,
    ∃ t, f.Completes p i n x t (D*(n+1)) ∧
      ((t+1 : ℕ) : ℝ) ≤ H*n*logScale n^((1:ℝ)/2+1/(j+2:ℝ))

theorem whole_data {blank : A} {w : List A} {T : Tape A} (h : whole blank w T) :
    whole (.inl blank) (w.map Sum.inl) (dataCell (I := I) T) := by
  unfold whole
  rw [←data_loaded]
  funext j
  exact congrArg Sum.inl (congrFun h j)

private theorem finite_space [Fintype I] {Q : Type} (m : Rule A Q I) (x : Config A Q I) (t : ℕ) :
    ∃ S, VisitsAtMost m x t S := by
  apply Exists.intro _ (visitsAtMost_of_tape_fences (fun i => (x.tape i).pos-t)
    (fun i => (x.tape i).pos+t) ?_)
  intro k hk z tr i
  have dis := head_excursion tr i
  omega

private theorem fence_of_cover {B Q J : Type} [Fintype J] [DecidableEq J]
    {s : Source B Q J} {n : ℕ} {x : Input n} {i t S L : ℕ} {y}
    (run : Trace (advance s.m) (s.candidate n x i) t y)
    (cover : VisitsAtMost s.m (s.candidate n x i) t S) (hs : S ≤ L*(2*n+1)) :
    FencedRun s.m (Source.scaledLower L n) (Source.scaledUpper L n) (s.candidate n x i) t y := by
  refine ⟨run,fun u hu z hz j => ?_⟩
  have rad := Uniform.radius_of_visits cover hu hz j
  have origin := Uniform.SlotLayout.raw_origins s.start (s.input n x) s.idx s.blank s.unary
    (s.input_origins n x) i j
  change ((s.candidate n x i).tape j).pos = 0 at origin
  rw [origin] at rad
  dsimp only [Source.scaledLower,Source.scaledUpper]
  omega

private instance : Fintype Turing.PartrecToTM2.K' :=
  ⟨{.main,.rev,.aux,.stack},by intro k; cases k <;> simp⟩

/-- All fixed generator costs and distinct-cell overheads are absorbed outside the
comparison quantifiers. The physical scheduler starts every trial on a common absolute fence. -/
theorem Programs.uniformMultiplicationSpec [Finite A] [Fintype I] [DecidableEq I] [DecidableEq A]
    (f : Programs A I) (p : Ports A I) (enum : Tag A I ≃ Fin (M+1))
    (eff : Computable (fun i => GeneratorPipeline.symbolWord enum (f.code i)))
    {D K b : ℕ} (runs : f.Comparisons p D K b) : UniformMultiplicationSpec := by
  classical
  obtain ⟨c,build⟩ := f.generate p enum eff
  choose E _ adapt using build
  let s := p.source c enum
  let L := D+E 0+1
  let : Finite (GeneratorPipeline.Control c M) := GeneratorPipeline.finite_control c M
  apply s.uniformMultiplicationSpec_scaled L (by dsimp [L]; omega) (K := E 0*K) (p := b)
  constructor
  · refine ⟨fun _ _ eq => p.letters.1 (Sum.inl.inj eq),fun d => ?_,?_⟩
    · exact ⟨fun eq => (p.letters.2.1 d).1 (Sum.inl.inj eq),fun eq => (p.letters.2.1 d).2 (Sum.inl.inj eq)⟩
    · exact fun eq => p.letters.2.2 (Sum.inl.inj eq)
  · refine ⟨by simp [s,Ports.source,indexedSource,dataIndex],?_,by simp [s,Ports.source,indexedSource,dataIndex]⟩
    simpa [s,Ports.source,indexedSource,dataIndex] using p.distinct
  · exact p.decoding
  · intro n x i u y ran stop
    by_cases hit : ∃ t z, Trace (advance (f.machine i)) (f.start p i n x) t z ∧ advance (f.machine i) z = none
    · obtain ⟨t,z,tr,hz⟩ := hit
      obtain ⟨S,vis⟩ := finite_space (f.machine i) (f.start p i n x) t
      obtain ⟨_,a,_,ra,ha,output,_⟩ := (adapt i).execute n x tr hz vis
      obtain ⟨bits,ok,hw⟩ := runs.sound i n x tr hz
      rw [(halting_trace_unique ran stop ra ha).2]
      refine ⟨bits,ok,?_⟩
      change whole (.inl p.blank) (bits.map fun b => .inl (p.bit b)) (a.tape (p.source c enum).out)
      rw [output]
      simpa only [List.map_map, Function.comp_def] using (whole_data (I := I) hw)
    · exact ((runsForever_iff _ _).mp ((adapt i).forever n x ((runsForever_iff _ _).mpr hit)) ⟨u,y,ran,stop⟩).elim
  · intro n x
    obtain ⟨t,⟨z,tr,stop,space⟩,ht⟩ := runs.fallback n x
    obtain ⟨u,a,hu,ra,ha,_,hv⟩ := (adapt 0).execute n x tr stop space
    refine ⟨u,a,fence_of_cover ra hv (by dsimp [L]; nlinarith),ha,?_⟩
    simpa only [← Nat.mul_assoc] using hu.trans (Nat.mul_le_mul_left (E 0) ht)
  · intro j
    obtain ⟨i,H,hH,good⟩ := runs.fast j
    refine ⟨i,(E i : ℝ)*H,by positivity,?_⟩
    filter_upwards [good,eventually_ge_atTop (E i)] with n hn large
    intro x
    obtain ⟨t,⟨z,tr,stop,space⟩,ht⟩ := hn x
    obtain ⟨u,a,hu,ra,ha,_,hv⟩ := (adapt i).execute n x tr stop space
    refine ⟨u,a,fence_of_cover ra hv (by dsimp [L]; nlinarith),ha,?_⟩
    have hreal : ((u+1 : ℕ) : ℝ) ≤ (E i : ℝ) * ((t+1 : ℕ) : ℝ) := by exact_mod_cast hu
    calc
      _ ≤ _ := hreal
      _ ≤ (E i : ℝ)*(H*n*logScale n^((1:ℝ)/2+1/(j+2:ℝ))) := mul_le_mul_of_nonneg_left ht (by positivity)
      _ = _ := by ring

end
end GeneratorInputRun

end NearSquareRoot
end Computability
end OAI
