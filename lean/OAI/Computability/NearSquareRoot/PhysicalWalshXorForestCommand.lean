import OAI.Computability.NearSquareRoot.PhysicalWalshXorForest
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffective

/-! # Named commands for the aligned XOR opcode schedule

A single header program prepares the annotated forest on the initial parameter
family. Every restricted call uses this same program and a three-register
tail loop around the supplied native opcode interpreter.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalsh

open IntegerMultiplication Code Strip Space EffectiveBoundedTask CommonRegisters GeneratorSyntax
open Controlled Controlled.PositionPreparation Controlled.PositionProgram

namespace XorSweep

theorem boundedProgramNamed {c : Cmd} {X : Type} {Y : X → Type} (k G : X → ℕ) (positive : ∀ x, 0 < G x)
    (key : X → Op → Tree) (box : (x : X) → ((Fin (k x) → Bool) → Y x) → Tree)
    (budget volume : X → ℕ) (charge : X → Op → ℕ)
    (stage : Runs c (fun j : (x : X) × {q // q ∈ program (k x/3) (G x)} × ((Fin (k x) → Bool) → Y x) => charge j.1 j.2.1)
      (fun j => volume j.1) (fun j => .fork (key j.1 j.2.1) (box j.1 j.2.2))
      (fun j => box j.1 (j.2.2 ∘ fun w => act (G j.1) w j.2.1)))
    (forest : ∀ x, (Task.forest (key x) (program (k x/3) (G x))).count ≤ volume x)
    (live : ∀ x f, (box x f).count ≤ volume x)
    (cost : ∀ x, ∀ q ∈ program (k x/3) (G x), charge x q + (key x q).count + 1 ≤ budget x) :
    Runs (RegisterTagFold.command c) (fun j : (x : X) × ((Fin (k x) → Bool) → Y x) => (4+3*G j.1)*budget j.1+1)
      (fun j => volume j.1)
      (fun j => .fork (Task.forest (key j.1) (program (k j.1/3) (G j.1))) (box j.1 j.2))
      (fun j => box j.1 (j.2 ∘ directed (gate (k j.1/3)))) :=
  command_contract (RegisterTagFold.command c) from
    boundedProgram k G positive key box budget volume charge stage.task forest live cost

end XorSweep

namespace XorForest

variable {X : Type} {r : Regime X}

/-- Annotate the schedule on the left, followed by the bounded table fold. -/
def programCmd (prep stage : Cmd) : Cmd :=
  (KernelEffectiveFamily.leftCmd prep).join (RegisterTagFold.command stage)

theorem programCmd_effective {P : Type} [Primcodable P] {prep stage : P → Cmd}
    (hp : Effective ltr prep) (hs : Effective ltr stage) :
    Effective ltr (fun p => programCmd (prep p) (stage p)) :=
  (KernelEffectiveFamily.effective_left hp).join (RegisterTagFold.effective hs)

theorem programCmd_within {R : ℕ} (hR : 3 ≤ R) {prep stage : Cmd}
    (hp : Within R prep) (hs : Within R stage) : Within R (programCmd prep stage) :=
  ⟨KernelEffectiveFamily.within_left (by omega) hp,RegisterTagFold.within hR _ hs⟩

variable {ops : X → List Op}

/-- The forest constructor is chosen once for the parameter regime before
any of its later restrictions, opcode routines, or clock bounds are supplied. -/
private theorem namedPrep (h : r.Has ops) : ∃ c : Cmd, ∃ D H : ℕ,
    let b x := H*(r.scale x+1)^D
    let key x (q : Op) := Tree.fork (r.header x) (send q)
    let forest x := Task.forest (key x) (ops x)
    Runs c b b r.header forest ∧ (∀ x, (forest x).count ≤ b x) ∧
      ∀ x q, q ∈ ops x → (key x q).count ≤ b x := by
  obtain ⟨D,H,⟨cmd,run⟩,forest,keys⟩ := bounded (default : Op) h
  exact ⟨cmd,D,H,run,forest,keys⟩

noncomputable def prepCmd (h : r.Has ops) : Cmd := (namedPrep h).choose

theorem prepCmd_spec (h : r.Has ops) : ∃ D H : ℕ,
    let b x := H*(r.scale x+1)^D
    let key x (q : Op) := Tree.fork (r.header x) (send q)
    let forest x := Task.forest (key x) (ops x)
    Runs (prepCmd h) b b r.header forest ∧ (∀ x, (forest x).count ≤ b x) ∧
      ∀ x q, q ∈ ops x → (key x q).count ≤ b x := (namedPrep h).choose_spec

theorem boundedProgramWith {prepCmd : Cmd} (k G : X → ℕ)
    (D H : ℕ)
    (prep : Runs prepCmd (fun x => H*(r.scale x+1)^D) (fun x => H*(r.scale x+1)^D) r.header
      (fun x => Task.forest (fun q : Op => .fork (r.header x) (send q)) (XorSweep.program (k x/3) (G x))))
    (forestCap : ∀ x, (Task.forest (fun q : Op => .fork (r.header x) (send q))
      (XorSweep.program (k x/3) (G x))).count ≤ H*(r.scale x+1)^D)
    (keyCap : ∀ x q, q ∈ XorSweep.program (k x/3) (G x) →
      (Tree.fork (r.header x) (send q)).count ≤ H*(r.scale x+1)^D) :
    ∀ {J : Type} (select : J → X) {Y : J → Type}
      (box : (j : J) → ((Fin (k (select j)) → Bool) → Y j) → Tree)
      (V factor : J → ℕ) (C : ℕ),
      (∀ j, 0 < G (select j)) → (∀ j, (r.scale (select j)+1)^D ≤ V j) →
      (∀ j f, (box j f).count ≤ C*V j) →
      let key j (q : Op) := Tree.fork (r.header (select j)) (send q)
      let stages j := XorSweep.program (k (select j)/3) (G (select j))
      let cost j := V j*(factor j+1)
      ∀ {stage : Cmd}, Runs stage (fun i : (j : J) × {q // q ∈ stages j} × ((Fin (k (select j)) → Bool) → Y j) => cost i.1)
        (fun i => V i.1) (fun i => .fork (key i.1 i.2.1) (box i.1 i.2.2))
        (fun i => box i.1 (i.2.2 ∘ fun w => act (G (select i.1)) w i.2.1)) →
      Runs (programCmd prepCmd stage) (fun i : (j : J) × ((Fin (k (select j)) → Bool) → Y j) =>
        (4+3*G (select i.1))*cost i.1+1) (fun i => V i.1)
        (fun i => .fork (r.header (select i.1)) (box i.1 i.2))
        (fun i => box i.1 (i.2 ∘ directed (XorSweep.gate (k (select i.1)/3)))) := by
  intro J select Y box V factor C pos reserve cell key stages cost stage run
  exact command_contract (programCmd prepCmd stage) from
    boundedProgramWithSetup k G D H prep.task forestCap keyCap select box V factor C pos reserve cell run.task

theorem boundedProgramOnNamed (k G : X → ℕ)
    (h : r.Has (fun x => XorSweep.program (k x/3) (G x))) :
    ∃ D : ℕ, ∀ {J : Type} (select : J → X) {Y : J → Type}
      (box : (j : J) → ((Fin (k (select j)) → Bool) → Y j) → Tree)
      (V factor : J → ℕ) (C : ℕ),
      (∀ j, 0 < G (select j)) → (∀ j, (r.scale (select j)+1)^D ≤ V j) →
      (∀ j f, (box j f).count ≤ C*V j) →
      let key j (q : Op) := Tree.fork (r.header (select j)) (send q)
      let stages j := XorSweep.program (k (select j)/3) (G (select j))
      let cost j := V j*(factor j+1)
      ∀ {stage : Cmd}, Runs stage (fun i : (j : J) × {q // q ∈ stages j} × ((Fin (k (select j)) → Bool) → Y j) => cost i.1)
        (fun i => V i.1) (fun i => .fork (key i.1 i.2.1) (box i.1 i.2.2))
        (fun i => box i.1 (i.2.2 ∘ fun w => act (G (select i.1)) w i.2.1)) →
      Runs (programCmd (prepCmd h) stage) (fun i : (j : J) × ((Fin (k (select j)) → Bool) → Y j) =>
        (4+3*G (select i.1))*cost i.1+1) (fun i => V i.1)
        (fun i => .fork (r.header (select i.1)) (box i.1 i.2))
        (fun i => box i.1 (i.2 ∘ directed (XorSweep.gate (k (select i.1)/3)))) := by
  obtain ⟨D,H,prep,forestCap,keyCap⟩ := prepCmd_spec h
  exact ⟨D,boundedProgramWith k G D H prep forestCap keyCap⟩

end XorForest
end PhysicalWalsh

end NearSquareRoot
end Computability
end OAI
