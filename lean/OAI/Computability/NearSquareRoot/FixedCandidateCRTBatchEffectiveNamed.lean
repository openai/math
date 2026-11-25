import OAI.Computability.NearSquareRoot.FixedCandidateCRTBatchEffective
import OAI.Computability.NearSquareRoot.FixedCandidateCRTBatchEffectivePrice
import OAI.Computability.NearSquareRoot.FixedCandidateCRTBatchPriceSize
import OAI.Computability.NearSquareRoot.SynchronizedPermutationConjugateCompiled

/-! # The named CRT batch command on arbitrary position-reserve guesses -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTKernel
open IntegerMultiplication Code Adic Strip Loom
open Controlled Controlled.PermutationLayout EffectiveBoundedTask CommonRegisters GeneratorSyntax

noncomputable section

variable {X : Type} (p : X → Batch) {U : X → Type} (u : (x : X) → Series (U x))
    (f : (x : X) → (p x).Address → U x → Bead)

abbrev input : X → Tree := together (fun x => send (p x).seed) (array p u f)

/-- Compile the CRT seed and physical array against an actual rectangle file.
All guesses execute the same scatter. A sufficient pair of position reserves
and sufficient room in the physical low word give the quantitative bound. -/
theorem named (sizeBound : Dom (fun x => (p x).k) (fun x => size (p x).seed))
    (pos : ∀ x, 0 < (u x).count) :
    ∃ (pre post : Cmd) (mid : Controlled.Effective.Template), ∀ c ρ, 0 ≤ ρ →
      Controlled.Effective.rectContract c ρ →
      (∀ a b, ∃ T S : X → ℕ, Runs (Controlled.Effective.BatchCmd.compile pre post mid a b c)
        T S (input p u f) (result p u f)) ∧
      ∃ d : ℕ, ∀ a b, d ≤ a → d ≤ b → ⌈ρ⌉₊+2 ≤ b → ∀ {Y : Type} (pick : Y → X),
        (∀ y, payloadBits d (p (pick y)).k ≤ (p (pick y)).low) →
        (∀ y, SynchronizedPermutationBudget.rowFactor (p (pick y)).k ρ ≤ 2^(p (pick y)).A) →
        Runs (Controlled.Effective.BatchCmd.compile pre post mid a b c)
          (fun y => CRTBudget.batchClock ρ (p (pick y)).k (volume p u (pick y))) (volume p u ∘ pick)
          (input p u f ∘ pick) (result p u f ∘ pick) := by
  let r := seedRegime p sizeBound
  have hs : r.Has (fun x => (p x).seed) := Regime.self
  obtain ⟨hA,hB,hC,shape,mask⟩ := seedReads p sizeBound
  have tables := relocationTables (r := r) (fun x => (p x).placement)
    (CRTTable.Native.prepare ∘ fun x => (p x).seed) (CRTTable.Native.prepare_has hs) _ Easy.fst
    (fun x => congrArg Prod.fst (p x).prepare_eq)
  have ripe : r.ripe (fun x => (volume p u x : ℝ)) :=
    ReserveStage.ripeOfWidth (r := r) (k := fun x => (p x).k) (fun _ => le_rfl)
      (fun x => Nat.le_mul_of_pos_right _ (pos x))
  obtain ⟨pre,post,mid,run⟩ := compiledNaturalBatch (r := r) (fun x => (p x).A) (fun x => (p x).G)
    (fun x => (p x).b) (fun x => (p x).low) hA hB hC shape (fun x => (p x).sparse)
    (fun x => (p x).placement) (fun x => (p x).controller) mask tables.1 tables.2 u pos (data p f) ripe
  have dst : file p u (fun x a => data p f x (naturalStage (p x).placement (p x).controller a)) =
      result p u f := by
    have eq : (fun x a => data p f x (naturalStage (p x).placement (p x).controller a)) =
        (fun x a => Benes.scatter (p x).action (f x) ((p x).view a)) := by
      funext x a v
      exact congrFun ((p x).scatter (f x) a) v
    exact congrArg (file p u) eq
  refine ⟨pre,post,mid,?_⟩
  intro c ρ hρ rect
  obtain ⟨total,d,fast⟩ := run c ρ hρ rect
  refine ⟨fun a b => ?_,d,?_⟩
  · obtain ⟨T,S,exec⟩ := total a b
    exact ⟨T,S,dst ▸ exec⟩
  · intro a b ha hb hv Y pick room high
    let factor y := SynchronizedPermutationBudget.rowFactor (p (pick y)).k ρ
    have rate y : 2*Spindle.modes (Packed.extent (fun x => (p x).G-1) (fun _ => 0)
        (fun x => (p x).b)) (τ := ρ) (pick y) ≤ factor y := by
      have fit := (p (pick y)).fit
      have h := SynchronizedPermutationBudget.row_rate (ρ := ρ)
        (show ((p (pick y)).b+1)*(p (pick y)).G ≤ (p (pick y)).k by unfold Batch.k; omega) hρ
      have posG := (p (pick y)).positive
      simpa only [Spindle.modes,Packed.extent,Packed.cap,Packed.width,Nat.add_zero,
        Nat.sub_add_cancel posG,Nat.cast_add,Nat.cast_one] using h
    have measured := fast a b ha hb hv pick (fun y => (p (pick y)).k) factor (fun _ => le_rfl) room rate high
    rw [← dst]
    apply measured.mono _ (fun _ => le_rfl)
    intro y
    unfold CRTBudget.batchClock
    apply Nat.mul_le_mul_left
    dsimp only [factor,Batch.k]
    omega

/-- Choose the needed degree for each certified rectangle before choosing the
candidate's numeric guesses. The width-only clock and arena price the same
effective file on every input, including inputs of unsuccessful guesses. -/
theorem compiledProfile (sizeBound : Dom (fun x => (p x).k) (fun x => size (p x).seed))
    (pos : ∀ x, 0 < (u x).count) {J : Type} [Primcodable J]
    (c : J → Cmd) (R : ℕ) (emit : GeneratorSyntax.Effective ltr c) (registers : ∀ j, Within R (c j))
    (θ : J → ℝ) (positive : ∀ j, 0 ≤ θ j) (rect : ∀ j, Controlled.Effective.rectContract (c j) (θ j)) :
    ∃ need : J → ℕ, ∀ {P : Type} [Primcodable P] {Y : P → Type} (pick : ∀ z, Y z → X)
      (index : P → J) (a b D : P → ℕ), Computable index → Computable a → Computable b →
      ∀ (w : ∀ z, Y z → ℕ) (kAt VAt : ℕ → ℕ) (cut : P → ℕ) (good : P → Prop),
      (∀ z y, (p (pick z y)).k = kAt (w z y)) →
      (∀ z y, volume p u (pick z y) ≤ VAt (w z y)) →
      (∃ C : ℕ, ∀ z y, VAt (w z y) ≤ C*(w z y+1)) →
      (∀ z, good z → need (index z) ≤ a z ∧ need (index z) ≤ b z ∧
        ⌈θ (index z)⌉₊+2 ≤ b z ∧ need (index z) ≤ D z) →
      (∀ z, good z → ∀ y, cut z ≤ w z y → payloadBits (D z) (p (pick z y)).k ≤ (p (pick z y)).low) →
      (∀ z, good z → ∀ y, cut z ≤ w z y →
        SynchronizedPermutationBudget.rowFactor (p (pick z y)).k (θ (index z)) ≤ 2^(p (pick z y)).A) →
      ∃ arena clock : P → ℕ → ℕ,
        Family (fun z y => clock z (w z y)) (fun z y => arena z (w z y))
          (fun z => input p u f ∘ pick z) (fun z => result p u f ∘ pick z) ∧
        (∀ z n, n ≤ arena z n ∧ arena z n ≤ clock z n) ∧
        ∀ z, good z → ∀ n ≥ cut z, arena z n = n ∧
          clock z n = max n (CRTBudget.batchClock (θ (index z)) (kAt n) (VAt n)) := by
  obtain ⟨pre,post,mid,program⟩ := named p u f sizeBound pos
  have run j := program (c j) (θ j) (positive j) (rect j)
  choose need sharp using fun j => (run j).2
  refine ⟨need,?_⟩
  intro P inst Y pick index a b D ei ea eb w kAt VAt cut good width support compact admissible low high
  obtain ⟨C,cap⟩ := compact
  let cmd z := Controlled.Effective.BatchCmd.compile pre post mid (a z) (b z) (c (index z))
  obtain ⟨B,hB,sites⟩ := Controlled.Effective.BatchCmd.within pre post mid R
  let all (s : Sigma Y) := pick s.1 s.2
  obtain ⟨K,key⟩ := seed_tables_le_width (p ∘ all) (width := fun s => w s.1 s.2)
    (sizeBound.map all) (fun s => pos (all s)) ⟨C,fun s => (support s.1 s.2).trans (cap s.1 s.2)⟩
  refine total_width_budgets good cut w (fun z => input p u f ∘ pick z) (fun z => result p u f ∘ pick z)
    (fun _ n => (K+5*C+1)*(n+1)) (fun _ n => 5*C*(n+1))
    (fun z n => CRTBudget.batchClock (θ (index z)) (kAt n) (VAt n)) ?_ ?_ cmd B (Controlled.Effective.BatchCmd.effective pre post mid ea eb (emit.comp ei)) hB
    (fun z => sites (a z) (b z) _ (registers _)) ?_ ?_
  · intro z y
    have kh := key ⟨z,y⟩ (p (pick z y)).placement
    change size (p (pick z y)).seed + _ + _ ≤ K*(w z y+1) at kh
    have h := (batchArrayCaps p u pos f (pick z y)).1.trans
      (Nat.mul_le_mul_left 5 ((support z y).trans (cap z y)))
    change size (p (pick z y)).seed + (array p u f (pick z y)).count + 1 ≤ _
    simp only [Nat.add_mul,Nat.mul_assoc]
    omega
  · intro z y
    have h := (batchArrayCaps p u pos f (pick z y)).2.trans
      (Nat.mul_le_mul_left 5 ((support z y).trans (cap z y)))
    change (result p u f (pick z y)).count ≤ 5*C*(w z y+1)
    simpa only [Nat.mul_assoc] using h
  · intro z y
    obtain ⟨T,S,total⟩ := (run (index z)).1 (a z) (b z)
    obtain ⟨A,exec⟩ := total.withoutSpace
    exact ⟨A*(T (pick z y)+1),exec (pick z y)⟩
  · intro z hz
    let pull (y : {y : Y z // cut z ≤ w z y}) := pick z y.val
    obtain ⟨ha,hb,hr,he⟩ := admissible z hz
    have priced := sharp (index z) (a z) (b z) ha hb hr pull
      (fun y => (Nat.mul_le_mul_right _ he).trans (low z hz y.val y.property))
      (fun y => high z hz y.val y.property)
    apply priced.bound 1 (C+1)
    · intro y
      simp only [Nat.one_mul]
      apply Nat.succ_le_succ
      change CRTBudget.batchClock _ (p (pick z y.val)).k (volume p u (pick z y.val)) ≤ _
      rw [width z y.val]
      exact Nat.mul_le_mul_right _ (support z y.val)
    · intro y
      have h := (support z y.val).trans (cap z y.val)
      change volume p u (pick z y.val)+1 ≤ (C+1)*(w z y.val+1)
      rw [Nat.succ_mul]
      omega

end
end FixedCandidate.CRTKernel

end NearSquareRoot
end Computability
end OAI
