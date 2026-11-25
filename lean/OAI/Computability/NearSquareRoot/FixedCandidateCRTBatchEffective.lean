import OAI.Computability.NearSquareRoot.FixedCandidateCRTBatchKernel
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveConjugate
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepEffectiveNative

/-! # Effective physical batch composition for an actual CRT seed -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTKernel

open IntegerMultiplication Code Adic Strip Loom Dims Staff
open NearSquareRoot.Space Controlled Controlled.PermutationLayout CRTTable EffectiveBoundedTask
open private dimensions from OAI.Computability.NearSquareRoot.FixedCandidateCRTBatchKernel

noncomputable section

namespace Batch

abbrev high (p : Batch) := p.A + Packed.cap p.b (p.G-1) 0 + Packed.cap p.b (p.G-1) 0

private abbrev prepared (p : Batch) :=
  Native.prepare_spec p.valid p.sel p.side p.inv p.j p.G p.low p.depth.le p.injective p.wide p.positive p.fit

def placement (p : Batch) : Equiv.Perm (Fin p.k) := p.prepared.choose

def controller (p : Batch) : Block 2 p.A → Fin p.b → Bool :=
  Native.ctrl p.valid p.sel p.j p.placement p.side p.inv

theorem prepare_eq (p : Batch) :
    Native.prepare p.seed = ((Reflections.table p.placement,Reflections.table p.placement.symm),
      Native.model p.valid p.sel p.side p.inv p.j (PermutationLayout.offset p.placement p.G p.low p.b)) :=
  p.prepared.choose_spec.2.2.2

theorem scatter (p : Batch) {V : Type} (f : p.Address → V) (a : Block 2 p.k) :
    f (p.view (naturalStage p.placement p.controller a)) = Benes.scatter p.action f (p.view a) :=
  Native.execute_scatter p.valid p.sel p.j p.positive p.fit p.placement p.which p.batch p.side p.inv
    p.depth p.wide p.selected p.complete p.prepared.choose_spec.1 p.prepared.choose_spec.2.1 f a

end Batch

variable {X : Type} (p : X → Batch) {U : X → Type} (u : (x : X) → Series (U x))
    (f : (x : X) → (p x).Address → U x → Bead)

abbrev data (x : X) (a : Block 2 (p x).k) := f x ((p x).view a)

abbrev placed (x : X) (a : Block 2 (p x).k) :=
  data p f x ((PositionProgram.permuteNative (p x).placement).symm a)

abbrev switched (x : X) (a : Block 2 (p x).k) :=
  placed p f x (flatMask (H := (p x).G-1) (p x).A 0 (p x).low (p x).controller a)

abbrev file (v : (x : X) → Block 2 (p x).k → U x → Bead) : X → Tree :=
  cloth (fun x => line 2 (p x).k) u v

abbrev group (v : (x : X) → Block 2 (p x).k → U x → Bead) : X → Tree :=
  ReservePack.grouped u (fun x => (p x).high) (fun x => (p x).low) v

/-- Physical reads used by the candidate-indexed grouped masker. These reads
are fixed independently of the candidate's rectangle code and reserve guesses. -/
theorem seedReads (sizeBound : Dom (fun x => (p x).k) (fun x => size (p x).seed)) :
    let r := seedRegime p sizeBound
    ∃ A : Realizes r (fun x => (p x).A),
      Realizes r (fun x => (p x).low) ∧
      Realizes r (Packed.extent (fun x => (p x).G-1) (fun _ => 0) (fun x => (p x).b)) ∧
      r.Has (fun x => Packed.signs ((p x).G-1) 0 (p x).b) ∧
      (fixedRowRegime r (fun x => (p x).A) A).Has (fun z => List.ofFn ((p z.1).controller z.2)) := by
  let r := seedRegime p sizeBound
  obtain ⟨hA,hB,hC,hS⟩ := dimensions p sizeBound
  have hs : r.Has (fun x => (p x).seed) := Regime.self
  refine ⟨hA,hB,hC,hS,?_⟩
  simpa only [Batch.prepare_eq,Native.ctrl_word,Batch.controller] using
    Native.mask_has (fun x => (p x).A) hA hs

/-- Group the physical suffix, run the effective row interpreter, restore
the native records, and conjugate by the two position files computed from
the same seed. The slot programs can use a larger arena for any bad guess. -/
theorem effectiveAt (sizeBound : Dom (fun x => (p x).k) (fun x => size (p x).seed))
    (pos : ∀ x, 0 < (u x).count) :
    ∃ K : ℕ, ∀ {P : Type} [Primcodable P] {Y : P → Type} (pick : ∀ j, Y j → X)
      (T S : ∀ j, Y j → ℕ),
      (∀ j y, K ≤ (p (pick j y)).k) →
      (∀ j y, (p (pick j y)).k/16 ≤ (p (pick j y)).low) →
      (∀ j y, volume p u (pick j y) ≤ T j y) → (∀ j y, volume p u (pick j y) ≤ S j y) →
      Family T S
        (fun j => together (fun x => send (Reflections.table (p x).placement.symm)) (array p u f) ∘ pick j)
        (fun j => file p u (fun x a => data p f x (flatBitPullback (p x).placement.symm a)) ∘ pick j) →
      Family T S
        (fun j => together (fun x => send (p x).seed) (group p u (placed p f)) ∘ pick j)
        (fun j => group p u (switched p f) ∘ pick j) →
      Family T S
        (fun j => together (fun x => send (Reflections.table (p x).placement)) (file p u (switched p f)) ∘ pick j)
        (fun j => file p u (fun x a => switched p f x (flatBitPullback (p x).placement a)) ∘ pick j) →
      Family T S (fun j => together (fun x => send (p x).seed) (array p u f) ∘ pick j)
        (fun j => result p u f ∘ pick j) := by
  let r := seedRegime p sizeBound
  have hs : r.Has (fun x => (p x).seed) := Regime.self
  obtain ⟨hA,hB,hC,_,_⟩ := seedReads p sizeBound
  have grid : Realizes r (fun x => (p x).high) := (hA.plus hC).plus hC
  obtain ⟨d,bridge⟩ := ReservePack.aroundFamilyOnAt (r := r) u (fun x => (p x).high)
    (fun x => (p x).low) (fun x => (u x).count) (placed p f) (switched p f) pos
    (fun _ => le_rfl) grid hB (head := r.header) Regime.self 1 (fun _ _ _ => le_rfl) (fun _ _ _ => le_rfl)
  obtain ⟨K,hK⟩ := Filter.eventually_atTop.mp (eventually_clog_fits (16*d))
  refine ⟨K,?_⟩
  intro P inst Y pick T S large low time space forward mask backward
  have room j (y : Y j) : payloadBits d (p (pick j y)).k ≤ (p (pick j y)).low := by
    apply le_trans _ (low j y)
    have h := hK _ (large j y)
    rw [Nat.mul_assoc] at h
    unfold payloadBits
    omega
  have vol x : ReservePack.volume (fun x => (p x).high) (fun x => (p x).low) (fun x => (u x).count) x =
      volume p u x := by
    simp only [volume,ReservePack.volume,ReservePack.packed,ReservePack.records,Batch.k,maskWidth,
      Batch.high,Nat.add_zero,pow_add,Nat.mul_assoc]
  have middle := bridge pick (fun j y => (p (pick j y)).k) T S (fun _ _ => le_rfl) room
    (fun j y => (vol _).le.trans (space j y)) mask
  have middle' : Family T S (fun j => together r.header (file p u (placed p f)) ∘ pick j)
      (fun j => file p u (switched p f) ∘ pick j) := by
    obtain ⟨c,R,eff,hR,run⟩ := middle
    refine ⟨c,R,eff,hR,fun j => ⟨(run j).1,(run j).2.bound 2 1 ?_ (fun _ => by simp)⟩⟩
    intro y
    change ReservePack.volume _ _ _ _ + T j y + 1 ≤ 2*(T j y+1)
    rw [vol]
    have := time j y
    omega
  have both := relocationTables (r := r) (fun x => (p x).placement)
    (Native.prepare ∘ fun x => (p x).seed) (Native.prepare_has hs) _ Easy.fst
    (fun x => congrArg Prod.fst (p x).prepare_eq)
  have ripe : r.ripe (fun x => (volume p u x : ℝ)) :=
    ReserveStage.ripeOfWidth (r := r) (k := fun x => (p x).k) (fun _ => le_rfl)
      (fun x => Nat.le_mul_of_pos_right _ (pos x))
  have run := effectiveNaturalBatchAt (r := r) (fun x => (p x).A) (fun x => (p x).G)
    (fun x => (p x).b) (fun x => (p x).low) (fun x => (p x).placement) (fun x => (p x).controller)
    u (data p f) both.1 both.2 ripe pick T S time space forward middle' backward
  apply run.conform (fun _ _ => rfl) (fun _ _ => rfl) (fun _ _ => rfl)
  intro j y
  have eq : (fun x a => data p f x (naturalStage (p x).placement (p x).controller a)) =
      (fun x a => Benes.scatter (p x).action (f x) ((p x).view a)) := by
    funext x a v
    exact congrFun ((p x).scatter (f x) a) v
  exact congrArg (fun g => file p u g (pick j y)) eq

end
end FixedCandidate.CRTKernel

end NearSquareRoot
end Computability
end OAI
