import OAI.Computability.NearSquareRoot.FixedCandidateCRTBudgetNative
import OAI.Computability.NearSquareRoot.CRTTableNativePlanAction
import OAI.Computability.NearSquareRoot.SynchronizedPermutationSweepConjugate

/-! # One physical sparse batch on the original padded CRT array -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace FixedCandidate.CRTKernel

open IntegerMultiplication Code Adic Strip Loom Dims Staff
open NearSquareRoot.Space Controlled Controlled.PermutationLayout CRTTable

noncomputable section

/-- The mathematical index of a batch. The only part supplied to the register
machine is the unary native seed defined below. -/
structure Batch where
  A : ℕ
  b : ℕ
  G : ℕ
  low : ℕ
  n : ℕ
  L : ℕ
  j : ℕ
  box : List (ℕ × ℕ)
  valid : BoxShape.Valid (maskWidth A b G low) L box
  sel : Fin b → Fin (targetOrder box.length n).length
  injective : Function.Injective sel
  depth : n < Nat.clog 2 box.length
  wide : ∀ q, j < axisWidth box (Native.Chosen sel q)
  which : TargetIndex box.length n → ℕ
  batch : ℕ
  side : Bool
  inv : Bool
  selected : ∀ q, which (targetRank _ _ (sel q)) = batch
  complete : ∀ r, which r = batch → j < axisWidth box (targetAxis _ _ r) →
    ∃ q, targetRank _ _ (sel q) = r
  positive : 0 < G
  fit : low+2*((b+1)*G)+(Native.controlSlots (axisWidth box) sel j).length ≤ maskWidth A b G low
  sparse : (3*Packed.cap b (G-1) 0+1)*(32*b) ≤ 2^Packed.width (G-1) 0

namespace Batch
abbrev k (p : Batch) := maskWidth p.A p.b p.G p.low
abbrev seed (p : Batch) : Native.Seed := Native.seed (k := p.k) p.sel p.side p.inv p.j p.G p.low

instance (p : Batch) (g : Fin p.box.length) : NeZero (BoxFin.modulus p.box g) :=
  BoxFin.modulus_neZero p.valid g

abbrev Address (p : Batch) := CRTTable.Packed (BoxFin.modulus p.box) (axisWidth p.box) p.n
abbrev view (p : Batch) : Block 2 p.k ≃ p.Address := Native.view p.valid
abbrev action (p : Batch) : Equiv.Perm p.Address :=
  Native.subbatch p.valid p.j p.which p.batch p.side p.inv

/-- Make a physical batch from the numeric admission certificate for the
concrete guard and prefix widths. The selector and its coverage proof refer
to the original unpermuted CRT tensor. -/
def admitted {k L n b j low D Q : ℕ} {box : List (ℕ × ℕ)} {ρ : ℝ}
    (valid : BoxShape.Valid k L box)
    (sel : Fin b → Fin (targetOrder box.length n).length)
    (admission : CRTBudget.NativeAdmission sel k j low D Q ρ)
    (injective : Function.Injective sel) (depth : n < Nat.clog 2 box.length)
    (wide : ∀ q, j < axisWidth box (Native.Chosen sel q))
    (which : TargetIndex box.length n → ℕ) (batch : ℕ) (side inv : Bool)
    (selected : ∀ q, which (targetRank _ _ (sel q)) = batch)
    (complete : ∀ r, which r = batch → j < axisWidth box (targetAxis _ _ r) →
      ∃ q, targetRank _ _ (sel q) = r) : Batch where
  A := CRTBudget.nativePrefix k b low
  b := b
  G := guardWidth k
  low := low
  n := n
  L := L
  j := j
  box := box
  valid := admission.total.symm ▸ valid
  sel := sel
  injective := injective
  depth := depth
  wide := wide
  which := which
  batch := batch
  side := side
  inv := inv
  selected := selected
  complete := complete
  positive := admission.guard_pos
  fit := admission.prepare_fits.trans_eq admission.total.symm
  sparse := admission.sparse

end Batch

variable {X : Type} (p : X → Batch) {U : X → Type} (u : (x : X) → Series (U x))
    (f : (x : X) → (p x).Address → U x → Bead)

def volume (x : X) : ℕ := 2^(p x).k*(u x).count

def array : X → Tree :=
  cloth (fun x => line 2 (p x).k) u (fun x a => f x ((p x).view a))

def result : X → Tree :=
  cloth (fun x => line 2 (p x).k) u (fun x a => Benes.scatter (p x).action (f x) ((p x).view a))

/-- The actual header register contains the CRT generator seed. Its scale is
the address width, for a family whose physical seed has polynomial size. -/
def seedRegime (sizeBound : Dom (fun x => (p x).k) (fun x => size (p x).seed)) : Regime X :=
  ⟨fun x => (p x).k,fun x => send (p x).seed,sizeBound⟩

/-- Recover all dimensions used in the masked interchange directly from the
seed. This includes the prefix, computed by subtracting the guarded chunks
and the low word from the original width. -/
private theorem dimensions (sizeBound : Dom (fun x => (p x).k) (fun x => size (p x).seed)) :
    let r := seedRegime p sizeBound
    Realizes r (fun x => (p x).A) ∧ Realizes r (fun x => (p x).low) ∧
    Realizes r (Packed.extent (fun x => (p x).G-1) (fun _ => 0) (fun x => (p x).b)) ∧
    r.Has (fun x => Packed.signs ((p x).G-1) 0 (p x).b) := by
  let r := seedRegime p sizeBound
  have s : r.Has (fun x => (p x).seed) := Regime.self
  have lo : Realizes r (fun x => (p x).low) := ((s.ez Easy.snd).ez Easy.fst).ez Easy.fst
  have g : Realizes r (fun x => (p x).G) := ((s.ez Easy.snd).ez Easy.fst).ez Easy.snd
  have k : Realizes r (fun x => (p x).k) := ((s.ez Easy.snd).ez Easy.snd).ez Easy.fst
  have c : Realizes r (fun x => (p x).b) := by
    have sIds := (((s.ez Easy.snd).ez Easy.snd).ez Easy.snd).ez (Easy.ruler Easy.identity)
    have m (x : X) : ruler (List.ofFn fun q => tally ((p x).sel q).val) = tally (p x).b := by
      rw [← recover_tally (ruler _),ruler_length,List.length_ofFn]
    simpa only [Batch.seed,Native.seed,id_eq,m,Realizes,Function.comp_def] using sIds
  have h := g.minused (Realizes.fix 1)
  have chunk := (c.plus (Realizes.fix 1)).times ((h.plus (Realizes.fix 1)).plus (Realizes.fix 0))
  refine ⟨?_,lo,chunk,h.pair ((Realizes.fix 0).pair c)⟩
  have pre := k.minused ((chunk.plus chunk).plus lo)
  convert pre using 1
  funext x
  simp only [Batch.k,maskWidth,Packed.cap,Packed.width,Nat.add_zero]
  omega

/-- A single command handles every batch chosen after its reserve degree is
fixed. Both placement tables and every prefix controller are computed from
the same physical seed. The output is the scatter by the selected CRT stage. -/
theorem bounded (ρ : ℝ) (hρ : 1/2 < ρ)
    (sizeBound : Dom (fun x => (p x).k) (fun x => size (p x).seed))
    (positive : ∀ x, 0 < (u x).count) :
    ∃ D : ℕ, ∀ {Y : Type} (pick : Y → X) (factor : Y → ℕ),
      (∀ y, payloadBits D (p (pick y)).k ≤ (p (pick y)).low) →
      (∀ y, 2*((((p (pick y)).b+1)*(p (pick y)).G+1:ℕ):ℝ)^ρ ≤ factor y) →
      (∀ y, factor y ≤ 2^(p (pick y)).A) →
      BoundedTask (fun y => volume p u (pick y)*
        (PositionProgram.positionFactor ρ (p (pick y)).k+factor y+1)) (volume p u ∘ pick)
        (together (fun x => send (p x).seed) (array p u f) ∘ pick) (result p u f ∘ pick) := by
  let r := seedRegime p sizeBound
  have hs : r.Has (fun x => (p x).seed) := Regime.self
  obtain ⟨hA,hB,hc,shape⟩ := dimensions p sizeBound
  choose π placed place offsets spec using fun x =>
    Native.prepare_spec (p x).valid (p x).sel (p x).side (p x).inv (p x).j (p x).G (p x).low
      (p x).depth.le (p x).injective (p x).wide (p x).positive (p x).fit
  let ctrl x := Native.ctrl (p x).valid (p x).sel (p x).j (π x) (p x).side (p x).inv
  have plan := Native.prepare_has hs
  have forward : r.Has (fun x => Reflections.table (π x)) := by
    simpa only [Function.comp_apply,Batch.seed,spec] using ((plan.ez Easy.fst).ez Easy.fst)
  have backward : r.Has (fun x => Reflections.table (π x).symm) := by
    simpa only [Function.comp_apply,Batch.seed,spec] using ((plan.ez Easy.fst).ez Easy.snd)
  have mask := Native.mask_has (fun x => (p x).A) hA hs
  simp only [Batch.seed,spec,Native.ctrl_word] at mask
  have ripe : r.ripe (fun x => (volume p u x : ℝ)) :=
    ReserveStage.ripeOfWidth (r := r) (k := fun x => (p x).k) (fun _ => le_rfl) (fun x =>
      Nat.le_mul_of_pos_right _ (positive x))
  obtain ⟨D,run⟩ := naturalBatch (r := r) (fun x => (p x).A) (fun x => (p x).G)
    (fun x => (p x).b) (fun x => (p x).low) ρ hρ hA hB hc shape (fun x => (p x).sparse)
    π ctrl mask forward backward u positive (fun x a => f x ((p x).view a)) ripe
  refine ⟨D,fun pick factor room rate rows => ?_⟩
  have clock y : 2*Spindle.modes (Packed.extent (fun x => (p x).G-1) (fun _ => 0)
      (fun x => (p x).b)) (τ := ρ) (pick y) ≤ factor y := by
    have hg := (p (pick y)).positive
    simpa only [Spindle.modes,Packed.extent,Packed.cap,Packed.width,Nat.add_zero,
      Nat.sub_add_cancel hg] using rate y
  apply (run pick (fun y => (p (pick y)).k) factor (fun _ => le_rfl) room clock rows).conform
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)
  intro y
  have eq : (fun x a => f x ((p x).view (naturalStage (π x) (ctrl x) a))) =
      (fun x a => Benes.scatter (p x).action (f x) ((p x).view a)) := by
    funext x a v
    apply congrFun _ v
    exact Native.execute_scatter (p x).valid (p x).sel (p x).j (p x).positive (p x).fit
      (π x) (p x).which (p x).batch (p x).side (p x).inv (p x).depth (p x).wide
      (p x).selected (p x).complete (placed x) (place x) (f x) a
  exact congrArg (fun g => cloth (fun x => line 2 (p x).k) u g (pick y)) eq

/-- The literal low reserve of the CRT directory covers the polynomial degree
of the row program at every sufficiently large width. The native classifier
provides the two logarithmic high-reserve slots for the integral row clock. -/
theorem bounded_fixedLow (ρ : ℝ) (hρ : 1/2 < ρ) (hu : ρ ≤ 1)
    (sizeBound : Dom (fun x => (p x).k) (fun x => size (p x).seed))
    (positive : ∀ x, 0 < (u x).count) :
    ∃ K : ℕ, ∀ {Y : Type} (pick : Y → X),
      (∀ y, K ≤ (p (pick y)).k) →
      (∀ y, (p (pick y)).k/16 ≤ (p (pick y)).low) →
      (∀ y, payloadBits 2 (p (pick y)).k ≤ (p (pick y)).A) →
      BoundedTask (fun y => CRTBudget.batchClock ρ (p (pick y)).k (volume p u (pick y)))
        (volume p u ∘ pick)
        (together (fun x => send (p x).seed) (array p u f) ∘ pick) (result p u f ∘ pick) := by
  obtain ⟨D,run⟩ := bounded p u f ρ hρ sizeBound positive
  obtain ⟨K,small⟩ := Filter.eventually_atTop.mp (eventually_clog_fits (16*D))
  refine ⟨max 1 K,fun pick large low high => ?_⟩
  let factor y := SynchronizedPermutationBudget.rowFactor (p (pick y)).k ρ
  have reserve y : payloadBits D (p (pick y)).k ≤ (p (pick y)).low := by
    apply le_trans _ (low y)
    have h := small _ ((le_max_right ..).trans (large y))
    rw [Nat.mul_assoc] at h
    unfold payloadBits
    omega
  have rate y : 2*((((p (pick y)).b+1)*(p (pick y)).G+1:ℕ):ℝ)^ρ ≤ factor y := by
    have fit := (p (pick y)).fit
    have h := SynchronizedPermutationBudget.row_rate (ρ := ρ)
      (show ((p (pick y)).b+1)*(p (pick y)).G ≤ (p (pick y)).k by unfold Batch.k; omega) (by linarith)
    simpa only [Nat.cast_add,Nat.cast_one] using h
  have rows y : factor y ≤ 2^(p (pick y)).A :=
    (SynchronizedPermutationBudget.row_factor_high ((le_max_left ..).trans (large y)) hu).trans
      (Nat.pow_le_pow_right (by decide) (high y))
  apply (run pick factor reserve rate rows).mono _ (fun _ => le_rfl)
  intro y
  unfold CRTBudget.batchClock
  apply Nat.mul_le_mul_left
  dsimp only [factor]
  omega

end
end FixedCandidate.CRTKernel

end NearSquareRoot
end Computability
end OAI
