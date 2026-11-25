import OAI.Computability.NearSquareRoot.InterchangeROMRepairStage
import OAI.Computability.NearSquareRoot.InterchangeRepairPhysical

/-! # The selected ground-field repair on a physical interchange layout

The large row bank stays in ground-field coordinates. The correction converts
only its two check blocks into spectral coordinates and converts the two output
blocks back. All four predictors use the same grouped rectangle program.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

noncomputable section

namespace InterchangeROMRepair.Physical

open Interchange SwapSpectrum Matrix

variable {R L X U V C : Type} [Field R] [Fintype U] [Fintype V] {m : ℕ}

abbrev Bank (R L X V : Type) := L → X → V → R

def gather {R L X U V : Type} [Field R] [Fintype V]
    (A : Matrix U V R) (x : Bank R L X V) : Bank R L X U := fun w z => A *ᵥ x w z

def sweep (f : (X → R) → X → R) (x : Bank R L X U) : Bank R L X U :=
  fun w z u => f (fun a => x w a u) z

def applyTag (t : Spec R V U m) (tag : X → Fin m → Bool) (out : Bool)
    (v w : Bank R L X U) : Bank R L X U := fun l z =>
  t.correct (tag z) out false *ᵥ v l z + t.correct (tag z) out true *ᵥ w l z

/-- The three live banks at the correction boundary are the saved first predictor
and the forward transforms of its check projection and of the input projection. -/
def schedule (t : Spec R V U m) (half : R) (tag : X → Fin m → Bool)
    (fw bw : (X → R) → X → R) (P : Bank R L X V → Bank R L X V)
    (x : Bank R L X V) : Bank R L X V :=
  let px := P x
  let a := sweep fw (gather t.extract px)
  let b := sweep fw (gather t.extract x)
  let v := sweep bw (applyTag t tag false a b)
  let w := sweep bw (applyTag t tag true a b)
  let z := P (gather t.restore v)
  let w' := gather t.restore w
  let cube := P (P px)
  px - half • (cube - px) - z + w'

def fibre {Y : Type} (key : Y → X) (w : L) (x : Bank R L X V) : V → Y → R :=
  fun i a => x w (key a) i

omit [Fintype U] in
private theorem gather_fibre (key : Address (Fin m) C → X) (w : L)
    (A : Matrix U V R) (x : Bank R L X V) :
    fibre key w (gather A x) = mix A (fibre key w x) := by
  funext i a
  simp [fibre,gather,mix,Matrix.mulVec,dotProduct,Finset.sum_apply]

theorem schedule_on_fibre [LinearOrder C] (t : Spec R V U m) (d : ℕ) (half : R) (hh : 2*half=1)
    (tag : X → Fin m → Bool) (fw bw : (X → R) → X → R) (P : Bank R L X V → Bank R L X V)
    (key : Address (Fin m) C → X) (w : L)
    (hp : ∀ x, fibre key w (P x) = (pencil t)^[d] (fibre key w x))
    (hf : ∀ v, fw v ∘ key = changeBasis half hh (v ∘ key))
    (hb : ∀ v, bw v ∘ key = (changeBasis half hh).symm (v ∘ key))
    (ht : ∀ a, tag (key a) = addressSign a) (x : Bank R L X V) :
    fibre key w (schedule t half tag fw bw P x) = run t d half hh (fibre key w x) := by
  have hc (out : Bool) (a b : Bank R L X U) :
      fibre key w (sweep bw (applyTag t tag out (sweep fw a) (sweep fw b))) =
        correction t half hh out (fibre key w a) (fibre key w b) := by
    funext u
    change bw _ ∘ key = (changeBasis half hh).symm _
    rw [hb]
    apply congrArg (changeBasis half hh).symm
    funext z
    have h (y : Bank R L X U) : sweep fw y w (key z) = observe half hh z (fibre key w y) :=
      funext fun i => congrFun (hf (fun a => y w a i)) z
    simp only [Function.comp_apply,applyTag,ht,h]
  let px := P x
  let px' := (pencil t)^[d] (fibre key w x)
  let a := gather t.extract px
  let b := gather t.extract x
  let v := sweep bw (applyTag t tag false (sweep fw a) (sweep fw b))
  let q := sweep bw (applyTag t tag true (sweep fw a) (sweep fw b))
  change fibre key w (px - half • (P (P px) - px) - P (gather t.restore v) + gather t.restore q) = _
  change fibre key w px - half • (fibre key w (P (P px)) - fibre key w px) -
    fibre key w (P (gather t.restore v)) + fibre key w (gather t.restore q) = _
  simp only [v,q,a,b,px,hp,gather_fibre,hc,run]

open IntegerMultiplication IntegerMultiplication.Port IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Loom
  InterchangeSlots InterchangeSpectralFibre Support RectangleAtlas Interchange.StageScript

variable {B H : Type} [DecidableEq L] [Fintype L] [Fintype B] [Fintype H]
  {r : B → Rectangle L} {a b : ℕ} [NeZero b] {A : RectangleAtlas r a}

/-- Literals, compiled moves, and the native spectral passes on one actual frame. -/
def native (F : Frame A m b) (I J : H → L) (M : Matrix H H R)
    (t : Spec R V U m) (d : ℕ) (half : R) (P G S : Tape) (f : ℕ) :
    Bank R L (Keys P G S (Fin (a+m+a)) (Block b f)) V →
      Bank R L (Keys P G S (Fin (a+m+a)) (Block b f)) V :=
  let s := RepairSchedule.mainSlots a m
  let axes := (List.finRange m).map s
  let g := extendLayout P G S (F.layout f)
  schedule t half (fun x j => decide ((numerical x (s j)).2 < (numerical x (s j)).1))
    (fun x => axes.foldl (fun v j => InterchangeSpectralRequest.advance false half j v) x)
    (fun x => axes.reverse.foldl (fun v j => InterchangeSpectralRequest.advance true half j v) x)
    ((eval g.perm (stageBank r I J t M))^[d])

theorem native_correct [DecidableEq V] [DecidableEq R] (F : Frame A m b) (I J : H → L)
    (M : Matrix H H R) (hM : (rectangleMatrix (K := R) r).submatrix id J * M *
      (rectangleMatrix r).submatrix I id = rectangleMatrix r)
    (t : Spec R V U m) (d : ℕ) (half : R) (hh : 2*half=1) (ht : accepts t d half = true)
    (P G S : Tape) (f : ℕ) (x : Bank R L (Keys P G S (Fin (a+m+a)) (Block b f)) V)
    (w : L) (i : V) (u : Keys P G S (Fin (a+m+a)) (Block b f)) :
    native F I J M t d half P G S f x w u i = x w (swapMain (RepairSchedule.mainSlots a m) u) i := by
  let s := RepairSchedule.mainSlots a m
  let k := key s (numerical u) u.1 u.2.2.1 u.2.2.2.2
  let z := numerical u ∘ s
  have hs : k z = u := key_self s u
  let g := extendLayout P G S (F.layout f)
  have hp (j : Fin m) (v : L) (z : Address (Fin m) (Fin (b^f))) :
      (g.S j v).symm (g.T j v (k z)) = k (swap j z) :=
    (F.native_pull j v P G S f (k z)).trans (key_swap s _ _ _ _ z j).symm
  let tag' (y : Keys P G S (Fin (a+m+a)) (Block b f)) (j : Fin m) :=
    decide ((numerical y (s j)).2 < (numerical y (s j)).1)
  have ht' (z' : Address (Fin m) (Fin (b^f))) : tag' (k z') = addressSign z' := by
    funext j
    simp [tag',k,key,numerical,InterchangeSpectralRequest.key,addressSign]
  have h := schedule_on_fibre t d half hh tag' _ _ _ k w
    (fun y => stageBank_iterate r I J t M hM g k hp y w d)
    (forward_key s _ _ _ _ half hh (List.finRange m))
    (inverse_key s _ _ _ _ half hh (List.finRange m)) ht' x
  have hout := congrFun (congrFun h i) z
  change native F I J M t d half P G S f x w (k z) i = run t d half hh (fibre k w x) i z at hout
  rw [run_correct _ _ _ hh ht] at hout
  have hz := key_swapAll s (numerical u) u.1 u.2.2.1 u.2.2.2.2 z
  change k (SwapRepair.swapAll z) = swapMain s (k z) at hz
  simpa only [fibre,hs,hz] using hout

end InterchangeROMRepair.Physical

end

end NearSquareRoot
end Computability
end OAI
