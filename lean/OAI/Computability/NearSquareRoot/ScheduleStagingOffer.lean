import OAI.Computability.NearSquareRoot.ScheduleStagingCopy
import OAI.Computability.NearSquareRoot.ScheduleStagingPorts

/-!
# Giving a staged request to the public multiplier

The controller's request register becomes the translated public output tape.
The public input is on the private bank's first tape. The copy leaves every
other tape untouched, including the absolute fence and origin markers.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace StagingOffer

open IntegerMultiplication TM CommonAlphabet CommonAlphabet.Pipeline StagingPorts

variable {X J I : Type}

/-- A common delimiter and bit alphabet for filing and offering the raw request. -/
def alphabet [DecidableEq X] (e : Encoding X) (sentinel : X) (hm : ∀ a, sentinel ≠ e.embed a) :
    StagingCopy.Alphabet X :=
  let he : Function.Injective e.embed := Function.LeftInverse.injective e.decode
  let h : Function.Injective (fun a : Option Bool => e.embed (some a)) :=
    fun _ _ eq => Option.some.inj (he eq)
  StagingCopy.Alphabet.ofEncoders (e.embed none) sentinel _ _ h h (hm none)
    (by intro a eq; cases he eq) (by intro a eq; cases he eq)
    (fun a => hm (some a))

def queryTape (e : Encoding X) (u : ℕ) (x y : List Bool) : Tape X :=
  StagingCopy.atPos (e.embed none) (-(2*u+1 : ℤ))
    ((StagingCopy.word x y).map fun a => e.embed (some a))

def replyTape (e : Encoding X) (u : ℕ) : Tape X := StagingCopy.atPos (e.embed none) (-(2*u : ℤ)) []

def blankBank (e : Encoding X) : Option I → Tape X := fun _ => Tape.loaded (e.embed none) []

private def bankData (e : Encoding X) (input : Tape X) : Option I → Tape X
  | none => input
  | some _ => Tape.loaded (e.embed none) []

def privateBankInput (e : Encoding X) (x y : List Bool) : Option I → Tape X :=
  bankData e (Tape.loaded (e.embed none) ((rawWord x y).map e.embed))

@[simp] theorem encoded_word (e : Encoding X) (x y : List Bool) :
    (StagingCopy.word x y).map (fun a => e.embed (some a)) = (rawWord x y).map e.embed := by
  simp [StagingCopy.word,rawWord,Public.bit,Public.sep,List.map_map,Function.comp_def]

theorem privateBankInput_active (e : Encoding X) (x y : List Bool) :
    privateBankInput (I:=I) e x y =
      active e (publicLoad x y) := by
  funext j
  cases j with
  | none => exact (image_loaded e.embed none (rawWord x y) 0).symm
  | some _ => exact (image_loaded e.embed none [] 0).symm

theorem replyTape_image (e : Encoding X) (u : ℕ) :
    replyTape e u = imageTape e.embed (-(2*u : ℤ)) (Tape.loaded none []) :=
  (image_loaded e.embed none [] _).symm

/-- The offer's returned bank is the literal input configuration of the public
digit call, with its output translated to the future product's register top. -/
theorem output_eq_call [DecidableEq J] (one : J) (e : Encoding X) (R u : ℕ)
    (shelf : J → Tape X) (x y : List Bool) :
    marked R (Function.update shelf one (replyTape e u)) (privateBankInput (I:=I) e x y) =
    marked R (Function.update shelf one (imageTape e.embed (-(2*u : ℤ)) (Tape.loaded none [])))
      (active e (publicLoad x y)) := by rw [replyTape_image,privateBankInput_active]

def rule [DecidableEq J] [DecidableEq X] (one : J) (e : Encoding X) (sentinel : X)
    (hm : ∀ a, sentinel ≠ e.embed a) :
    Rule (StagingReset.Symbol X) StagingCopy.Phase (Bank J I) :=
  StagingBank.rule (copyRoute one) (markTrack id id) (StagingCopy.rule (alphabet e sentinel hm))

private def localFrame (R : ℕ) : StagingBank.Frame (markTrack (X:=X) id id) Bool :=
  frame id id (fun _ => rfl) R (fun _ => 0)

private theorem frame_id (R : ℕ) (i : Bool) (t : Tape X) :
    StagingBank.tape (localFrame R) i t = StagingReset.markedTape R t := by
  rw [localFrame,frame_tape]
  cases t
  simp [imageTape]

private theorem place [DecidableEq J] (one : J) (e : Encoding X) (R : ℕ)
    (shelf : J → Tape X) (q : StagingCopy.Phase) (src dst : Tape X) :
    StagingBank.parked (copyRoute one) (localFrame R) (marked R shelf (blankBank (I:=I) e))
      (StagingCopy.cfg q src dst) =
    ⟨q,marked R (Function.update shelf one src) (bankData e dst)⟩ := by
  unfold StagingBank.parked
  rw [Config.mk.injEq]
  refine ⟨rfl,funext fun j => ?_⟩
  rcases j with j|(_|j)
  · by_cases eq : j=one
    · subst j
      simp [Route.put,copyRoute,StagingBank.config,
        StagingCopy.cfg,StagingCopy.both,frame_id,marked,split]
    · simp [Route.put,copyRoute,eq,marked,split]
  · simp [Route.put,copyRoute,StagingBank.config,StagingCopy.cfg,
      StagingCopy.both,frame_id,marked,split,bankData]
  · rfl

/-- A physical, halted offer of two literal MSF operands to the digit core. -/
theorem run [DecidableEq J] [DecidableEq X] (one : J) (e : Encoding X) (sentinel : X)
    (hm : ∀ a, sentinel ≠ e.embed a) (shelf : J → Tape X)
    {x y : List Bool} {u R : ℕ} (hx : x.length=u) (hy : y.length=u)
    (hquery : shelf one = queryTape e u x y) (hR : 6*u+7 ≤ R)
    (hshelf : ∀ j, -(R:ℤ) ≤ (shelf j).pos ∧ (shelf j).pos ≤ R) :
    let m := rule (I:=I) one e sentinel hm
    let endTapes := marked R (Function.update shelf one (replyTape e u)) (privateBankInput e x y)
    FencedRun m (fun _ => -(R:ℤ)) (fun _ => (R:ℤ))
      ⟨.start,marked R shelf (blankBank e)⟩ (4*u+6) ⟨.done,endTapes⟩ ∧
    advance m ⟨.done,endTapes⟩ = none := by
  let a := alphabet e sentinel hm
  let m := StagingCopy.rule a
  let r := copyRoute (I:=I) one
  let f := localFrame (X:=X) R
  let s := marked R shelf (blankBank (I:=I) e)
  let initial := StagingCopy.cfg .start (queryTape e u x y) (Tape.loaded (e.embed none) [])
  let doneCfg := StagingCopy.cfg .done (replyTape e u)
    (Tape.loaded (e.embed none) ((rawWord x y).map e.embed))
  have localRun : Trace (advance m) initial (4*u+6) doneCfg := by
    have h := StagingCopy.copy_request_equal_width a hx hy
    change Trace _ initial _ (StagingCopy.cfg .done (replyTape e u) (Tape.loaded (e.embed none)
      ((StagingCopy.word x y).map fun v => e.embed (some v)))) at h
    rwa [encoded_word] at h
  have enter : StagingBank.parked r f s initial = ⟨.start,marked R shelf (blankBank e)⟩ := by
    rw [show StagingBank.parked r f s initial = _ from place (I:=I) one e R shelf ..]
    rw [← hquery,Function.update_eq_self]
    congr 2
    funext j
    cases j <;> rfl
  have finish : StagingBank.parked r f s doneCfg =
      ⟨.done,marked R (Function.update shelf one (replyTape e u)) (privateBankInput e x y)⟩ :=
    place one e R shelf ..
  dsimp only
  rw [← enter,← finish]
  refine ⟨⟨StagingBank.run r _ f s m localRun,?_⟩,StagingBank.halt r _ f s m (by rfl)⟩
  intro k hk z hz j
  obtain ⟨c,first,_⟩ := trace_split localRun hk
  have eq := trace_endpoint_unique hz (StagingBank.run r _ f s m first)
  subst z
  have inside (b : Bool) :
      -(R:ℤ) ≤ ((StagingBank.parked r f s c).tape (r.index b)).pos ∧
      ((StagingBank.parked r f s c).tape (r.index b)).pos ≤ R := by
    rw [StagingBank.inside]
    change -(R:ℤ) ≤ 0+(c.tape b).pos ∧ 0+(c.tape b).pos ≤ R
    have he := head_excursion first b
    cases b <;> simp [initial,StagingCopy.cfg,StagingCopy.both,queryTape,StagingCopy.atPos,
      Tape.loaded] at he <;> omega
  rcases j with j|(_|j)
  · by_cases h : j = one
    · subst j
      exact inside false
    · rw [StagingBank.off r f s c (.inl j) (by
        rintro ⟨b,hb⟩
        cases b with
        | false => change Sum.inl one = Sum.inl j at hb; exact h (Sum.inl.inj hb).symm
        | true => change Sum.inr none = Sum.inl j at hb; cases hb)]
      exact hshelf j
  · exact inside true
  · rw [StagingBank.off r f s c (.inr (some j)) (by
      rintro ⟨b,hb⟩
      cases b with
      | false => change Sum.inl one = Sum.inr (some j) at hb; cases hb
      | true => change Sum.inr none = Sum.inr (some j) at hb; cases hb)]
    change -(R:ℤ) ≤ 0 ∧ (0:ℤ) ≤ R
    omega

end StagingOffer

end NearSquareRoot
end Computability
end OAI
