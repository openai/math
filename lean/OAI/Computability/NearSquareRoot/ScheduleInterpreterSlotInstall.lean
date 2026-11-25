import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotInstallCells
import OAI.Computability.NearSquareRoot.ScheduleInterpreterSlotInstallPhase
import OAI.Computability.NearSquareRoot.InterchangeSplitCompose

/-!
# Installing a symmetric fence on every raw tape

The first outward pass reads the input and marks its first trailing blank on
every tape. In each of the next two passes a different head measures that
distance by scanning to its right marker while all other heads move left.
Both passes rewind to the temporary origin stamps. The final tick at the
origin erases the stamps, leaving just the two endpoints and the original data.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Uniform.SlotInstall
open IntegerMultiplication TM
variable {A I : Type} [DecidableEq I]

private def along (reference : I) (j : I) := decide (j=reference)

private def right (inp : I) [DecidableEq A] (blank : A) : Rule (Fence.Symbol A) Bool I :=
  InstallPass.rule (fun _ => true) inp (fun c => decide (c.1=blank)) atOrigin (fun _ => writeRight)

private def left (reference : I) : Rule (Fence.Symbol A) Bool I :=
  InstallPass.rule (along reference) reference rightEnd atOrigin (writeLeft reference)

omit [DecidableEq I] in
private theorem atHome {P : Type} (sign : I → Bool) (f : I → ℤ → P) (s : Bool) :
    InstallPass.layout sign f 0 s = base s f := by
  apply congrArg (Config.mk s)
  funext j
  exact InstallPass.layout_zero_tape sign f s j

omit [DecidableEq I] in
private theorem right_marks (f : I → ℤ → A) (L : ℕ) (hL : 0 < L) :
    InstallPass.mark (fun _ => true) (paint f L true false (fun _ => false)) L (fun _ => writeRight) =
      paint f L true true (fun _ => false) := by
  funext j p
  by_cases h : p = (L : ℤ)
  · subst p
    simp [InstallPass.mark,InstallPass.gaugePos,paint,writeRight,hL.ne']
  · simp [InstallPass.mark,InstallPass.gaugePos,paint,h]

private theorem left_marks (f : I → ℤ → A) (L : ℕ) (g : I) (old : I → Bool) :
    InstallPass.mark (along g) (paint f L true true old) L (writeLeft g) =
      paint f L true true (fun j => decide (j ≠ g) || old j) := by
  funext j p
  by_cases hj : j=g
  · subst j
    by_cases hp : p=(L:ℤ) <;> simp [InstallPass.mark,InstallPass.gaugePos,along,writeLeft,paint,hp]
  · by_cases hp : p= -(L:ℤ)
    · subst p
      simp [InstallPass.mark,InstallPass.gaugePos,along,writeLeft,paint,hj]
    · simp [InstallPass.mark,InstallPass.gaugePos,along,writeLeft,paint,hj,hp]

omit [DecidableEq I] in
private theorem sense (f : I → ℤ → A) (L : ℕ) (hL : 0<L) (old : I → Bool)
    (j : I) (k : ℕ) :
    rightEnd (paint f L true true old j (k:ℤ)) = decide (k=L) := by
  have hn : (k:ℤ) ≠ -(L:ℤ) := by omega
  by_cases hk : k=0
  · subst k
    simp [rightEnd,paint,hL.ne',Ne.symm hL.ne']
  · simp [rightEnd,paint,hk,hn]

omit [DecidableEq I] in
private theorem home (f : I → ℤ → A) (L : ℕ) (hL : 0<L) (old : I → Bool)
    (j : I) (k : ℕ) :
    atOrigin (paint f L true true old j (k:ℤ)) = decide (k=0) := by
  have hn : (k:ℤ) ≠ -(L:ℤ) := by omega
  by_cases hk : k=0 <;> simp [atOrigin,paint,hk,hn]

private theorem first_run [DecidableEq A] (inp : I) (blank : A) (s : List A) (hL : 0<s.length)
    (hn : blank∉s) :
    let f := fun j => (loaded inp blank s j).view
    let bare := paint f s.length true false (fun _ => false)
    let r := paint f s.length true true (fun _ => false)
    Trace (advance (right inp blank)) (base false bare) (2*s.length+1) (base true r) ∧
      advance (right inp blank) (base true r) = none := by
  let f := fun j => (loaded inp blank s j).view
  have h := InstallPass.run (fun _ : I => true) inp (fun c : Fence.Symbol A => decide (c.1=blank))
    atOrigin (fun _ => writeRight) (paint f s.length true false (fun _ => false)) s.length
  rw [right_marks f s.length hL] at h
  have run := h (fun k hk => by
    simp [InstallPass.gaugePos,paint,f,read_nonblank inp blank s hn hk]) (by
    simp [InstallPass.gaugePos,paint,f,read_end]) (fun k hk _ => by
    simp [InstallPass.gaugePos,home f _ hL,hk.ne']) (by
    simp [InstallPass.gaugePos,atOrigin,paint])
  simpa only [atHome,right,f] using run

private theorem second_run (g : I) (f : I → ℤ → A) (L : ℕ) (hL : 0<L) (old : I → Bool) :
    let before := paint f L true true old
    let after := paint f L true true (fun j => decide (j≠g) || old j)
    Trace (advance (left g)) (base false before) (2*L+1) (base true after) ∧
      advance (left g) (base true after) = none := by
  have h := InstallPass.run (along g) g rightEnd atOrigin (writeLeft g) (paint f L true true old) L
  rw [left_marks f L g old] at h
  have run := h (fun k hk => by
    simp [along,InstallPass.gaugePos,sense f L hL,hk.ne]) (by
    simp [along,InstallPass.gaugePos,sense f L hL]) (fun k hk _ => by
    simp [along,InstallPass.gaugePos,home f L hL,hk.ne']) (by
    simp [along,InstallPass.gaugePos,atOrigin,paint])
  simpa only [atHome,left] using run

abbrev PC := Bool ⊕ (Bool ⊕ (Bool ⊕ (Bool ⊕ Bool)))

def start : PC := .inl false

def done : PC := .inr (.inr (.inr (.inr true)))

def rule [DecidableEq A] (inp aux : I) (blank : A) : Rule (Fence.Symbol A) PC I :=
  TapeSequence.rule (originRule true)
    (TapeSequence.rule (right inp blank)
      (TapeSequence.rule (left aux)
        (TapeSequence.rule (left inp) (originRule false) false) (.inl false)) (.inl false)) (.inl false)

/-- All tapes, including the literal input, acquire symmetric fence flags.
Only the input length is used. Each outward pass and rewind has a physical
transition count, and the four changes of program are included. -/
theorem install [DecidableEq A] (inp aux : I) (blank : A) (s : List A) (distinct : inp ≠ aux)
    (hL : 0 < s.length) (hn : blank ∉ s) :
    let last : Config (Fence.Symbol A) PC I :=
      ⟨done,fun j => Fence.markedTape (-(s.length : ℤ)) s.length (loaded inp blank s j)⟩
    Trace (advance (rule inp aux blank)) ⟨start,plain inp blank s⟩ (6*s.length+9) last ∧
      advance (rule inp aux blank) last = none := by
  let f := fun j => (loaded inp blank s j).view
  let L := s.length
  let m : I → Bool := fun _ => false
  let a : I → Bool := fun j => decide (j≠aux) || m j
  have filled : (fun j => decide (j≠inp) || a j) = (fun _ => true) := by
    funext j
    by_cases h : j=inp
    · subst j; simp [a,distinct]
    · simp [h]
  have openRun := origin_run f L hL true false false m
  obtain ⟨r,h₁⟩ := first_run inp blank s hL hn
  obtain ⟨l,h₂⟩ := second_run aux f L hL m
  obtain ⟨g,h₃⟩ := second_run inp f L hL a
  rw [filled] at g h₃
  have closeRun := origin_run f L hL false true true (fun _ => true)
  have t₄ := TapeSequence.run _ _ false g h₃ closeRun (origin_halt false _)
  have t₃ := TapeSequence.run _ _ (.inl false) l h₂ t₄.1 t₄.2
  have t₂ := TapeSequence.run _ _ (.inl false) r h₁ t₃.1 t₃.2
  have full := TapeSequence.run _ _ (.inl false) openRun (origin_halt true _) t₂.1 t₂.2
  have time : 1+1+((2*L+1)+1+((2*L+1)+1+((2*L+1)+1+1)))=6*L+9 := by omega
  rw [time] at full
  rw [plain_eq inp blank s start,←marked_eq inp blank s done]
  exact full

end Uniform.SlotInstall

end NearSquareRoot
end Computability
end OAI
