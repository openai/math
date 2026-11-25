import OAI.Computability.NearSquareRoot.PhysicalWalshCompileSwapLiteral
import OAI.Computability.NearSquareRoot.FixedCandidateEffectiveTask
import OAI.Computability.NearSquareRoot.PhysicalWalshOpen

/-! # Named ruler emitters for the three high-field interchange stages -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace PhysicalWalshCompileSwapKeys
open IntegerMultiplication Code Space PhysicalWalsh PhysicalWalshNode PhysicalWalshCompileSwapRulers
open CommonRegisters GeneratorSyntax

def KeyRuns {Z : Type} [Codec Z] (f : World → Z) (d : ℕ) (c : Control → Cmd) : Prop :=
  ∀ (a W : ℕ) (i j : Fin (a+1)), i ≠ j → ∀ D, let S := fun t : XorInput W => allowance (a+1) d t.shape
    ClosedRuns (c (a+1,W,i.val,j.val,D)) S S
      (fun t => send (Header.wire (a+1) t.shape)) (fun t => send (f ⟨a,W,i,j,D,t.shape⟩))

private theorem ofConfigured {Z : Type} [Codec Z] {f : World → Z} {d : ℕ} {c : Control → Cmd}
    (h : Configured f (size ∘ f) d c) (e : ℕ) (one : 1 ≤ e) (le : d ≤ e)
    (cap : ∀ (a W : ℕ) (i j : Fin (a+1)), i ≠ j → ∀ D (t : XorInput W),
      size (f ⟨a,W,i,j,D,t.shape⟩) ≤ 20*(allowance (a+1) e t.shape+1)) :
    KeyRuns f e c := by
  intro a W i j ne D S
  obtain ⟨C,hc⟩ := h a W i j D
  let z (t : XorInput W) : World := ⟨a,W,i,j,D,t.shape⟩
  have hpow (t : XorInput W) {n : ℕ} (he : n ≤ e) : (Header.scale (a+1) t.shape+1)^n ≤ S t :=
    (Nat.pow_le_pow_right (Nat.succ_pos _) he).trans (Nat.le_add_left ..)
  have clock : ∃ K, ∀ (t : XorInput W) env, Fits.value env (c (a+1,W,i.val,j.val,D)) 0
      (send (Header.wire (a+1) t.shape)) (send (f (z t))) (K*(S t+1)) := by
    refine ⟨C*21,fun t env r => (hc t.shape env r).mono ?_⟩
    rw [Nat.mul_assoc]
    apply Nat.mul_le_mul_left
    have q := hpow t le
    have out := cap a W i j ne D t
    change size (f (z t)) ≤ 20*(S t+1) at out
    change _+size (f (z t)) ≤ _
    omega
  exact (EffectiveBoundedTask.Runs.of_time clock).bound 1 2 (fun _ => by simp) (fun t => by
    have q := hpow t one
    rw [pow_one] at q
    change Header.scale (a+1) t.shape+S t+1 ≤ 2*(S t+1)
    omega)

open private header_sizes from OAI.Computability.NearSquareRoot.PhysicalWalshSwapRulers

def setGrade (g : World → ℕ) (t : World) : World := {t with depth := g t}

/-- Choose the three emitted programs and one degree before fixing a shape,
a slot pair, or the degree used for the low-bit reserve. -/
theorem compileAt (g : World → ℕ)
    (pm : Mint regime (packHeader ∘ setGrade g))
    (rm : Mint regime (rectHeader ∘ setGrade g))
    (um : Mint regime (unpackHeader ∘ setGrade g)) : ∃ (pk rc up : Control → Cmd) (d R : ℕ), Effective ltr pk ∧ Effective ltr rc ∧ Effective ltr up ∧
    (∀ k, Within R (pk k) ∧ Within R (rc k) ∧ Within R (up k)) ∧ 1 ≤ d ∧
    KeyRuns (packHeader ∘ setGrade g) d pk ∧ KeyRuns (rectHeader ∘ setGrade g) d rc ∧ KeyRuns (unpackHeader ∘ setGrade g) d up := by
  obtain ⟨Rp,dp,pk,hp,ep,rp,cp⟩ := configuredMint pm
  obtain ⟨Rr,dr,rc,_,er,rr,cr⟩ := configuredMint rm
  obtain ⟨Ru,du,up,_,eu,ru,cu⟩ := configuredMint um
  let d := max dp (max dr du)
  have pd : dp ≤ d := le_max_left ..
  have rd : dr ≤ d := (le_max_left ..).trans (le_max_right ..)
  have ud : du ≤ d := (le_max_right ..).trans (le_max_right ..)
  let R := max Rp (max Rr Ru)
  have pR : Rp ≤ R := le_max_left ..
  have rR : Rr ≤ R := (le_max_left ..).trans (le_max_right ..)
  have uR : Ru ≤ R := (le_max_right ..).trans (le_max_right ..)
  have hd := hp.trans pd
  refine ⟨pk,rc,up,d,R,ep,er,eu,fun k => ⟨RegisterSelect.within_mono pR _ (rp k),
    RegisterSelect.within_mono rR _ (rr k),RegisterSelect.within_mono uR _ (ru k)⟩,hd,
    ofConfigured cp d hd pd ?_,ofConfigured cr d hd rd ?_,ofConfigured cu d hd ud ?_⟩
  · intro a W i j ne D t
    let E := g ⟨a,W,i,j,D,t.shape⟩
    have := (header_sizes E W i j ne t.shape t.positive d).1
    change size (SlotSwap.Rulers.packHeader E W i j t.shape) ≤ _
    omega
  · intro a W i j ne D t
    let E := g ⟨a,W,i,j,D,t.shape⟩
    have := SlotSwap.header_le (W:=W) i j ne t.shape t.positive (SlotSwap.reserve E _ t.shape) (min_le_left ..)
    have ineq : (Header.scale (a+1) t.shape+1)^1 ≤ allowance (a+1) d t.shape :=
      (Nat.pow_le_pow_right (Nat.succ_pos _) hd).trans (Nat.le_add_left ..)
    rw [pow_one] at ineq
    change size (SlotSwap.geometry W i j t.shape (SlotSwap.reserve E (a+1) t.shape)).header ≤ _
    omega
  · intro a W i j ne D t
    let E := g ⟨a,W,i,j,D,t.shape⟩
    have := (header_sizes E W i j ne t.shape t.positive d).2
    change size (SlotSwap.Rulers.unpackHeader E W i j t.shape) ≤ _
    omega

end PhysicalWalshCompileSwapKeys

end NearSquareRoot
end Computability
end OAI
