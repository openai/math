import OAI.Computability.NearSquareRoot.KernelEffectiveFamily
import OAI.Computability.NearSquareRoot.ScheduleRegisterLoom
import OAI.Computability.IntegerMultiplication.Code.Slice

/-! # Effective mapping over a runtime list

One call to a compiled action processes each element. The element is parked on
register one while its tail is processed and returns to register zero before
the action runs. The total shuttle distance is linear in the input size.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelEffectiveFamily
open IntegerMultiplication Code CommonRegisters GeneratorSyntax RegisterWitness

def mapBody (c : Cmd) := splitRoot 0 (fun _ => give 0 false)
  ((move 0 1 2).join ((.again 0 : Cmd).join ((move 1 0 2).join (c.join (pack 0)))))

theorem mapBody_within {R : ℕ} (hR : 3 ≤ R) {c : Cmd} (hc : Within R c) :
    Within R (mapBody c) := by
  have h1 : 0 < R := by omega
  exact splitRoot_within.mpr ⟨h1,h1,h1,
    LoomRegisters.move_within (by omega) (by omega) (by omega), trivial,
    LoomRegisters.move_within (by omega) (by omega) (by omega), hc, h1⟩

theorem mapBody_effective {P : Type} [Primcodable P] (c : P → Cmd) (h : Effective ltr c) :
    Effective ltr (fun p => mapBody (c p)) := by
  apply effective_look _ (Computable.const _)
  intro t
  apply (effective_const ltr (.pop 0)).join
  rcases t with _|(_|_|_)
  all_goals first
    | exact effective_const ltr _
    | exact (effective_const (X := P) ltr _).join ((effective_const ltr _).join
        ((effective_const ltr _).join (h.join (effective_const ltr _))))

private theorem map_runs {X Y : Type} [Codec X] [Codec Y] {c : Cmd} {f : X → Y}
    (h : Runs c f) : Runs (.tie (mapBody c)) (List.map f) := by
  obtain ⟨C,hc⟩ := h
  let K := C+100
  have body (l : List X) (env : Env) (r : Deck) :
      Fits (mapBody c :: env) (mapBody c) (pile 0 (send l) r) (pile 0 (send (l.map f)) r) (K*size l) := by
    let G := mapBody c :: env
    induction l generalizing r with
    | nil =>
      apply (fits_bit (b := false) (c := fun _ => give 0 false) (fits_give false r 0 G)).mono
      simp [K]
    | cons x xs ih =>
      let xt := send x
      let tl := send xs
      let ans := send (xs.map f)
      have save := fits_move (i:=0) (u:=2) (j:=1) (by decide) (by decide) xt G (pile 0 tl r)
      rw [pile_comm 1 _ r 0 tl (by decide)] at save
      have sub := Fits.again0 (ih (pile 1 xt r))
      have back := fits_move (i:=1) (u:=2) (j:=0) (by decide) (by decide) xt G (pile 0 ans r)
      rw [pile_comm 1 _ r 0 ans (by decide)] at back
      have act := hc x G (pile 0 ans r)
      have pair := fits_pack (send (f x)) ans r 0 G
      apply (fits_pair (save.join (sub.join (back.join (act.join pair))))).mono
      change 42*size x + (_ + (42*size x + (C*(size x+1)+1+2)+2)+2)+2+4 ≤ _
      simp only [K,size_cons,Nat.add_mul,Nat.mul_add,Nat.mul_one]
      omega
  refine ⟨K+1,fun l env r => ((body l env r).tie).mono ?_⟩
  simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
  omega

/-- Mapping a uniformly generated family preserves its register cutoff, the
linear contract, and computability of its entire P192 source file. -/
theorem Family.mapping {P X Y : Type} [Primcodable P] [Codec X] [Codec Y] {R : ℕ}
    {f : P → X → Y} (hR : 4 ≤ R) (h : Family R f) :
    Family R (fun p => List.map (f p)) := by
  obtain ⟨c,he,hc⟩ := h
  exact ⟨fun p => .tie (mapBody (c p)),(mapBody_effective c he).tie,
    fun p => ⟨mapBody_within (by omega) (hc p).1,map_runs (hc p).2⟩⟩

end KernelEffectiveFamily

end NearSquareRoot
end Computability
end OAI
