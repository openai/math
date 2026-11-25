import OAI.Computability.NearSquareRoot.KernelEffectiveFamilyMapping
import OAI.Computability.NearSquareRoot.ScheduleRegisterSelect
import OAI.Computability.NearSquareRoot.ScheduleRegisterAlignEffectiveTask
import OAI.Computability.IntegerMultiplication.Strip.Cars

/-! # A named program for mapping an arbitrary compiled row command over a strip -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace NamedLiftoff
open IntegerMultiplication Code Code.Task Strip CommonRegisters GeneratorSyntax KernelEffectiveFamily

def rowMap (c : Cmd) : Cmd := .tie (mapBody c)

theorem within {R : ℕ} {c : Cmd} (hc : Within R c) :
    Within (max 3 R) (rowMap c) :=
  mapBody_within (Nat.le_max_left ..) (RegisterSelect.within_mono (Nat.le_max_right ..) _ hc)

theorem effective {P : Type} [Primcodable P] (c : P → Cmd) (hc : Effective ltr c) :
    Effective ltr (fun p => rowMap (c p)) := (mapBody_effective c hc).tie

/-- The tagged element type may depend on the strip. Its computation weight
need only cover the row and its serialized input, uniformly within one strip. -/
theorem runs {J : Type} {A : J → Type} (s : ∀ i, Series (A i)) (v u : ∀ i, A i → Tree)
    (w : J → ℝ) (hw : ∀ i, 1 ≤ w i)
    (vol : Volume (fun x : Sigma A => w x.1) (fun x => v x.1 x.2))
    {c : Cmd} (hc : EffectiveTask.Runs c (fun x : Sigma A => ⌈w x.1⌉₊)
      (fun x => v x.1 x.2) (fun x => u x.1 x.2)) :
    EffectiveTask.Runs (rowMap c) (fun i => ⌈((s i).count : ℝ)*w i+1⌉₊)
      (stackRun s v) (stackRun s u) := by
  obtain ⟨C,hc⟩ := hc
  let K := C+100
  have loop (i : J) (l : List (A i)) (env : Env) (r : Deck) :
      Fits (mapBody c :: env) (mapBody c) (pile 0 (forest (v i) l) r) (pile 0 (forest (u i) l) r)
        (K*((forest (v i) l).count+l.length*(⌈w i⌉₊+1))) := by
    let G := mapBody c :: env
    induction l generalizing r with
    | nil =>
      apply (fits_bit (b := false) (c := fun _ => give 0 false) (fits_give false r 0 G)).mono
      simp [forest_nil,Tree.count,K]
    | cons x xs ih =>
      let xt := v i x
      let tl := forest (v i) xs
      let ys := forest (u i) xs
      have save := fits_move (i:=0) (u:=2) (j:=1) (by decide) (by decide) xt G (pile 0 tl r)
      rw [pile_comm 1 _ r 0 tl (by decide)] at save
      have sub := Fits.again0 (ih (pile 1 xt r))
      have back := fits_move (i:=1) (u:=2) (j:=0) (by decide) (by decide) xt G (pile 0 ys r)
      rw [pile_comm 1 _ r 0 ys (by decide)] at back
      have act := hc ⟨i,x⟩ G (pile 0 ys r)
      have pair := fits_pack (u i x) ys r 0 G
      apply (fits_pair (save.join (sub.join (back.join (act.join pair))))).mono
      simp only [xt,K,forest_cons,Tree.count,List.length_cons,Nat.add_mul,Nat.mul_add,
        Nat.mul_one,Nat.one_mul]
      omega
  obtain ⟨B,vb⟩ := stripe_volume s v w vol hw
  let a (i : J) := (stackRun s v i).count + (s i).count*(⌈w i⌉₊+1)
  have raw : EffectiveTask.Runs (rowMap c) a (stackRun s v) (stackRun s u) := by
    refine ⟨K+1,fun i env r => ?_⟩
    have tr := (loop i (s i).explore env r).tie
    simp only [rowMap,a,stackRun,stripe_simple,Series.count]
    apply tr.mono
    simp only [Nat.add_mul,Nat.mul_add,Nat.one_mul,Nat.mul_one]
    omega
  apply raw.bound (B+4)
  intro i
  have ceil := Nat.ceil_lt_add_one (show 0 ≤ w i by linarith [hw i])
  have cq : (⌈w i⌉₊ : ℝ)+1 ≤ 3*w i := by linarith [hw i]
  have hcount := mul_le_mul_of_nonneg_left cq (Nat.cast_nonneg (s i).count (α := ℝ))
  have budget := Nat.le_ceil ((↑(s i).count : ℝ)*w i+1)
  have total : ((a i + 1 : ℕ) : ℝ) ≤ ((B+4 : ℕ) : ℝ)*(⌈((s i).count : ℝ)*w i+1⌉₊+1 : ℕ) := by
    dsimp only [a,stackRun]
    push_cast
    nlinarith [vb i,mul_le_mul_of_nonneg_left budget (Nat.cast_nonneg B (α := ℝ))]
  exact_mod_cast total

end NamedLiftoff

end NearSquareRoot
end Computability
end OAI
