import OAI.Computability.NearSquareRoot.KernelEffectiveFamily

/-! # Product constructors for effective linear commands -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace KernelEffectiveFamily

open IntegerMultiplication Code CommonRegisters GeneratorSyntax

variable {P X Y Z : Type} [Primcodable P] [Codec X] [Codec Y] [Codec Z] {R : ℕ}

theorem effective_splitRoot {atom : Bool → P → Cmd} {node : P → Cmd} (i : ℕ)
    (ha : ∀ b, Effective ltr (atom b)) (hn : Effective ltr node) :
    Effective ltr (fun p => splitRoot i (fun b => atom b p) (node p)) := by
  apply effective_look ltr (Computable.const i)
  intro a
  apply Effective.join (effective_const ltr (.pop i))
  cases a with
  | none => exact effective_const ltr .pass
  | some c => cases c with
    | bit b => exact ha b
    | node => exact hn
    | _ => exact effective_const ltr .pass

def leftCmd (c : Cmd) := splitRoot 0 (fun _ => .pass) (c.join (pack 0))

def rightCmd (c : Cmd) := splitRoot 0 (fun _ => .pass)
  ((move 0 1 2).join (c.join ((move 1 0 2).join (pack 0))))

theorem effective_left {c : P → Cmd} (hc : Effective ltr c) :
    Effective ltr (fun p => leftCmd (c p)) :=
  effective_splitRoot _ (fun _ => effective_const _ _) (hc.join (effective_const _ _))

theorem effective_right {c : P → Cmd} (hc : Effective ltr c) :
    Effective ltr (fun p => rightCmd (c p)) :=
  effective_splitRoot _ (fun _ => effective_const _ _)
    ((effective_const _ _).join (hc.join (effective_const _ _)))

theorem within_left {c : Cmd} (hR : 1 ≤ R) (hc : Within R c) : Within R (leftCmd c) := by
  simp [leftCmd,RegisterWitness.splitRoot_within,Within,pack,hc]
  omega

theorem within_right {c : Cmd} (hR : 3 ≤ R) (hc : Within R c) : Within R (rightCmd c) := by
  simp [rightCmd,RegisterWitness.splitRoot_within,Within,move,forward,forwardBody,flood,give,pack,hc]
  omega

theorem Runs.left {c : Cmd} {f : X → Y} (h : Runs c f) :
    Runs (leftCmd c) (fun x : X × Z => (f x.1,x.2)) := by
  obtain ⟨C,hc⟩ := h
  refine ⟨C+7, fun x env r => ?_⟩
  apply (fits_pair ((hc x.1 env (pile 0 (send x.2) r)).join (fits_pack _ _ _ _ _))).mono
  rw [size_prod, Nat.add_mul]
  have hc' := Nat.mul_le_mul_left C (show size x.1+1 ≤ size x.1+size x.2+1+1 by omega)
  omega

theorem Runs.right {c : Cmd} {f : X → Y} (h : Runs c f) :
    Runs (rightCmd c) (fun x : Z × X => (x.1,f x.2)) := by
  obtain ⟨C,hc⟩ := h
  refine ⟨91+C,fun x env r => ?_⟩
  have h₁ := fits_move (i := 0) (u := 2) (j := 1) (by decide) (by decide) (send x.1) env (pile 0 (send x.2) r)
  have h₂ := hc x.2 env (pile 1 (send x.1) r)
  rw [pile_comm 1 _ r 0 _ (by decide)] at h₁
  have h₃ := fits_move (i := 1) (u := 2) (j := 0) (by decide) (by decide) (send x.1) env (pile 0 (send (f x.2)) r)
  rw [pile_comm 1 _ r 0 _ (by decide)] at h₃
  refine (fits_pair (h₁.join (h₂.join (h₃.join (fits_pack _ _ _ _ _))))).mono ?_
  rw [size_prod, Nat.add_mul]
  have hc' := Nat.mul_le_mul_left C (show size x.2+1 ≤ size x.1+size x.2+1+1 by omega)
  have hsize : (send x.1).count = size x.1 := rfl
  rw [hsize]
  omega

namespace Family

theorem left {f : P → X → Y} (hR : 1 ≤ R) (h : Family R f) :
    Family R (fun p (x : X × Z) => (f p x.1,x.2)) := by
  obtain ⟨c,he,hc⟩ := h
  exact ⟨_,effective_left he,fun p => ⟨within_left hR (hc p).1, (hc p).2.left⟩⟩

theorem right {f : P → X → Y} (hR : 3 ≤ R) (h : Family R f) :
    Family R (fun p (x : Z × X) => (x.1,f p x.2)) := by
  obtain ⟨c,he,hc⟩ := h
  exact ⟨_,effective_right he,fun p => ⟨within_right hR (hc p).1, (hc p).2.right⟩⟩

theorem pair {f : P → X → Y} {g : P → X → Z} (hR : 3 ≤ R) (h : Family R f) (h' : Family R g) :
    Family R (fun p x => (f p x,g p x)) :=
  ((fixed (RegisterWitness.Easy.clone hR)).comp (left (by omega) h)).comp (right hR h')

end Family
end KernelEffectiveFamily

end NearSquareRoot
end Computability
end OAI
