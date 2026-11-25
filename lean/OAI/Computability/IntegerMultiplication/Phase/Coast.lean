import OAI.Computability.IntegerMultiplication.Phase.Estate

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Phase
open Net Net.Shuttle Net.Tensor Net.Walsh Strip Strip.Dims Strip.Optic Code Packed Loom Dusk
open Finset

private theorem rack2 (f n : ℕ) :
    ∀ a∈ Loom.Rack (Adic.field 2 f) n,2≤a ∧ a≤base := by
  suffices t : ∀ a∈Adic.field 2 f, 2≤a ∧ a≤base by
    induction n <;> simp_all [Loom.Rack]
    intro a h; rcases h with h|h
    all_goals apply (by assumption : ∀a∈_,2≤a ∧ a≤base) _ h
  induction f with
  | zero => simp [Adic.field]
  | succ f ih =>
    rw [Adic.field,List.forall_mem_cons]
    exact ⟨⟨le_rfl,base_large.le⟩,ih⟩

variable {J W I : Type} {k : ℕ} [Fintype J]
noncomputable section
variable (x : Estate (dim J) ((dim J)^(k+1))) (φ : J≃Fin (dim J)) (j : J)
def harbour_ (_a : Tally) := () -- term
abbrev dirt := Adic.field 2 (dim J^k*width x.tops x.foot)
abbrev first := x.sunrise++leftF φ (dirt x) j
abbrev last_ := rightF φ (dirt x) j ++ x.sunset
theorem bsize (φ : J≃Fin (dim J)) (j : J) :
    (φ j).val + 1 + (dim J - (φ j).val - 1) = dim J := by
  have i := (φ j).isLt
  omega
theorem field_ :
    (dirt x).length = dim J^k*width x.tops x.foot := Loom.field_length _ _
def beach : Estate (dim J) ((dim J)^k) :=
  { metres := x.metres
    shade := x.shade
    tops := x.tops
    foot := x.foot
    sunrise := first x φ j
    sunset := last_ x φ j
    radix := fun a ha=> by
      obtain ⟨A,B⟩ := x.rays
      simp only [first,last_,List.mem_append] at ha
      rcases ha with (p|k)|(z|p)
      · exact A _ p
      · exact rack2 _ _ a k
      · exact rack2 _ _ a z
      exact B _ p
    range := by
      have e := x.range
      simp only [first,last_,leftF,rightF,Loom.ranking,List.length_append,Loom.pieces,field_]
      apply le_trans _ e
      have q := congrArg (fun i=> (dim J^k*width x.tops x.foot)*i) (bsize φ j)
      simp only [Nat.mul_add,Nat.mul_one] at q
      have t : dim J^(k+1)*width x.tops x.foot =
          dim J^k*width x.tops x.foot*dim J := by ring
      rw [t]; unfold width at *; simp only [Nat.mul_add,Nat.mul_one] at *; omega
    okay := by
      have q := (φ j).isLt
      refine safe_r ?_ x.okay
      rw [pow_succ]; exact Nat.le_mul_of_pos_right _ (by omega) }

variable (Y : I→QuestP (W:=W) (dim J)) [Fintype W]
variable {r : Regime I} (h : r.Small (roof Y))
abbrev sun i := (tapes _ (Y i)).sunrise
abbrev moon i := (tapes _ (Y i)).sunset
abbrev amp i := width (tapes _ (Y i)).tops (tapes _ (Y i)).foot
abbrev depth_ i := (Y i).1
abbrev grain_ i := (Y i).2.plot.shade
private theorem held (_D : ℕ) {K:I→ℕ} (h : ∀ i, 1≤K i) (p q : I→Tape)
    (H G : I→ℕ) (hp : Told r p) (hq : Told r q)
    (a : r.Has (fun i=> signs (H i) (G i) (K i-1)))
    (b : r.Has fun i=> tally (dect H G K i)) :
    Station r (fun i=>plain (p i) (q i) (H i) (G i) (K i)) := by
  obtain ⟨n,f⟩ : ∃ n:I→ℕ,K=fun i=>n i+1 :=
    ⟨fun i=>K i-1,funext fun i=>by dsimp; specialize h i; omega⟩
  subst K
  simp at a
  exact (glow p q H G n hp hq b a).valid
include h
omit [Fintype W] in
theorem climate (d : 1≤dim J) :
    Station r (fun i=>(tapes (dim J) (Y i)).terrain) := by
  obtain ⟨_,v,_⟩ := children Y h
  obtain ⟨a,g,t,r0⟩ := profiles Y h
  obtain ⟨y,σ⟩ := controlFiber (fun i=>(tapes _ (Y i)).tops)
    (fun i=>(tapes _ (Y i)).foot) (fun i=>dim J^violet Y i) t r0 v
  exact held 0 (fun i=> one_le_pow₀ (n:=violet Y i) d) (sun Y) (Phase.moon Y) _ _ a g σ y

omit h
-- tariff
def powerNow (i:I) := dim J^depth_ Y i
def users {D : ℕ} (Y : QuestP D (W:=W)) : ℕ := Y.2.radio*dim W^Y.1
abbrev timeMark {D : ℕ} (Y : QuestP D (W:=W)) := users Y * (2*(Y.2.plot.shade+1))

structure Range {D : ℕ} (x y : QuestP D (W:=W)) where
  close : y.1+1=x.1
  common : y.2.plot.metres=x.2.plot.metres
  sense : y.2.plot.shade=x.2.plot.shade
  rows : y.2.plot.terrain.count=x.2.plot.terrain.count
  radio : y.2.radio=x.2.radio
  K : width y.2.plot.tops y.2.plot.foot=width x.2.plot.tops x.2.plot.foot
end
end Phase

end IntegerMultiplication
end Computability
end OAI
