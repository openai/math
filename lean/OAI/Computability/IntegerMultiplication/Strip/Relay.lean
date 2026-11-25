import OAI.Computability.IntegerMultiplication.Strip.Across

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Strip
open Code Code.Task
variable {I J : Type} {r : Regime I} {n l : I→ℕ}
abbrev Alive (r : Regime I) (n l : I→ℕ) (p : I→Tree) := Rip r n l p p
namespace Rip
variable {p q v t : I→Tree}
theorem monoSize (h : Rip r n l p q) {N L : I→ℕ}
    (u : ∀ i,n i ≤ N i) (e : ∀ i,l i≤L i) : Rip r N L p q := by
  obtain ⟨k,v⟩ := h; refine ⟨k,v.larger fun x => ?_⟩
  unfold mass; have := (show (0:ℝ) ≤ l x+(r.scale x+1:ℝ)^k by positivity)
  exact mul_le_mul (by exact_mod_cast u _) (by gcongr; exact e _) this (by positivity)
theorem alivePair (h : Alive r n l p) (e : Alive r n l q) : Alive r n l (together p q) :=
  h.left e
end Rip

/-- Marked vehicle. Work can use the descriptor and propagate it. -/
abbrev Drive (r : Regime I) (n l : I→ℕ) (p q : I → Tree) :=
  Rip r n l (together r.header p) q

namespace Drive
variable {p q m v : I→Tree}
theorem started (h : ∀ i, 1 ≤ n i) : Alive r n l r.header :=
  Rip.header h Regime.self

theorem fetch (h : ∀ i, 1 ≤ n i) (pv : Alive r n l p) :
    Drive r n l p r.header :=
  Rip.split (Rip.alivePair (started h) pv) |>.1

theorem self (h : ∀ i, 1 ≤ n i) (pv : Alive r n l p) : Drive r n l p p :=
  Rip.split (Rip.alivePair (started h) pv) |>.2

theorem pipe (a : Drive r n l p q) (b : Drive r n l q m) : Drive r n l p m :=
  ((Rip.split a.again |>.1).twice a).chain b

theorem used (h : Drive r n l p q) : Alive r n l p :=
  (Rip.split h.again).2.idle
theorem small (h : ∀ i, 1 ≤ n i) (pv : Alive r n l p) (hc : r.Small q) : Drive r n l p q :=
  (fetch h pv).chain (Rip.header h hc)

end Drive
/-- Series geometry supplied from the same descriptor. -/
def Station (r : Regime I) {A : I→Type} (s : (i:I)→Series (A i)) :=
  (∀ x, 1≤(s x).count) ∧
    Rip r (fun x => (s x).count) (fun _ => 0) r.header (fun i => send (tally (s i).count))

namespace Station
variable {A B : I→Type} {s : (i:I)→Series (A i)} {t : (i:I)→Series (B i)}
theorem supply (h : Station r s) (e : ∀ x,(s x).count ≤ n x) :
    Rip r n l r.header (fun i => send (tally (s i).count)) :=
  h.2.monoSize e (fun _ => Nat.zero_le _)

theorem pull (h : Station r s) (f : J→I) :
    Station (r.pull f) (fun i => s (f i)) :=
  ⟨fun _ => h.1 _, h.2.pull f⟩

theorem tape {s : I→Dims.Tape} (h : ∀i,Dims.solid (s i)) (g : r.Has (Dims.shape ∘ s)) :
    Station r (fun i => Dims.layout (s i)) := by
  have pos (i) : 1 ≤ (Dims.layout (s i)).count := by rw [Dims.space]; exact Dims.wide _ (h i)
  refine ⟨pos, ?_⟩
  simpa only [Function.comp_def,Dims.space] using
    (Rip.ruler (r:=r) (n:=fun i => (Dims.layout (s i)).count) (l:=fun _ => 0) pos g h (by simp))

theorem fixed (x : Series J) (h : 1 ≤ x.count) : Station r (fun _ => x) :=
  ⟨fun _ => h,Rip.header (fun _ => h) (Regime.fixed _)⟩

theorem product (a : Station r s) (b : Station r t) :
    Station r (fun i => (s i).cart (t i)) := by
  let n i := ((s i).cart (t i)).count
  have es i : (s i).count ≤ n i := by
    unfold n; rw [Series.count_cart]; exact Nat.le_mul_of_pos_right _ (b.1 i)
  have et i : (t i).count ≤ n i := by
    unfold n; rw [Series.count_cart]; exact Nat.le_mul_of_pos_left _ (a.1 i)
  let x (i:I) := (tally (s i).count,tally (t i).count)
  have u := Rip.twice (l:=fun _ => 0) (Station.supply a es) (Station.supply b et)
  let v := (Code.generate (X:=Tally)).on x
  have pn : ∀ i,1≤n i := fun i => (b.1 i).trans (et i)
  refine ⟨pn,?_⟩
  obtain ⟨k,ak⟩ := Rip.relay pn x u v (show ∃ k D : ℕ, ∀ i:I, (((x i).1.length+1)*size (x i).2 : ℕ)+(1:ℝ) ≤ (D:ℝ)*mass r n (fun _ => 0) k i from
      ⟨0,10,fun i => by
        dsimp only [x,n]; rw [tally_length, size_tally,tally_length]
        have ps : (1:ℝ) ≤ (s i).count := by exact_mod_cast a.1 i
        have pb : (1:ℝ) ≤ (t i).count := by exact_mod_cast b.1 i
        simp only [mass, Series.count_cart, Nat.cast_add,Nat.cast_mul,pow_zero,Nat.cast_one,Nat.cast_zero,Nat.cast_ofNat]
        nlinarith [mul_nonneg (sub_nonneg.mpr ps) (sub_nonneg.mpr pb)]⟩)
  have ha := ak.chain (Carries.func ak.budget ak.out List.flatten Easy.flatten)
  simpa only [x,tally_length,Dims.tallies,Series.count_cart,n] using
    (show Rip r n (fun _ => 0) r.header _ from ⟨k,ha⟩)

end Station
end Strip

end IntegerMultiplication
end Computability
end OAI
