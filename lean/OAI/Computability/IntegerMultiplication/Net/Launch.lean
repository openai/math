import OAI.Computability.IntegerMultiplication.Net.Contract
import OAI.Computability.IntegerMultiplication.Port.Shot

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Net.Shuttle
open Matrix Tensor Finset IntegerMultiplication.Port Motif Halo
noncomputable section
variable {J : Type} [DecidableEq J] [Fintype J]

namespace Rank
variable {p : ℕ}
abbrev present (r : J→Pinpoint p) := univ.filter fun j => r j ≠ Option.none

theorem high (r : J→Pinpoint p) (k : J→ℕ) (e : Function.Injective k) :
    (∀ i, r i=Option.none) ∨
    ∃ i t, r i=some t ∧ ∀ j∈Lag.others r i,k j < k i := by
  by_cases n : (present r).Nonempty
  · right
    obtain ⟨i,hi,v⟩ := exists_max_image _ k n
    obtain ⟨m,hm⟩ : ∃ m, r i = some m := by
      cases g : r i <;> simp_all [present]
    refine ⟨i,m,hm,fun j hj => ?_⟩
    have h := (Lag.active_iff ..).mp hj -- issue
    exact lt_of_le_of_ne (v j (by simp [present,h])) (fun z => h.1 (e z))
  exact .inl fun i => by
    by_contra g; exact n ⟨i,by simp [present,g]⟩

theorem low (r : J→Pinpoint p) (k : J→ℕ) (e : Function.Injective k) :
    (∀ i,r i=Option.none) ∨
    ∃ i t,r i=some t ∧ ∀ j∈Lag.others r i,k i < k j := by
  by_cases n : (present r).Nonempty
  · right
    obtain ⟨i,hi,v⟩ := exists_min_image _ k n
    obtain ⟨m,hm⟩ : ∃ m, r i=some m := by
      cases g : r i <;> simp_all [present]
    refine ⟨i,m,hm,fun j hj => ?_⟩
    have h := (Lag.active_iff ..).mp hj
    exact lt_of_le_of_ne (v j (by simp [present,h])) (fun z => h.1 (e z).symm)
  exact .inl fun i => by
    by_contra g; exact n ⟨i,by simp [present,g]⟩

def shear {R : Type} [CommRing R] (M : Mat J R) (x : Duplex J R) : Duplex J R :=
  (x.1 + M *ᵥ x.2,x.2)
omit [DecidableEq J] in
@[simp] theorem sheen {R} [CommRing R] (M N : Mat J R) (x : Duplex J R) :
    shear M (shear N x)=shear (N+M) x := by simp [shear,add_mulVec,add_assoc]

theorem emit (u v : J→Pinpoint p) (k : J→ℕ) (e : Function.Injective k) :
    ∃ l : List (Lag J p), (∀ r∈l,r.legal k) ∧
      (l.map Lag.prices).sum≤1 ∧ ∀ j s,
      l.foldl (Lag.fire j) s =
        shear (vecMulVec (Lag.point u j) (Lag.point v j)) s := by
  have mid {j} (x : J→Tower p j) : vecMulVec (Lag.point u j) (Lag.point v j) *ᵥ x =
      (fun i => Lag.point u j i*((Lag.point v j) ⬝ᵥ x)) := by
    funext i
    simp [vecMulVec,mulVec,dotProduct,Finset.mul_sum,mul_assoc]
  rcases high v k e with h|⟨t,b,g,hb⟩
  · refine ⟨[],by simp,by simp,fun j x => ?_⟩
    rw [shear,mid,show Lag.point v j=0 by funext; simp [Lag.point,h]]; simp [← Pi.zero_def]
  rcases low u k e with h|⟨i,a,f,ha⟩
  · exact ⟨[],by simp,by simp,fun _ _ => by
      rw [shear,mid]
      simp [Lag.point,h,← Pi.zero_def]⟩
  have d := Lag.passes _ _ _ _ a b k ha hb
  exact ⟨_,d.1,d.2.le,fun j s => by simpa [shear,mid] using Lag.strikes i t u v a b f g k hb j s⟩

theorem table {m : ℚ} (h : m∈catalog) :
    ∃ s : Pinpoint base, ∀ j, s.stamp j = read base j m := by
  -- use base records den limit need export
  obtain ⟨s,r⟩ := Pinpoint.from_rat m base_prime (mTitle h).1 (mTitle h).2
  exact ⟨s,fun j => (r j).unique (base_record h j).1⟩
theorem compileQ (x : Outer Point ℚ) (h : ∀ i : Point, x.1 i ∈ catalog ∧ x.2 i∈catalog)
    (k : Point→ℕ) (e : Function.Injective k) :
    ∃ l : List (Lag Point base), (∀ r∈l,r.legal k) ∧
      (l.map Lag.prices).sum ≤ 1 ∧ ∀ j s,l.foldl (Lag.fire j) s = shear (component j x) s := by
  choose u he using fun i : Point => table (h i).1
  choose v hf using fun i : Point => table (h i).2
  have eu (j) : Lag.point u j=vector j x.1 := funext (fun i => he i j)
  have ev (j) : Lag.point v j=vector j x.2 := funext (fun i => hf i j)
  simpa only [eu,ev,component] using emit u v k e
end Rank

theorem choiceSchedule (a b : Mark) (rank : Point → ℕ) (e : Function.Injective rank)
    (x : Place.road align a b) :
    ∃ l : List (Lag Point base), (∀ r∈l,r.legal rank) ∧
      ((l.map Lag.prices).sum:ℤ) ≤ allow a b ∧ ∀ j s,
        l.foldl (Lag.fire j) s = Rank.shear (deck j b-deck j a) s := by
  by_cases q : a=b
  · subst b; exact ⟨[],by simp,by simp,by intro _ _; simp [Rank.shear]⟩
  obtain ⟨A,B⟩ := checked _ _ x q
  have study : ∀ t : List (Outer Point ℚ), (∀ v ∈ t,v∈manifestQ a b) →
      ∃ l : List (Lag Point base), (∀ r∈l,r.legal rank) ∧
      (l.map Lag.prices).sum ≤ t.length ∧ ∀ j s,
        l.foldl (Lag.fire j) s = Rank.shear ((t.map (component j)).sum) s := by
    intro t h
    induction t with
    | nil => exact ⟨[],by simp,by simp,fun _ _ => by simp [Rank.shear]⟩
    | cons f t ih =>
      obtain ⟨l,e1,e2,e3⟩ := ih (fun z v => h z (List.mem_cons_of_mem _ v))
      obtain ⟨k,n1,n2,n3⟩ := Rank.compileQ f (partQ _ _ A B f (h f List.mem_cons_self)) rank e
      refine ⟨k++l,fun r hx => (List.mem_append.mp hx).elim (n1 r) (e1 r),
        by simp only [List.length_cons,List.map_append,List.sum_append]; omega,fun _ _ => ?_⟩
      rw [List.foldl_append,n3,e3,Rank.sheen,List.map_cons,List.sum_cons]
  obtain ⟨l,h,c,g⟩ := study (manifestQ a b) fun _ => id
  exact ⟨l,h, (by exact_mod_cast c : (((l.map Lag.prices).sum:ℕ):ℤ)≤(manifestQ a b).length) |>.trans (obligation a b x).2,
    by simpa only [sum_from a b x] using g⟩
end
end Net.Shuttle

end IntegerMultiplication
end Computability
end OAI
