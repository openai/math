import OAI.Computability.IntegerMultiplication.Cap.Mix
import Mathlib.Data.Int.GCD

namespace OAI
namespace Computability
namespace IntegerMultiplication

namespace Cap
open Finset Nat
def inverse (s x:ℕ) :=
  ∑ i:Fin s, if x*i.val % s=1 then i.val else 0
theorem inverse_use (s x : ℕ) (p : 2≤ s) (h: Nat.Coprime x s):
    inverse s x < s ∧
    x*inverse s x ≡ 1 [MOD s] := by
  obtain ⟨u,t,e⟩ := Nat.exists_mul_mod_eq_one_of_coprime h p
  have v:x*u ≡ 1 [MOD s]:= e.trans (Nat.mod_eq_of_lt p).symm
  have unique (i:Fin s) (p0:x*i.val%s=1): i.val=u := by
    have p1 : x*i.val≡1 [MOD s]:=p0.trans (Nat.mod_eq_of_lt p).symm
    have r: i.val≡u [MOD s]:=calc
      i.val ≡ (x*u)*i.val [MOD s] := (Eq.trans (show i.val%s=(1*i.val)%s by rw [one_mul]) (v.symm.mul_right i.val))
      _ = (x*i.val)*u := by ring
      _ ≡ u [MOD s] := by simpa only [one_mul] using p1.mul_right u
    simpa only [Nat.ModEq,Nat.mod_eq_of_lt i.isLt,Nat.mod_eq_of_lt t] using r
  have b : inverse s x=u := by
    unfold inverse
    rw [sum_eq_single (⟨u,t⟩:Fin s)]
    · exact ite_eq_left e
    · intro i _ e
      apply ite_eq_right
      exact fun h=>e (Fin.ext (unique i h))
    simp
  rw [b]; exact ⟨t,v⟩

variable {d:ℕ} {s:Bounds d}
def Nice (s:Bounds d) :=
  (∀ i, 2≤ s i) ∧ ∀ a b,a≠b → Nat.Coprime (s a) (s b)
theorem base_coprime (h:Nice s) (i : Fin d) :
    Nat.Coprime (base s i) (s i) := by
  apply Nat.coprime_prod_left_iff.mpr
  intro j _
  split
  next e=> exact h.2 _ _ (Fin.ne_of_lt e)
  exact Nat.coprime_one_left _

def coefficient (s:Bounds d) (i:Fin d) :=
  inverse (s i) (base s i)
theorem coefficient_use (h:Nice s) (i):
    coefficient s i< s i ∧ base s i * coefficient s i ≡ 1 [MOD s i] :=
  inverse_use _ _ (h.1 i) (base_coprime h i)

theorem space_mod (h:Nice s) (a b:ℕ):
    (∀ i,a ≡ b [MOD s i]) ↔ a ≡ b [MOD space s] := by
  suffices e : ∀ E:Finset (Fin d),(∀ i∈E,a≡ b [MOD s i]) ↔ a≡b [MOD (∏ i∈E,s i)] by
    simpa [space] using (e univ)
  intro E; induction E using Finset.induction_on with
  | empty=>simp [Nat.ModEq, Nat.mod_one]
  | insert i E hi ih=>
    have j: Nat.Coprime (∏ j∈E,s j) (s i) := by
      apply Nat.coprime_prod_left_iff.mpr
      intro e v
      exact h.2 _ _ (fun w=>hi (w ▸ v))
    rw [prod_insert hi,← Nat.modEq_and_modEq_iff_modEq_mul j.symm,← ih]
    simp only [mem_insert]
    aesop

theorem late (i j:Fin d) (h:i< j):
    s i ∣ base s j := by
  unfold base
  have t:= Finset.dvd_prod_of_mem (fun k=> if k< j then s k else 1) (Finset.mem_univ i)
  simpa only [ite_eq_left h] using t

def tilt (x:Vector_ s) (i:Fin d) : ℕ :=
  coefficient s i * ∑ j:Fin d,if j < i then (x j).val*base s j else 0

theorem addmods {A:Type*} [DecidableEq A]{n} (E:Finset A) (x y:A→ℕ)
    (h:∀ i∈E,x i ≡ y i [MOD n]):
    ∑ i∈E,x i ≡ ∑ i∈E,y i [MOD n]:= by
  induction E using Finset.induction_on with
  | empty=> simp [Nat.ModEq]
  | insert i E e ih =>
    rw [sum_insert e,sum_insert e]
    exact (h i (mem_insert_self ..)).add (ih (fun i t=>h _ (mem_insert_of_mem t)))

theorem controls (h:Nice s) (x : Vector_ s) (i:Fin d) :
    coefficient s i*amount s x ≡ (x i).val+tilt x i [MOD s i] := by
  let f j:= (x j).val*base s j
  let g j : ℕ:= (if j < i then coefficient s i*f j else 0)+(if j=i then (x i).val else 0)
  have e (j:Fin d): coefficient s i*f j ≡ g j [MOD s i] := by
    unfold f g
    rcases lt_trichotomy j i with q|q|q
    · simp [q,q.ne, ModEq,f]
    · subst j
      rw [ite_eq_right (by simp),ite_eq_left rfl, Nat.zero_add,
        show coefficient s i * ((x i).val * base s i) =
          (base s i * coefficient s i)*(x i).val by ring]
      simpa only [one_mul] using (coefficient_use h i).2.mul_right (x i).val
    · simp only [ite_eq_right q.ne',ite_eq_right (not_lt_of_gt q), zero_add]
      apply Nat.modEq_zero_iff_dvd.mpr
      apply dvd_mul_of_dvd_right
      exact dvd_mul_of_dvd_right (Cap.late _ _ q) _
  have P := addmods (n:=s i) univ (fun j=>coefficient s i*f j) g (fun i _=> e i)
  unfold amount tilt
  rw [Finset.mul_sum,Finset.mul_sum]
  simp only [g,sum_add_distrib,sum_ite_eq',mem_univ,ite_true] at P
  rw [Nat.add_comm]
  simpa only [mul_ite,Nat.mul_zero] using P

/-- transport in *output* direction: record at mixed x goes to the address transform x. -/
def turn (h:Nice s) (x:Vector_ s):Vector_ s :=
  fun i=>⟨((x i).val+tilt x i)%s i,Nat.mod_lt _ (by have t:=h.1 i; omega)⟩
theorem bears (h:Nice s) (x:Vector_ s) (i:Fin d) :
    (turn h x i).val=coefficient s i*amount s x % s i :=
  Eq.symm (controls h x i)
theorem undo (h:Nice s) (x:Vector_ s) (i):
    (turn h x i).val*base s i ≡ amount s x [MOD s i] := by
  rw [bears]
  refine ModEq.trans ((mod_modEq ..).mul_right _) ?_
  rw [show coefficient s i * amount s x * base s i = (base s i*coefficient s i)*amount s x by ring]
  simpa only [one_mul] using (coefficient_use h i).2.mul_right (amount s x)
theorem turn_unique (h:Nice s):
    Function.Injective (turn h) := by
  intro x y e
  have z := (space_mod h (amount s x) (amount s y)).mp
    (fun i=> (undo h x i).symm.trans (e ▸ undo h y i)) -- rewrite direction occurrences?
  apply amount_inj s x y
  simpa [ModEq,Nat.mod_eq_of_lt (amount_lt ..)] using z
noncomputable def tune (h:Nice s) : Equiv.Perm (Vector_ s) :=
  Equiv.ofBijective _ (Finite.injective_iff_bijective.mp (turn_unique h))

theorem turn_sum (h:Nice s) (x y z:Vector_ s) :
    (∀ i, (turn h x i).val+(turn h y i).val ≡ (turn h z i).val [MOD s i])
    ↔ amount s x+amount s y ≡ amount s z [MOD space s] := by
  rw [← space_mod h]
  constructor
  · intro e i
    have t := (e i).mul_right (base s i)
    rw [Nat.add_mul] at t
    exact ((undo h x i).add (undo h y i)).symm.trans (t.trans (undo h z i))
  intro e i
  have v (x:Vector_ s): (turn h x i).val ≡ coefficient s i * amount s x [MOD s i] := by rw [bears]; exact mod_modEq _ _
  refine ((v x).add (v y)).trans ?_
  rw [← Nat.mul_add]
  exact ((e i).mul_left _).trans (v z).symm
end Cap

end IntegerMultiplication
end Computability
end OAI
