import OAI.Hierarchy.DescentSeedIncidenceLoad
import OAI.Hierarchy.DescentInitialPackage

namespace OAI
/-! # Initial ordinary-site and saturated hub loads from their actual native incidences -/

namespace Hierarchy.DescentInitialHost
open Computability.BorderVNP.Crossing
open scoped Classical BigOperators
noncomputable section

variable {D : ℕ} {P : Type} [Fintype P] (N : Network D P (fun _=>1))
theorem inside_load (w β : ℕ) (v : N.Site) : incidenceLoad N w β (.inl v)=w*N.bitDegree v := by
  unfold Network.bitDegree
  change _=w*(Finset.univ.filter fun t : OldPort N=>owner N t=v).card
  calc
    _ = ∑ _t ∈ Finset.univ.filter (fun t : OldPort N => owner N t=v), w := by
      rw [Finset.sum_filter]
      unfold incidenceLoad
      simp only [Fintype.sum_sum_type,Fintype.sum_prod_type,Fintype.sum_bool]
      have orient (s : N.Site) : (v=s) ↔ (s=v) := eq_comm
      simp [source,target,hubFlag,owner,Finset.sum_add_distrib,orient]; ac_rfl
    _ = _ := by simp [Nat.mul_comm]

theorem hub_load (w β : ℕ) (p : P) : incidenceLoad N w β (.inr p)=w*β := by
  simp [incidenceLoad,Fintype.sum_sum_type,source,target,hubFlag]

theorem core_adj (e : Wire N) : target N e∈near N (source N e) ∧ source N e∈near N (target N e) :=
  wire_near N e

theorem old_cap (tri : N.Trivalent) (w hist : ℕ) (h : 3*w+hist≤256*w) (v : Site N) :
    incidenceLoad N w 256 v+(if hubFlag N v then 0 else hist)≤256*w := by
  cases v with
  | inl v =>
    simp only [inside_load,hubFlag,Sum.elim_inl,Bool.false_eq_true,ite_false]
    exact (Nat.add_le_add_right (Nat.mul_le_mul_left w (tri.2 v)) hist).trans (by simpa [Nat.mul_comm] using h)
  | inr p => simp [hub_load,hubFlag,Nat.mul_comm]

variable {G I : Type} [Fintype G] [Fintype I] [DecidableEq G] [DecidableEq I]
omit [Fintype G] [Fintype I] in
/-- A source address contains a coarse group and a site. The disjoint low
coordinate is the native block being mixed by this step's common layout. -/
theorem fibre_units {J S : Type} [Fintype J] [Fintype S] [DecidableEq S]
    (digits : J≃G×I) (u : J×S→ℕ) (g : G) (v : S) (x : I) :
    (∑j : J×S, if ((digits j.1).1,j.2)=(g,v) ∧ (digits j.1).2=x then u j else 0)=
      u (digits.symm (g,x),v) := by
  let a : J×S := (digits.symm (g,x),v)
  rw [Finset.sum_eq_single_of_mem a (Finset.mem_univ _)]
  · simp [a]
  · rintro ⟨b,t⟩ _ ne
    apply ite_eq_right
    rintro ⟨same,low⟩
    apply ne
    have high : (digits b).1=g := congrArg Prod.fst same
    have site : t=v := congrArg Prod.snd same
    have cell : digits b=(g,x) := Prod.ext high low
    exact Prod.ext (digits.eq_symm_apply.mpr cell) site

omit [DecidableEq I] [Fintype G] in
/-- No expense proportional to the number of blocks is introduced by the
disjoint-union label. At a fixed new group and low bit there is one old site. -/
theorem sparse_root {k : ℕ} (digits : I≃G×Fin (2^k))
    (w hist : ℕ) (tri : N.Trivalent) (cap : 3*w+hist≤256*w) (g : G) (v : Site N) (x : Fin (2^k)) :
    (∑j : I×Site N,if ((digits j.1).1,j.2)=(g,v) ∧ (digits j.1).2=x then
      incidenceLoad N w 256 j.2+(if hubFlag N j.2 then 0 else hist) else 0)≤256*w := by
  rw [fibre_units digits]
  exact old_cap N tri w hist cap v

end
end Hierarchy.DescentInitialHost

end OAI
