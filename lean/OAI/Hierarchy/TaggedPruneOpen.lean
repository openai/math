import OAI.Hierarchy.TaggedData
import OAI.Hierarchy.Catalyst
import OAI.Hierarchy.CorrectionProducts

namespace OAI
/-! # Local projection to the exposed permutation tags -/

noncomputable section
namespace Hierarchy.TaggedPrune

open LinearAlgebra.SpectralBooks SiteTensor
open Catalyst Tagged
open Computability.VPVNP.RAMSerialization (wordBits)
open scoped Classical BigOperators

abbrev Index {h : ℕ} (count : Equiv.Perm (Row h) → ℕ) := Σ perm, Fin (count perm)

/-- Use the protocol's own binary words for its accepted selectors. Unused
words may occur anywhere in the encoding. -/
abbrev Encoding {h : ℕ} (count : Equiv.Perm (Row h) → ℕ) (B : ℕ) :=
  (perm : Equiv.Perm (Row h)) → Fin (count perm) ↪ Bits B

/-- The permutation can be encoded using one address per row. Padding each
permutation's selector word to a common length bounds the joint entropy. -/
theorem card_index {h B : ℕ} (count : Equiv.Perm (Row h) → ℕ)
    (enc : ∀ perm, count perm ≤ 2^B) :
    Fintype.card (Index count) ≤ 2^(h*2^h+B) := by
  have hperm : Fintype.card (Equiv.Perm (Row h)) ≤ (2^h)^(2^h) := by
    have H := Fintype.card_le_of_injective
      (fun e : Equiv.Perm (Row h) => (e : Row h → Row h))
      (fun e f he => Equiv.ext (congrFun he))
    simpa only [Row, Fintype.card_fun, Fintype.card_fin] using H
  calc
    Fintype.card (Index count) = ∑ perm, count perm := by simp [Index]
    _ ≤ ∑ _ : Equiv.Perm (Row h), 2^B := Finset.sum_le_sum fun perm _ => enc perm
    _ = Fintype.card (Equiv.Perm (Row h)) * 2^B := by simp
    _ ≤ (2^h)^(2^h)*2^B := Nat.mul_le_mul_right _ hperm
    _ = _ := by rw [←pow_mul, ←pow_add]

/-- The bound applies to any discarded subset, including an empty one. -/
theorem discarded_entropy {h B : ℕ} (count : Equiv.Perm (Row h) → ℕ)
    (enc : ∀ perm, count perm ≤ 2^B) (keep : Index count → Prop) :
    Real.logb 2 (Fintype.card {i // ¬keep i}) ≤ (h:ℝ)*2^h+B := by
  classical
  let m := Fintype.card {i // ¬keep i}
  have hm : m ≤ 2^(h*2^h+B) :=
    (Fintype.card_subtype_le (fun i => ¬keep i)).trans (card_index count enc)
  by_cases hz : m=0
  · change Real.logb 2 (m:ℝ) ≤ _
    simp [hz]; positivity
  have hu : (m : ℝ) ≤ (2:ℝ)^(h*2^h+B) := by exact_mod_cast hm
  have HL := Real.logb_le_logb_of_le (by norm_num : (1:ℝ)<2)
    (Nat.cast_pos.mpr (Nat.pos_of_ne_zero hz)) hu
  change Real.logb 2 (m:ℝ) ≤ _
  simpa [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1:ℝ)<2)] using HL

variable {F : Type*} [Field F] {h w k : ℕ} {b : Fin k → ℕ}
abbrev OpenPins (h w : ℕ) {k : ℕ} (b : Fin k → ℕ) := Catalyst.Port (pins h w) b
abbrev Table (F : Type*) (h w : ℕ) {k : ℕ} (b : Fin k → ℕ) := (OpenPins h w b → Bool) → F

def bit (i : Row h) (j : Fin h) : OpenPins h w b :=
  .inl (portIndex h w (.inr (.inl (i,j))))

def exposed (perm : Equiv.Perm (Row h)) (f : Table F h w b) : Table F h w b :=
  fun x => if (perm : Row h → Row h) = tag (fun i => x (.inl i)) then f x else 0

def perTag (perm : Equiv.Perm (Row h)) : Table F h w b :=
  ideal b (fun x => if ∀ i, target x i = source x (perm i) then 1 else 0)

/-- The routing protocol itself has only source, target, and catalyst ends. -/
abbrev RoutingPin (h w : ℕ) {k : ℕ} (b : Fin k → ℕ) :=
  ((Row h × Fin w) × Bool) ⊕ (Wire b × Bool)

def routingPort : RoutingPin h w b → OpenPins h w b
  | .inl (ij,false) => .inl (portIndex h w (.inl ij))
  | .inl (ij,true) => .inl (portIndex h w (.inr (.inr ij)))
  | .inr i => .inr i

def addTagPorts (f : (RoutingPin h w b → Bool) → F) : Table F h w b :=
  fun x => f (x ∘ routingPort)

def routingMatch (perm : Equiv.Perm (Row h)) (x : RoutingPin h w b → Bool) : F :=
  if ∀ v : Wire b, x (.inr (v,false)) = x (.inr (v,true)) then
    if ∀ i, (fun j => x (.inl ((i,j),true))) = (fun j => x (.inl ((perm i,j),false))) then 1 else 0
  else 0

/-- The per-tag identity on its original untagged ports implies the identity
on the common output format by pulling back the same coefficients. -/
theorem addTagPorts_sum {count : Equiv.Perm (Row h) → ℕ}
    (route : Index count → (RoutingPin h w b → Bool) → F)
    (ident : ∀ perm, (∑ i : Fin (count perm), route ⟨perm,i⟩) = routingMatch perm)
    (perm : Equiv.Perm (Row h)) :
    (∑ i : Fin (count perm), addTagPorts (route ⟨perm,i⟩)) = perTag perm := by
  funext x
  have atPins := congrFun (ident perm) (x ∘ routingPort)
  rw [Finset.sum_apply]
  change (∑ i : Fin (count perm), route ⟨perm,i⟩ (x ∘ routingPort)) = _
  calc
    _ = routingMatch perm (x ∘ routingPort) := by simpa only [Finset.sum_apply] using atPins
    _ = _ := by
      let z := fun i : Fin (pins h w) => x (.inl i)
      by_cases cat : ∀ v : Wire b,x (.inr (v,false))=x (.inr (v,true))
      · by_cases data : ∀ i,target z i=source z (perm i)
        · exact (show routingMatch perm (x ∘ routingPort)=(1:F) from
              (ite_eq_left cat).trans (ite_eq_left data)).trans
            (show perTag (F:=F) (b:=b) perm x=1 from (ite_eq_left cat).trans (ite_eq_left data)).symm
        · exact (show routingMatch perm (x ∘ routingPort)=(0:F) from
              (ite_eq_left cat).trans (ite_eq_right data)).trans
            (show perTag (F:=F) (b:=b) perm x=0 from (ite_eq_left cat).trans (ite_eq_right data)).symm
      · exact (show routingMatch (F:=F) perm (x ∘ routingPort)=(0:F) from ite_eq_right cat).trans
          (show perTag (F:=F) (b:=b) perm x = 0 from ite_eq_right cat).symm

/-- Adding open tag pins to a local table means ignoring the new coordinates
in every row of its local matrices. -/
theorem addTagPorts_restricts {S : ℕ} (τ : OpenPins h w b → Fin S)
    (f : (RoutingPin h w b → Bool) → F) {Y : Raw.{0} (Fin S) F}
    (r : ((CorrectionProducts.raw f).group (τ ∘ routingPort)).Restricts Y) :
    ((CorrectionProducts.raw (addTagPorts f)).group τ).Restricts Y := by
  obtain ⟨A,H⟩ := r
  refine ⟨fun s x y => A s (fun u => x ⟨routingPort u.val,u.property⟩) y,?_⟩
  intro x
  exact H (fun s u => x s ⟨routingPort u.val,u.property⟩)

/-- Multiplicities within a routing identity survive summation over the exposed
permutation. Invalid tag assignments have no summand. -/
theorem exposed_sum {count : Equiv.Perm (Row h) → ℕ}
    (route : Index count → Table F h w b)
    (routing : ∀ perm, (∑ i : Fin (count perm), route ⟨perm,i⟩) = perTag perm) :
    (∑ a : Index count, exposed a.1 (route a)) = ideal b (coeff F h w) := by
  funext x
  let d : Fin (pins h w) → Bool := fun i => x (.inl i)
  rw [Finset.sum_apply,Fintype.sum_sigma]
  have row (perm : Equiv.Perm (Row h)) :
      (∑ i : Fin (count perm), exposed perm (route ⟨perm,i⟩) x) =
        if (perm : Row h → Row h) = tag d then perTag perm x else 0 := by
    change (∑ i : Fin (count perm), if (perm : Row h → Row h) = tag d then route ⟨perm,i⟩ x else 0) = _
    by_cases hv : (perm : Row h → Row h) = tag d
    · simpa only [ite_eq_left hv,Finset.sum_apply] using congrFun (routing perm) x
    · simp [hv]
  simp_rw [row]
  by_cases through : ∀ v : Wire b, x (.inr (v,false)) = x (.inr (v,true))
  · simp only [perTag,ideal,ite_eq_left through]
    change (∑ perm : Equiv.Perm (Row h), if (perm : Row h → Row h) = tag d then
      (if ∀ i, target d i = source d (perm i) then (1:F) else 0) else 0) = _
    have matchSum := Tagged.sum_matchings (F:=F) (source d) (target d) (tag d)
    refine (Eq.trans ?_ matchSum).trans ?_
    · apply Finset.sum_congr rfl
      intro p _
      by_cases eqn : (p : Row h → Row h)=tag d
      · by_cases data : ∀ i,target d i=source d (p i)
        · simp only [ite_eq_left eqn,ite_eq_left data,ite_eq_left (And.intro eqn data)]
        · simp [eqn]
      · simp [eqn]
    · unfold Tagged.coeff
      by_cases valid : Valid (source d) (tag d) (target d)
      · exact (ite_eq_left valid).trans (ite_eq_left valid).symm
      · exact (ite_eq_right valid).trans (ite_eq_right valid).symm
  · simp [perTag,ideal,through]

/-- Attaching the exposed tag delta only multiplies rows of the existing local
matrices by zero or one. The installed binary communication widths are preserved. -/
theorem exposed_restricts {S : ℕ} (τ : OpenPins h w b → Fin S) (perm : Equiv.Perm (Row h))
    (f : Table F h w b) {Y : Raw.{0} (Fin S) F}
    (r : ((CorrectionProducts.raw f).group τ).Restricts Y) :
    ((CorrectionProducts.raw (exposed perm f)).group τ).Restricts Y := by
  obtain ⟨A,hA⟩ := r
  let good (s : Fin S) (a : {v // τ v = s} → Bool) : Prop :=
    ∀ i j (eqn : τ (bit i j) = s), a ⟨bit i j,eqn⟩ = wordBits h (perm i) j
  refine ⟨fun s a y => if good s a then A s a y else 0,?_⟩
  intro x
  let read (v : OpenPins h w b) := x (τ v) ⟨v,rfl⟩
  let d : Fin (pins h w) → Bool := fun i => read (.inl i)
  have decode (i : Row h) (j : Fin h) : wordBits h (tag d i) j = read (bit i j) :=
    congrFun ((wordBits h).apply_symm_apply (fun t => read (bit i t))) j
  have iffAll : ((perm : Row h → Row h) = tag d) ↔ ∀ s, good s (x s) := by
    constructor
    · intro eqn s i j es
      subst s
      have ee := congrArg (fun e : Row h → Row h => wordBits h (e i) j) eqn
      exact (decode i j).symm.trans ee.symm
    · intro all
      funext i
      apply (wordBits h).injective
      funext j
      exact ((all (τ (bit i j)) i j rfl).symm).trans (decode i j).symm
  change (if (perm : Row h → Row h) = tag d then f read else 0) = _
  by_cases hg : ∀ s, good s (x s)
  · simp only [ite_eq_left (iffAll.mpr hg),hg,ite_true]
    exact hA x
  · rw [ite_eq_right (mt iffAll.mp hg)]
    obtain ⟨s,hs⟩ := not_forall.mp hg
    symm
    apply Finset.sum_eq_zero
    intro y _
    exact mul_eq_zero_of_right _ (Finset.prod_eq_zero (Finset.mem_univ s) (ite_eq_right hs))

end Hierarchy.TaggedPrune

end
end OAI
