import OAI.Computability.BorderVNP.ShortenEpochProfileRecords

/-!
# Local physical size after joint histogram sewing

The new end of a hook is charged to the original cable end exposed there.
Every old endpoint is counted at its own position, even for an uncharged
nonlocal cable. Each nearby seed contributes the fixed cost of its public
profile and, in expanded mode, a linear cost in its matched blocks.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening

open Crossing Finset
open scoped Classical

private theorem ite_record_mono (w : ℕ) {p q : Prop} [Decidable p] [Decidable q] (h : p → q) :
    (if p then w else 0) ≤ if q then w else 0 := by by_cases hp : p <;> simp [hp,h]

private theorem tested_mono {E : Type*} [Fintype E] (w : E → ℕ) {p q : E → Prop}
    (h : ∀ x, p x → q x) : testedWidth w p ≤ testedWidth w q :=
  sum_le_sum fun x _ => ite_record_mono _ (h x)

private theorem tested_keep_le {E : Type*} [Fintype E] (w : E → ℕ) (S : Finset E)
    {p : {x : E // x ∉ S} → Prop} {q : E → Prop} (h : ∀ x, p x → q x.val) :
    testedWidth (fun x => w x.val) p ≤ testedWidth w q := by
  classical
  refine (tested_mono _ h).trans ?_
  let f (x : E) := if q x then w x else 0
  change (∑ x : {x : E // x ∉ S}, f x.val) ≤ ∑ x, f x
  rw [← Fintype.sum_subtype_add_sum_subtype (fun x => x ∉ S) f]
  exact Nat.le_add_right _ _

private theorem sew_tested_sums {U V A : Type} [Fintype U] [Fintype V] [Fintype A]
    {E : A → Type} [∀ a, Fintype (E a)] (w : U ⊕ (V ⊕ Σ a, E a) → ℕ)
    (p : U ⊕ (V ⊕ Σ a, E a) → Prop) :
    testedWidth w p =
      testedWidth (fun u => w (.inl u)) (fun u => p (.inl u)) +
      testedWidth (fun v => w (.inr (.inl v))) (fun v => p (.inr (.inl v))) +
      ∑ a, testedWidth (fun e => w (.inr (.inr ⟨a,e⟩))) (fun e => p (.inr (.inr ⟨a,e⟩))) := by
  simp only [testedWidth,Fintype.sum_sum_type,Fintype.sum_sigma,add_assoc]

variable {D m : ℕ} {K : Type*} [Field K] {P : Type*} [Fintype P] {bits : P → ℕ}
    {A : Type} [Fintype A] (e : PaidIdentity K D m) (j : A → ℕ)
    {p : Pack D P bits K} (t : AddressPartition p.layout A)
    (b : ∀ a, Bundle p.layout (t.part a) (j a*m)) (q : ProfileCounts e j)

/-- The public history at each original site remains accessible there. A new
box has its own record and no previous local history. -/
def sewnPrior (prior : p.layout.Site → ℕ) : (sewnProfile e j t b q).Site → ℕ :=
  Sum.elim prior (fun _ => 0)

/-- In a new bank site, one use is charged for each copy of the represented
term. Private data at retained sites are carried to the actual output layout. -/
def sewnPayload (payload : p.layout.Site → ℕ) : (sewnProfile e j t b q).Site → ℕ :=
  Sum.elim payload (fun z => bankUses e (j z.1) (q z.1).val z.2)

/-- Tile record cost of an actual replacement. The hypotheses specify the
locality of old sites, hook ends and inserted seed boxes. -/
theorem sewnProfile_records_le (expanded : Bool) (prior payload : p.layout.Site → ℕ)
    (region : p.layout.Site → Prop) (near : Finset A)
    (post : (sewnProfile e j t b q).Site → Prop)
    (hold : ∀ v, post (.inl v) → region v)
    (hhook : ∀ k, post (.inr ((t.parallel (seedNetwork e j t b q)).attach k)) →
      region (oldHookSite p.layout t.selected k))
    (hnew : ∀ a v, post (.inr ⟨a,v⟩) → a ∈ near) :
    localRecords (sewnProfile e j t b q) expanded (sewnPrior e j t b q prior)
      (sewnPayload e j t b q payload) post ≤
      3 * localRecords p.layout expanded prior payload region +
      ∑ a ∈ near, (profileDescriptorBound e + if expanded then profilePayloadBound e * j a else 0) := by
  classical
  let N := p.layout
  let G := seedNetwork e j t b q
  let S := sewnProfile e j t b q
  let bo (v : N.Site) := boxCost expanded (prior v) (payload v)
  let bn (a : A) (v : (G a).Site) := recordCost expanded (bankUses e (j a) (q a).val v)
  let ho (k : N.CutPorts t.selected) := recordCost expanded (N.cutWidths t.selected k)
  let eo (c : N.Edge) := recordCost expanded (N.width c)
  let en (a : A) (c : (G a).Edge) := recordCost expanded ((G a).width c)
  let ew (c : S.Edge) := recordCost expanded (S.width c)
  let pw (i : P) := recordCost expanded (bits i)
  let pin (a : A) (v : (G a).Site) := post (.inr ⟨a,v⟩)
  let new (a : A) := testedWidth (bn a) (pin a) +
    testedWidth (en a) (fun c => pin a ((G a).src c)) +
    testedWidth (en a) (fun c => pin a ((G a).dst c))
  let hout (k : N.CutPorts t.selected) := post (.inl (oldHookSite N t.selected k))
  let hin (k : N.CutPorts t.selected) := post (.inr ((t.parallel G).attach k))
  let keep (get : N.Edge → N.Site) := testedWidth (fun c : {c : N.Edge // c ∉ t.selected} => eo c.val)
    (fun c => post (.inl (get c.val)))
  have hbox : testedWidth bo (fun v => post (.inl v)) ≤ testedWidth bo region := tested_mono _ hold
  have hp : testedWidth pw (fun i => post (.inl (N.attach i))) ≤
      testedWidth pw (fun i => region (N.attach i)) := tested_mono _ (fun i => hold _)
  have hk (get : N.Edge → N.Site) : keep get ≤ testedWidth eo (fun c => region (get c)) :=
    tested_keep_le eo t.selected (fun c => hold _)
  have hook0 : testedWidth ho hout ≤ endRecords N expanded region :=
    (tested_mono _ (fun k => hold (oldHookSite N t.selected k))).trans (hook_records_le _ _ _ _)
  have hook1 : testedWidth ho hin ≤ endRecords N expanded region :=
    (tested_mono _ hhook).trans (hook_records_le _ _ _ _)
  have hh (a : A) : new a ≤ if a ∈ near then
      profileDescriptorBound e + (if expanded then profilePayloadBound e * j a else 0) else 0 := by
    by_cases ha : a ∈ near
    · rw [ite_eq_left ha]
      refine le_trans ?_ (seed_internal_records_le e expanded (j a) (q a).val (profileCounts_total e j q a))
      have full {E : Type} [Fintype E] (w : E → ℕ) (test : E → Prop) : testedWidth w test ≤ ∑ x, w x :=
        sum_le_sum fun x _ => by change (if test x then w x else 0) ≤ w x; split_ifs <;> omega
      change testedWidth _ _ + testedWidth _ _ + testedWidth _ _ ≤ (∑ v, bn a v) + 2 * ∑ c, en a c
      have h1 := full (bn a) (pin a)
      have h2 := full (en a) (fun c => pin a ((G a).src c))
      have h3 := full (en a) (fun c => pin a ((G a).dst c))
      omega
    · have hn (v) : ¬pin a v := fun h => ha (hnew a v h)
      simp [new,testedWidth,hn,ha]
  have hall : (∑ a, new a) ≤ ∑ a ∈ near,
      (profileDescriptorBound e + if expanded then profilePayloadBound e * j a else 0) :=
    (sum_le_sum (s := univ) fun a _ => hh a).trans_eq (by rw [←sum_filter,filter_mem_eq_inter,univ_inter])
  have src := sew_tested_sums ew (fun c => post (S.src c))
  have dst := sew_tested_sums ew (fun c => post (S.dst c))
  change testedWidth ew (fun c => post (S.src c)) =
    testedWidth ho hout + keep N.src + ∑ a, testedWidth (en a) (fun c => pin a ((G a).src c)) at src
  change testedWidth ew (fun c => post (S.dst c)) =
    testedWidth ho hin + keep N.dst + ∑ a, testedWidth (en a) (fun c => pin a ((G a).dst c)) at dst
  have site : testedWidth (fun v => boxCost expanded (sewnPrior e j t b q prior v)
      (sewnPayload e j t b q payload v)) post = testedWidth bo (fun v => post (.inl v)) +
      ∑ a, testedWidth (bn a) (pin a) := by
    change (∑ v : N.Site ⊕ Σ a, (G a).Site, if post v then boxCost expanded
      (sewnPrior e j t b q prior v) (sewnPayload e j t b q payload v) else 0) = _
    rw [Fintype.sum_sum_type, Fintype.sum_sigma]
    simp [testedWidth,bo,bn,pin,boxCost,sewnPrior,sewnPayload,Sum.elim]
    congr 1
  change testedWidth _ post + testedWidth ew _ + testedWidth ew _ + testedWidth pw _ ≤ _
  rw [site,src,dst]
  dsimp only [new] at hall
  rw [sum_add_distrib,sum_add_distrib] at hall
  change _ ≤ 3 * (testedWidth bo region + testedWidth eo (fun c => region (N.src c)) +
    testedWidth eo (fun c => region (N.dst c)) + testedWidth pw (fun i => region (N.attach i))) + _
  change testedWidth ho hout ≤ testedWidth eo (fun c => region (N.src c)) +
    testedWidth eo (fun c => region (N.dst c)) at hook0
  change testedWidth ho hin ≤ testedWidth eo (fun c => region (N.src c)) +
    testedWidth eo (fun c => region (N.dst c)) at hook1
  have hs := hk N.src
  have hd := hk N.dst
  change _ + testedWidth pw (fun i => post (.inl (N.attach i))) ≤ _
  omega

end Shortening

end BorderVNP
end Computability
end OAI
