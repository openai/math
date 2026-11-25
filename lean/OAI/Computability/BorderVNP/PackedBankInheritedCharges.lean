import OAI.Computability.BorderVNP.PackedBankIncidenceCharges
import OAI.Computability.BorderVNP.PackedBankInheritedWidths
import OAI.Computability.BorderVNP.PackedBankMergeCharges

/-! # Cumulative local resource charges of a chosen physical histogram

At a retained site we keep its prior syntax and private payload once and
reserve a slab for its old incident cable words and external ports. The
band ties use one equality per distinct live hook or retained cable at each
incident site. At a seed site we charge its frozen guard and box syntax, its
one-copy private table, and its multiplicity-dependent bank and visits.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Packing.InheritedBank

open Crossing Shortening Shortening.StaticRows Shortening.CombiningStep Shortening.SeedIntervals BankCharges
open scoped Classical

variable {D m : ℕ} {K : Type*} [Field K] (e : PaidIdentity K D m)

/-- Fixed contribution of a complete seed packet, its stored one-copy table,
its public record syntax and its resolved one-copy factor sweep. -/
noncomputable def staticLoad (first : Fin D × Bool) (v : TemplateSite e) :=
  wordCount e first v + guardNodes e first v + stored e v + sweepNodes e v

private noncomputable def templateBound := ∑ u : Fin D × Bool, ∑ v : TemplateSite e, staticLoad e u v

private theorem staticLoad_le (first : Fin D × Bool) (v : TemplateSite e) :
    staticLoad e first v ≤ templateBound e :=
  (Finset.single_le_sum (fun i _ => Nat.zero_le (staticLoad e first i)) (Finset.mem_univ v)).trans
    (Finset.single_le_sum (fun u _ => Nat.zero_le (∑ i, staticLoad e u i)) (Finset.mem_univ first))

/-- Fixed per-epoch multiplier for all guard, table, staging and visit costs.
It is chosen before the field-valued packs, selected profile and tile test. -/
noncomputable def loadMultiplier := 1 + 1100 + templateBound e + (1 + BankCharges.bound e)

variable [NeZero D] {P : Type*} [Fintype P] {bits : P → ℕ} (p : Pack D P bits K)
  {A : Type} [Fintype A] (bin : p.layout.Edge → Option A) (perm : Fin D → Equiv.Perm A)
  (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)

private noncomputable abbrev G := (output e p bin perm positive first q).layout

/-- Only the retained and hook wires are joined to the prior or gathered bank.
On a cut self-loop the old table reads its source hook. The fixed profile-internal
cables already have ties in their frozen packets. -/
def gathered : (G e p bin perm positive first q).Site → (G e p bin perm positive first q).Edge → Prop
  | .inl old, .inl (.inr c) => p.layout.src c.val.1 ≠ old
  | _, .inl _ | _, .inr (.inl _) => True
  | _, .inr (.inr _) => False

/-- Every retained site inherits its previous static metadata once. Every
new site contributes its fixed table and packet. The tie allowance covers
one public equality guard and its serialized fields. -/
noncomputable def nextPrior (prior : p.layout.Site → ℕ) (v : (G e p bin perm positive first q).Site) :=
  Sum.elim prior (fun z : Σ _ : A, TemplateSite e => staticLoad e first z.2) v +
    1100 * tieRows (G e p bin perm positive first q) (gathered e p bin perm positive first q v) v

/-- Actual cumulative payload allowance. The prior site's area is carried
once. Its old cable and port words are staged once, and a new site's rectangular
bank and its expanded paid visits are charged at the selected multiplicity. -/
noncomputable def nextPayload (payload : p.layout.Site → ℕ) : (G e p bin perm positive first q).Site → ℕ
  | .inl old => payload old + (incidentWidth p.layout old + portWidth p.layout old)
  | .inr ⟨a,v⟩ => volume e (blocks p.layout bin perm m a) (q a).val v

private theorem oldSlab_le (prior payload : (G e p bin perm positive first q).Site → ℕ) (v : p.layout.Site) :
    incidentWidth p.layout v + portWidth p.layout v ≤
      localRecords (G e p bin perm positive first q) true prior payload (fun u => u = .inl v) := by
  let L := G e p bin perm positive first q
  let old : L.Site := .inl v
  have hw := output_incidentWidth_le e p bin perm positive first q v
  have hp := output_portWidth e p bin perm positive first q v
  apply (Nat.add_le_add hw hp.symm.le).trans
  have h := local_incidence_le L true prior payload old (fun _ => True) L.width bits
    (fun c => Nat.le_add_left _ 1) (fun t => Nat.le_add_left _ 1)
  let equiv : Inherited.Incident L old ≃ {c : L.Edge // True ∧ (L.src c = old ∨ L.dst c = old)} :=
    Equiv.subtypeEquivRight fun _ => ⟨fun hc => ⟨trivial,hc⟩,And.right⟩
  have he := Fintype.sum_equiv equiv (fun c => L.width c.val) (fun c => L.width c.val) (fun _ => rfl)
  refine (Nat.add_le_add_right he.le _).trans ?_
  convert! h using 1
  congr! 3

/-- Complete local history and payload on any region of an actual sewn output.
The right hand side uses the retained physical-record estimate for that very
histogram. In particular the multiplier is independent of the attained copy
counts, the number of sites and the cover level. -/
theorem output_load_le (ex : Bool) (prior payload : p.layout.Site → ℕ)
    (test : (G e p bin perm positive first q).Site → Prop) :
    localRecords (G e p bin perm positive first q) ex
        (nextPrior e p bin perm positive first q prior) (nextPayload e p bin perm positive first q payload) test ≤
      loadMultiplier e * localRecords (G e p bin perm positive first q) ex
        (Sum.elim prior (fun _ => 0))
        (Sum.elim payload (fun z => bankUses e (blocks p.layout bin perm m z.1) (q z.1).val z.2)) test := by
  let L := G e p bin perm positive first q
  let hist : L.Site → ℕ := Sum.elim prior (fun _ => 0)
  let pay : L.Site → ℕ := Sum.elim payload (fun z => bankUses e (blocks p.layout bin perm m z.1) (q z.1).val z.2)
  let newHist := nextPrior e p bin perm positive first q prior
  let newPay := nextPayload e p bin perm positive first q payload
  apply localRecords_of_singletons L ex hist pay newHist newPay
  intro v
  let M := localRecords L ex hist pay (fun u => u = v)
  have one : 1 ≤ M := one_le_siteRecords L ex hist pay v
  let rows := tieRows L (gathered e p bin perm positive first q v) v
  have row : rows ≤ M := tieRows_le L ex hist pay _ v
  have hrow := Nat.mul_le_mul_left 1100 row
  have hstatic := Nat.mul_le_mul_left (templateBound e) one
  rw [Nat.mul_one] at hstatic
  have hswap := exchange_site_records L ex hist pay newHist newPay v
  change _ + boxCost ex (hist v) (pay v) = M + boxCost ex (newHist v) (newPay v) at hswap
  change _ ≤ loadMultiplier e * M
  rw [loadMultiplier,Nat.add_mul,Nat.add_mul,Nat.add_mul,one_mul,Nat.add_mul,one_mul]
  rcases v with old | ⟨a,v⟩
  · cases ex with
    | false =>
      change _ + (prior old + 1) = M + (prior old + 1100*rows + 1) at hswap
      omega
    | true =>
      have hs : incidentWidth p.layout old + portWidth p.layout old ≤ M :=
        oldSlab_le e p bin perm positive first q hist pay old
      change _ + (prior old + (1+payload old)) =
        M + ((prior old+1100*rows)+(1+(payload old+(incidentWidth p.layout old+portWidth p.layout old)))) at hswap
      omega
  · have hs := staticLoad_le e first v
    cases ex with
    | false =>
      change _ + 1 = M + (staticLoad e first v+1100*rows+1) at hswap
      omega
    | true =>
      have ht := BankCharges.tile_le e p bin perm positive first q true prior payload
        (fun u => u = (.inr ⟨a,v⟩ : L.Site))
      have hv : sparse e v + volume e (blocks p.layout bin perm m a) (q a).val v ≤ BankCharges.bound e * M := by
        let site : L.Site := .inr ⟨a,v⟩
        let f := BankCharges.charge e p bin perm positive first q true
        have h := Finset.single_le_sum (fun z _ => Nat.zero_le (if z = site then f z else 0)) (Finset.mem_univ site)
        exact (by simpa only [testedWidth,ite_true] using h : f site ≤ testedWidth f (fun z => z = site)).trans ht
      change _ + (0+(1+bankUses e (blocks p.layout bin perm m a) (q a).val v)) =
        M + ((staticLoad e first v+1100*rows)+(1+volume e (blocks p.layout bin perm m a) (q a).val v)) at hswap
      omega

end Packing.InheritedBank

end BorderVNP
end Computability
end OAI
