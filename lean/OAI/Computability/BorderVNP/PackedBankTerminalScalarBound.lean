import OAI.Computability.BorderVNP.PackedBankBirthScalarLimits

/-! # Magnitudes of all frozen and cable-dependent terminal operands

The ordinal in an empty interval can reach the end of the old bin. Charging
the original bin population also covers these rows, without requiring any
positive overlap at the terminal.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Shortening.SeedIntervals

open Crossing Packing
open scoped Classical

variable {D : ℕ} [NeZero D] {P : Type*} {bits : P → ℕ} (N : Network D P bits)
    {S : Type} (bin : N.Edge → Option S) (perm : Fin D → Equiv.Perm S) (m : ℕ) (names : S → ℕ)

/-- Both the clipped width and the untrimmed ordinal are bounded by the
old bin's population, up to a factor two for the latter. -/
theorem descriptor_numeric {a : S} (z : {z : N.Edge // bin z = some a}) (b : Band D) :
    let d := descriptor N bin perm m names z b
    d.span ≤ count N bin a ∧ d.ordinal ≤ 2*count N bin a := by
  intro d
  have hc : (∑ i : {i : N.Edge // bin i = some a}, N.width i.val) = count N bin a := by
    simp [count,BinBits,Fintype.card_sigma]
  have hw : d.width ≤ count N bin a := (Finset.single_le_sum (f := fun i : {i : N.Edge // bin i = some a} =>
    N.width i.val) (fun _ _ => Nat.zero_le _) (Finset.mem_univ z)).trans_eq hc
  have hs : d.start ≤ count N bin a := by
    apply le_trans _ hc.le
    apply Finset.sum_le_sum
    intro i _
    change (if cableName N i.val < cableName N z.val then N.width i.val else 0) ≤ N.width i.val
    split <;> omega
  unfold CutDescriptor.span CutDescriptor.ordinal CutDescriptor.localStart overlapWidth cutOffset
  omega

omit [NeZero D] in
/-- Total old cable width bounds each actual bin, without an assumption
about the size of the names assigned to those bins. -/
theorem population_le_total (a : S) : count N bin a ≤ ∑ z, N.width z := by
  rw [count_eq_sum]
  apply Finset.sum_le_sum
  intro z _
  split <;> omega

end Shortening.SeedIntervals

namespace Packing.Inherited

open Crossing Crossing.Profile.Cell CellSparse Shortening Shortening.SeedIntervals Shortening.StaticRows
  Shortening.CombiningStep InheritedProfile BankSite BankJoint BankCharges BankPacket BankCircuit CellAddresses
open private slice_le from OAI.Computability.BorderVNP.PackedBankHeaderCapacity
open scoped Classical

variable {D m : ℕ} [NeZero D] {K : Type*} [Field K] (e : PaidIdentity K D m)
    {P S : Type} [Fintype P] {bits : P → ℕ} [Fintype S] (p : Pack D P bits K)
    (bin : p.layout.Edge → Option S) (perm : Fin D → Equiv.Perm S)
    (positive : p.layout.Edge → Bool) (first : Fin D × Bool) (q : Counts e p bin perm)
    {T : Type*} (tile : (output e p bin perm positive first q).layout.Site → T) (prior payload : p.layout.Site → ℕ)
    (M : ℕ) (cap : BirthTileCap e p bin perm positive first q tile prior payload M)
    (a : S) {ns ne np : ℕ} (siteID : (output e p bin perm positive first q).layout.Site ↪ Fin ns)
    (edgeID : (output e p bin perm positive first q).layout.Edge ↪ Fin ne) (portID : P ↪ Fin np)
    (binName : S → ℕ) (B : ℕ) (pool : ∀ s, count p.layout bin s ≤ B)
local notation3 "G" => (output e p bin perm positive first q).layout
local notation3 "work₀" => workAt e p bin perm positive first q
local notation3 "raw₀" => InheritedProfile.raw e p bin perm positive first q a siteID edgeID portID

include cap pool in
private theorem hook_fields_le (d : Fin D) (z : {z : p.layout.Edge // bin z = some (perm d a)}) (src : Bool) :
    Packet.RecordFields (terminalHook e p bin perm positive first q a id work₀ siteID edgeID portID binName d z src)
      (birthScalarLimit e M B) := by
  let u := seedHook e p bin perm a d z src
  let v := incidentSite G u false
  let v' : {x : (G).Site // id x = v} := ⟨v,rfl⟩
  let wire := incidentWire G u false
  let sb := siteBase G id v siteID work₀ v'
  let wb := wireBase G id v edgeID portID work₀ v' wire
  let desc := descriptor p.layout bin perm m binName z (some (d,true))
  let L := terminalLayout (blocks p.layout bin perm m a) m (q a).val
  let row : Unit ⊕ Unit ⊕ Fin e.count := .inr (.inl ())
  let base := (L.port row).base
  let S₀ := birthCapacity e M
  have hbank := birthBank_le e p bin perm positive first q tile prior payload M cap v
  have hsb : sb ≤ S₀ := ((Nat.le_add_right _ _).trans (siteBase_fits G id v siteID work₀ v')).trans
    ((Nat.le_add_right _ _).trans hbank)
  have hwb : wb ≤ S₀ := (wireBase_le G id v edgeID portID work₀ v' wire).trans hbank
  have hbase : base ≤ S₀ := by
    have hs := site_le e p bin perm positive first q tile prior payload M cap a (.inr (.inl first))
    have hb := slice_le L row .base
    change base ≤ Fintype.card (Unit ⊕ Unit ⊕ Fin e.count)*L.stride at hb
    change _ + Fintype.card (Unit ⊕ Unit ⊕ Fin e.count)*L.stride ≤ _ at hs
    have h : BankCharges.bound e*M ≤ S₀ := by dsimp [S₀,birthCapacity]; rw [Nat.add_mul]; omega
    exact hb.trans ((Nat.le_add_left _ _).trans (hs.trans h))
  obtain ⟨hspan,hord⟩ := descriptor_numeric p.layout bin perm m binName z (some (d,true))
  change desc.span ≤ _ at hspan
  change desc.ordinal ≤ _ at hord
  have hp := pool (perm d a)
  change (1 ≤ _ ∧ desc.span ≤ _ ∧
    (sb+base+desc.ordinal*1 ≤ _ ∧ 0 ≤ _ ∧ 1 ≤ _) ∧ (wb ≤ _ ∧ 0 ≤ _ ∧ 1 ≤ _)) ∧ True
  dsimp only [S₀] at hsb hwb hbase
  simp only [birthScalarLimit,Nat.mul_one,and_true]
  repeat' constructor <;> omega

include cap pool in
/-- All actual scalar words of a fresh terminal, including every cable-dependent
hook row in the physical order. Empty intervals retain their computed ordinal. -/
theorem terminal_scalarBound (hm : 0 < m) (t : Fin D × Bool) :
    (terminalSite e p bin perm positive first q a siteID edgeID portID binName t).ScalarBound
      (birthScalarLimit e M B) := by
  apply birthScalar_of_records
  intro r hr
  simp only [terminalSite,Site.rows,List.reverse_singleton,List.flatten_cons,List.flatten_nil,List.append_nil,List.mem_append] at hr
  rcases hr with ht | hh
  · change r ∈ (format e first (.inr (.inl t))).2.map (RecordCode.read (terminalWords e raw₀ t)) at ht
    exact (emitted_recordFields e first (.inr (.inl t)) (terminalWords e raw₀ t) (birthCapacity e M)
      (fun i => birthPrepared_le e p bin perm positive first q tile prior payload M cap a siteID edgeID portID
        hm (pin e (.inr (.inl t)) i)) r ht).mono (birthFrozen_le e first (.inr (.inl t)) M B)
  · obtain ⟨z,_,rfl⟩ := List.mem_map.mp hh
    exact hook_fields_le e p bin perm positive first q tile prior payload M cap a siteID edgeID portID
      binName B pool t.1 z _

end Packing.Inherited

end BorderVNP
end Computability
end OAI
