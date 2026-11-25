import OAI.Hierarchy.DescentClosedStemRoster
import OAI.Hierarchy.DescentResetContactLocalRoster
import OAI.Hierarchy.DescentResetInstalledDigits
import OAI.Hierarchy.DescentResetStemCompactOrder

namespace OAI
/-! # The old host digit inside every installed parent at a reset receiver -/
noncomputable section
namespace Hierarchy.DescentResetCableSlots
open DescentResetOrdinalDigits

/-- Read the original host digit from each branch that has one. -/
def originHostDigit {N U k Y Ht cap : ℕ} :
    (originalLayout N U k Y Ht cap).Value → Option (Fin U)
  | .inl _ => none
  | .inr (.inl t) => some t.1
  | .inr (.inr (.inl (.inl x))) => some x.1.1
  | .inr (.inr (.inl (.inr x))) => some x.1.1
  | .inr (.inr (.inr ((_,.inl g),_))) => some g.1
  | .inr (.inr (.inr ((_,.inr t),_))) => some t.1

end Hierarchy.DescentResetCableSlots

namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentChosenRouter DescentResetAttachments DescentSharedCableNames
open DescentParallelBase DescentHostDirectory DescentCommonHost DescentResetCableSlots
open DescentDenseHostOrder DescentResetTrunks
open DescentResetStemCompactOrder
open scoped Classical BigOperators
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "A" => input.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "R" => B.reset.placement
local notation "old" => W.granular B.count (z*G.b) B.fit
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "rows" => blocks B
local notation "rawDigits" => (Z).installedParts T vertex birth

def originHost (e : (coarse).graph.Edge) : Option (Z).V :=
  match motherNames B e with
  | .inl _=>none
  | .inr (.inl t)=>some ((T).code t).1
  | .inr (.inr (.inl c))=>some ((Z).rootVertex T ((R).owner false c))
  | .inr (.inr (.inr ⟨(_,g₀),_⟩))=>some ((Z).rootVertex T g₀)

/-- The host reported by the case analysis is literally the digit of the
original installed-ordinal comparison, including the left socket of a link. -/
theorem originHost_digit (e : (coarse).graph.Edge) :
    originHostDigit (rawDigits e)=(originHost B e).map vertex := by
  obtain ⟨tag,rfl⟩:=(motherNames B).symm.surjective e
  unfold originHost ResetInput.installedParts
  change originHostDigit (originParts (R) vertex (T).code (fun t=>((T).codeLegal t).2)
    (GroupStage.depthBound D n f g) (T).bookHeight (Z).graph (Z).positive (Z).pay (Z).circuit d birth
    ((motherNames B) ((motherNames B).symm tag)))=_
  rw [Equiv.apply_symm_apply]
  rcases tag with stem|trunk|c|⟨⟨s,g₀⟩,j⟩
  · rfl
  · rfl
  · cases c <;> rfl
  · cases g₀ <;> rfl

def originDomain (u : Host) :=
  insert (receiverRoot B u).1 ((T).columns.near (receiverRoot B u).1)

/-- The old halo emitted by the source frame, read in the original host
coordinates used by the terminal/base digit. -/
theorem origin_neighbor (x y : (Z).V) :
    y∈(T).columns.near x ↔ B.frame.host.symm y∈(A).near (B.frame.host.symm x) := by
  obtain ⟨a,rfl⟩:=B.frame.host.surjective x
  obtain ⟨b,rfl⟩:=B.frame.host.surjective y
  rw [B.roster.2.1,Equiv.symm_apply_apply,Equiv.symm_apply_apply]
  change b∈((A).near a).filter (fun j=>a∈(A).near j) ↔ _
  exact ⟨fun yes=>(Finset.mem_filter.mp yes).1,fun yes=>Finset.mem_filter.mpr ⟨yes,((A).symmetric a b).mp yes⟩⟩

theorem origin_domain_room (u : Host) : (originDomain B u).card≤(A).degree+1 := by
  let x:=(receiverRoot B u).1
  have nearEq : ((T).columns.near x).map B.frame.host.symm.toEmbedding=(A).near (B.frame.host.symm x) := by
    ext v
    constructor
    · intro yes
      obtain ⟨v₀,hv,rfl⟩:=Finset.mem_map.mp yes
      exact (origin_neighbor B _ _).mp hv
    · intro inside
      exact Finset.mem_map.mpr ⟨B.frame.host v,(origin_neighbor B _ _).mpr (by simpa using inside),B.frame.host.symm_apply_apply v⟩
  have bound : ((T).columns.near x).card≤(A).degree := by
    have eqn:=congrArg Finset.card nearEq
    rw [Finset.card_map] at eqn
    exact eqn.le.trans ((A).degreeBound _)
  exact (Finset.card_insert_le x ((T).columns.near x)).trans (Nat.add_le_add_right bound 1)

/-- A live public contact has a real old grain. On both ends the selected
root is precisely its original endpoint host. -/
theorem contact_owner_host (s : Bool) (j : (old).graph.Edge) :
    (Z).rootVertex T ((R).owner s ((R).contact j))=
      B.frame.host ((A).pos (ends (old).graph s j)).2 := by
  have address:=DescentChosenRouter.public_read (R) (T).code (T).source s j
  rw [←(T).attach] at address
  rw [←(R).align]
  have host (p : (R).Public) : (Z).rootVertex T ((R).site s p)=
      (DescentChosenRouter.publicAddress (R) (T).code p).1 := by
    rcases p with ⟨g₀,r⟩|t <;> rfl
  exact (host _).trans ((congrArg Prod.fst address).trans (B.frame.homeHost _))

theorem contact_witness (c : (R).Contact) (positive : 0<(rows).count (contactParent B c)) :
    ∃j : (old).graph.Edge,(R).contact j=c := by
  let e:=contactParent B c
  have census:=congrArg (fun a : ℕ×ℕ×ℕ×ℕ×ℕ×ℕ×Bool=>a.2.2.2.2.2.1)
    ((Z).contactArchive T vertex birth c)
  change (coarse).graph.width e=Fintype.card {j : (old).graph.Edge // (R).contact j=c}*(Z).unit at census
  have counted:=weight_quotient B e
  rw [census] at counted
  have inhabited : 0<Fintype.card {j : (old).graph.Edge // (R).contact j=c} := by
    by_contra empty
    have zero:=Nat.eq_zero_of_not_pos empty
    rw [zero,Nat.zero_mul,Nat.zero_div] at counted
    exact (Nat.ne_of_gt positive) counted
  obtain ⟨j⟩:=Fintype.card_pos_iff.mp inhabited
  exact ⟨j.val,j.property⟩

theorem contact_origin_mem (u : Host) (c : (R).Contact)
    (positive : 0<(rows).count (contactParent B c))
    (atEnd : (rows).src (contactParent B c)=u ∨ (rows).dst (contactParent B c)=u) :
    (Z).rootVertex T ((R).owner false c)∈originDomain B u := by
  rcases atEnd with here|there
  · have hit:=contact_endpoint_root B c false
    change receiverRoot B ((rows).src (contactParent B c))=_ at hit
    rw [here] at hit
    exact Finset.mem_insert.mpr (.inl (congrArg Prod.fst hit).symm)
  · have hit:=contact_endpoint_root B c true
    change receiverRoot B ((rows).dst (contactParent B c))=_ at hit
    rw [there] at hit
    obtain ⟨j,reserved⟩:=contact_witness B c positive
    have left:=contact_owner_host B false j
    have right:=contact_owner_host B true j
    rw [reserved] at left right
    apply Finset.mem_insert.mpr
    right
    rw [congrArg Prod.fst hit]
    apply (origin_neighbor B _ _).mpr
    rw [left,right,Equiv.symm_apply_apply,Equiv.symm_apply_apply]
    change ((A).pos (W.graph.src j.1)).2∈(A).near ((A).pos (W.graph.dst j.1)).2
    obtain ⟨v,hv,eqn⟩:=Finset.mem_map.mp ((A).peers j.1).2
    exact (congrArg Prod.snd eqn : v=((A).pos (W.graph.src j.1)).2) ▸ hv

theorem trunk_center_host (u : Host) (t : (Z).Fallback)
    (atEnd : (rows).src (trunkParent B t)=u ∨ (rows).dst (trunkParent B t)=u) :
    ((T).code t).1=(receiverRoot B u).1 := by
  let e:=trunkParent B t
  have trunkFields:=(Z).trunkFields T t
  obtain ⟨left,right⟩:=endpoint_root B e
  rcases atEnd with here|there
  · rw [here] at left
    exact ((congrArg Prod.fst left).trans (congrArg (position (Z).graph) (congrArg RawFields.src trunkFields))).symm
  · rw [there] at right
    exact ((congrArg Prod.fst right).trans (congrArg (position (Z).graph) (congrArg RawFields.dst trunkFields))).symm

theorem originHost_mem (u : Host) (x : Local rows u) (v : (Z).V) (present : originHost B x.val=some v) :
    v∈originDomain B u := by
  obtain ⟨e,positive,atEnd⟩:=x
  obtain ⟨tag,rfl⟩:=(motherNames B).symm.surjective e
  change (match (motherNames B) ((motherNames B).symm tag) with
    | .inl _=>none
    | .inr (.inl t)=>some ((T).code t).1
    | .inr (.inr (.inl c))=>some ((Z).rootVertex T ((R).owner false c))
    | .inr (.inr (.inr ⟨(_,g₀),_⟩))=>some ((Z).rootVertex T g₀))=some v at present
  rw [Equiv.apply_symm_apply] at present
  rcases tag with stem|t|c|j
  · cases present
  · cases present
    exact Finset.mem_insert.mpr (.inl (trunk_center_host B u t atEnd))
  · cases present
    exact contact_origin_mem B u c positive atEnd
  · rcases j with ⟨⟨s,g₀⟩,q₀⟩
    cases present
    exact Finset.mem_insert.mpr (.inl (congrArg Prod.fst (private_owner B u ⟨(s,g₀),q₀⟩ atEnd)).symm)

def haloNumbers (u : Host) := (originDomain B u).image (T).columns.host

theorem halo_host (v : (Z).V) : (T).columns.host v=(vertex v).val := by
  obtain ⟨a,rfl⟩:=B.frame.host.surjective v
  simpa using B.roster.1 a

def haloNumber (u : Host) (v : (Z).V) := compress (haloNumbers B u) ((T).columns.host v)

theorem haloNumber_room (u : Host) (v : (Z).V) : haloNumber B u v≤(A).degree+1 :=
  ((compress_bound _ _).trans Finset.card_image_le).trans (origin_domain_room B u)

theorem haloNumber_live (u : Host) (x : Local rows u) (v : (Z).V) (present : originHost B x.val=some v) :
    haloNumber B u v<(A).degree+1 := by
  let table:=haloNumbers B u
  let code:=(T).columns.host v
  have inside : code∈table:=Finset.mem_image_of_mem _ (originHost_mem B u x v present)
  have earlier : (table.filter (·<code))⊂table :=
    (Finset.ssubset_iff_of_subset (Finset.filter_subset _ _)).mpr ⟨code,inside,by simp⟩
  exact (Finset.card_lt_card earlier).trans_le (Finset.card_image_le.trans (origin_domain_room B u))

theorem origin_host_compare (u : Host) (x y : Local rows u) (a b : (Z).V)
    (atX : originHost B x.val=some a) (atY : originHost B y.val=some b) :
    (haloNumber B u a<haloNumber B u b ↔ vertex a<vertex b) ∧
      (haloNumber B u a=haloNumber B u b ↔ vertex a=vertex b) := by
  have one:=(Finset.mem_image_of_mem (T).columns.host (originHost_mem B u x a atX))
  have two:=(Finset.mem_image_of_mem (T).columns.host (originHost_mem B u y b atY))
  have strict:=compress_lt (haloNumbers B u) one two
  have eqn:=compress_eq (haloNumbers B u) one two
  change (haloNumber B u a<haloNumber B u b ↔ (vertex a).val<(vertex b).val) ∧ _
  exact ⟨strict.trans (by rw [halo_host,halo_host]),
    eqn.trans (by rw [halo_host,halo_host,Fin.ext_iff])⟩

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
