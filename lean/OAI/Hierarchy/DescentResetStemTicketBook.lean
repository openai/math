import OAI.Hierarchy.DescentResetStemTable
import OAI.Hierarchy.DescentResetStemKeyKernel

namespace OAI
/-! # Finite height and exact three-bit descriptor fields at reset stems -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open scoped Classical
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "placement" => B.reset.placement
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => B.reset.orderedReentry B.terminals birth
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "digits" => S.resetOutputDigits ctl.base ctl.radix B.age B.commonDepth
local notation "sel" => selected placement (Z).graph (Z).positive (Z).pay (Z).circuit
local notation "dev" => DescentMixedRouter.device (Z).graph (Z).positive (Z).unit
  (placement).contact (placement).input (placement).site (placement).owner (placement).align (D:=d)
local notation "height" => GroupStage.depthBound D n f g
local notation "capacity" => max (Fintype.card (DescentCommonPalette.rotor (Z).graph).Edge) (2^(height+1))



local notation "rawRank" => ((Z).rawHostRank T vertexCode).trans Fin.valEmbedding
local notation "rawSite" => B.raw.siteFrom (groupRank (Fin.valEmbedding (n:=groups)) rawRank) B.valid.coordinates
local notation "hop" => DescentPhysicalOrder.rename rawSite
local notation "old" => W.granular B.count (z*G.b) B.fit


local notation "A" => input.placement
local notation "digitsIn" => S.resetInputDigits ctl.base ctl.radix i
local notation "c" => (T).commonDepth
local notation "m" => S.groupWidth k tail i+k
local notation "before" => input.order.trans Fin.valEmbedding
local notation "fits" => B.frame.enough.trans (Nat.sub_le ..)


local notation "Slot" => Fin (2^(m-c))×Fin (2*(A).cap)

open DescentResetFieldAssembler DescentResetWindowResidentSources
local notation "R" => blocks B
local notation "rank" => (Z).rawHostRank T vertexCode
local notation "shapeId" => (Z).codeHost T vertexCode
local notation "lab" => DescentRelativeContacts.shortName c
local notation "End" => (old).graph.Edge

local notation "center" u:arg => (receiverRoot B u)
local notation "actor" u:arg => B.frame.host.symm (center u).1
local notation "rack" u:arg => (center u).2
local notation "site" s:arg j:arg => endSite A s (beforeStem B j)

open DescentResetStemDecoder DescentRelativeContacts
local notation "Y" => 2^(Z).n
local notation "r" => (Z).k-c
local notation "use" => useRotor (placement).b (placement).depth (placement).L (placement).keys (placement).hub (placement).old
local notation "label" s:arg j:arg => lab ((T).code ((T).home (ends (old).graph s j)))

local notation "count" => DescentFallbackShapeTable.rows r Y
local notation "K" => 2*count

def stemBook (u : Host) (s : Bool) (j : Fin K) :=
  stemTable B u s (some (j.val/2,decide (j.val%2=1)))

theorem stemBook_same (u v : Host) (same : u.1.2=v.1.2) (s : Bool) (j : Fin K) :
    stemBook B u s j=stemBook B v s j := stem_table_same B u v same s _

theorem stem_ticket_fits (s : Bool) (j : End) :
    (stemTicket B s j).1 < count := by
  let t:=(T).home (ends (old).graph s j)
  exact DescentFallbackShapeTable.cell_fit _ _ (Nat.sub_le_sub_right ((T).codeLegal t).2.1 _) (Nat.mod_lt _ (Nat.two_pow_pos _))

theorem stem_key_limit (u : Host) (s : Bool) (slot : Slot) :
    DescentResetStemKey.code ((oldStemAt B u s slot).map (stemTicket B s)) ≤ K := by
  cases read : oldStemAt B u s slot with
  | none=>exact Nat.zero_le _
  | some j=>
    have cap:=stem_ticket_fits B s j
    change 1+2*(stemTicket B s j).1+(stemTicket B s j).2.toNat≤2*count
    cases (stemTicket B s j).2 <;> simp only [Bool.toNat_true,Bool.toNat_false] <;> omega

def stemBookRead (u : Host) (s : Bool) (key : ℕ) : Meta :=
  if yes : 0 < key ∧ key ≤ K then stemBook B u s ⟨key-1,by omega⟩ else .blank

theorem book_at_ticket (u : Host) (s : Bool) (j : End) :
    stemBookRead B u s (DescentResetStemKey.code (some (stemTicket B s j)))=
      stemTable B u s (some (stemTicket B s j)) := by
  let t:=stemTicket B s j
  have bound : t.1 < count:=stem_ticket_fits B s j
  have closed : (1+2*t.1+t.2.toNat)-1=2*t.1+t.2.toNat:=by omega
  have how : (2*t.1+t.2.toNat)/2=t.1 ∧ decide ((2*t.1+t.2.toNat)%2=1)=t.2 := by
    cases t with
    | mk a b=>cases b <;> simp [Nat.add_mod]; omega
  have safe : 0<1+2*t.1+t.2.toNat ∧ 1+2*t.1+t.2.toNat ≤ K := by
    have bits : t.2.toNat≤1:=by cases t.2 <;> decide
    omega
  change (if _ : 0<1+2*t.1+t.2.toNat ∧ 1+2*t.1+t.2.toNat ≤ K then _ else _) = _
  rw [dite_eq_left safe]
  change stemTable B u s (some (((1+2*t.1+t.2.toNat-1)/2),decide ((1+2*t.1+t.2.toNat-1)%2=1))) = stemTable B u s (some t)
  rw [closed, how.1, how.2]

theorem stem_book_read (u : Host) (s : Bool) (slot : Slot) :
    stemBookRead B u s (DescentResetStemKey.code ((oldStemAt B u s slot).map (stemTicket B s)))=
      «meta» B u (localOrigin B u (stemIndex B s slot)) := by
  rw [←stem_table_read B u s slot]
  cases hit : oldStemAt B u s slot with
  | none=>simp [DescentResetStemKey.code,stemBookRead,stemTable,stemWord]
  | some j=>exact book_at_ticket B u s j

theorem all_stem_fields_fit (u : Host) (s : Bool) (key : Option (ℕ×Bool)) :
    ∀f, DescentResetFieldAssembler.digits (stemTable B u s key) f<2^3 := by
  have bounded (n : ℕ) : stemOrdinal (rank u.1.2).val (stemNeighbors B u) n≤4 := by
    unfold stemOrdinal
    apply (Finset.card_filter_le ..).trans
    have neighbors:=B.next.placement.degreeBound u.1.2
    rw [B.next.branch] at neighbors
    have cap : (stemNeighbors B u).card≤3 := by
      exact (Finset.card_map (s:=B.next.placement.near u.1.2) (f:=rawRank)).trans_le neighbors
    exact (Finset.card_insert_le _ _).trans (by omega)
  have valid (v : Option (ℕ × ℕ)) (j : Fin 7) :
      DescentResetFieldAssembler.digits
        (stemWord (rank u.1.2).val (stemNeighbors B u) s ((A).hub (actor u)) v) j < 2^3 := by
    cases v with
    | none =>
      change DescentResetFieldAssembler.digits Meta.blank j < 8
      fin_cases j <;> decide
    | some pair =>
      rcases pair with ⟨src, dst⟩
      simp only [stemWord]
      split
      · have bit (b : Bool) : b.toNat < 8 := by cases b <;> decide
        have small (x : ℕ) : stemOrdinal (rank u.1.2).val (stemNeighbors B u) x < 8 :=
          lt_of_le_of_lt (bounded x) (by decide)
        fin_cases j <;> first | exact bit _ | exact small _ | exact (by decide : 1 < 8)
      · fin_cases j <;> decide
  exact valid _

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
