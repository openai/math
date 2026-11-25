import OAI.Hierarchy.DescentResetStemRawSeen
import OAI.Hierarchy.DescentResetStemPeerCriterion
import OAI.Hierarchy.DescentResetStemShapeTemplate

namespace OAI
/-! # The native one-based peer ticket agrees with the complete raw stem relation -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentIssuedFallbackPanel DescentGL DescentSIMDLookup DescentSharedCableNames DescentSharedCableNames.Stage
open DescentResetCableSlots DescentResetLocalRoster DescentParallelBase DescentResetAttachments
open DescentCompiler DescentColonies DescentCommonHost DescentChosenRouter DescentMixedRouter
open DescentStageEdgeReceipt DescentDenseHostOrder DescentResetTrunks
open private Hierarchy.DescentSixParty.ClosedReset.Window.old_panel
  Hierarchy.DescentSixParty.ClosedReset.Window.grain_at
  from OAI.Hierarchy.DescentResetStemRead
open scoped Classical
noncomputable section

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)

set_option quotPrecheck false
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertexCode" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "groups" => S.groupCount (i+1)
local notation "Host" => Stage.Host (Fin groups) B.next.V k
local notation "height" => GroupStage.depthBound D n f g


local notation "A" => input.placement
local notation "c" => (T).commonDepth
local notation "m" => S.groupWidth k tail i+k
local notation "before" => input.order.trans Fin.valEmbedding

local notation "Slot" => Fin (2^(m-c))×Fin (2*(A).cap)

open DescentResetFieldAssembler DescentResetWindowResidentSources
local notation "rank" => (Z).rawHostRank T vertexCode

local notation "center" u:arg => (receiverRoot B u)
local notation "actor" u:arg => B.frame.host.symm (center u).1

open DescentResetStemDecoder DescentRelativeContacts
local notation "Y" => 2^(Z).n
local notation "shapeBits" => (Z).k-c

local notation "shapeCount" => DescentFallbackShapeTable.rows shapeBits Y
local notation "K" => 2*shapeCount

open DescentResetStemPeerChip DescentResetPeerUnionRAM DescentSIMDLookup
local notation "pool" => DescentDenseHostOrder.roster (Z).graph shapeBits height
local notation "size" => (pool).card
local notation "tpl" s:arg => fun j : Fin K=>localTemplate (Z).graph shapeBits height s j.val

/-- The public finite pair table, after adding the true previous-actor coordinate,
returns the literal two ends of the saved granular stem. -/
theorem decoded_stem_pair {a : ℕ} (u : Host) (s : Bool) (slot : Slot) (key_ : Cell a)
    (read : key_.val=DescentResetStemKey.code ((oldStemAt B u s slot).map (stemTicket B s))) :
    (decoded (tpl s) key_.val).map (fun z=>
      (z.1.val+size*((vertexCode) (center u).1).val,z.2.val+size*((vertexCode) (center u).1).val))=
      (oldStemAt B u s slot).map (stemPair B s) := by
  have nonempty:=((Z).hostFields T (vertexCode) u.1.2).2.pos
  cases him : oldStemAt B u s slot with
  | none=>simp [him,DescentResetStemKey.code] at read; simp [read,decoded]
  | some j=>
    let short:=stemTicket B s j
    let name:=2*short.1+short.2.toNat
    have ht : short.1< shapeCount:=stem_ticket_fits B s j
    have small : name<K:=by dsimp [name];cases short.2 <;> simp <;> omega
    have id : key_.val=(⟨name,small⟩ : Fin K).val+1:=by
      change key_.val=name+1
      simpa only [him,Option.map_some,DescentResetStemKey.code,Option.elim_some,short,name,Nat.add_assoc,
        Nat.add_comm,Nat.add_left_comm] using read
    rw [id,decoded_valid]
    have how : name/2=short.1 ∧ decide (name%2=1)=short.2 := by
      dsimp [name]
      rcases short with ⟨cell,flag⟩
      cases flag <;> simp [Nat.add_mod]; omega
    obtain ⟨fst,snd⟩:=how
    exact (localTemplate_read (Z) T (vertexCode) (center u).1 s name nonempty).trans (by
      rw [fst,snd]
      exact stem_table_names B u s slot j him)

private theorem coded_pair {S H : ℕ} (p : Fin H) (q : Fin S) (x : Fin (H*S)) (pair : Option (Fin S×Fin S)) :
    (∃u v,pair=some (u,v) ∧ ((q=u ∧ x=finProdFinEquiv (p,v)) ∨ (q=v ∧ x=finProdFinEquiv (p,u)))) ↔
      ∃z,pair.map (fun t=>((finProdFinEquiv (p,t.1)).val,(finProdFinEquiv (p,t.2)).val))=some z ∧
        eitherDirection (finProdFinEquiv (p,q)).val x.val z := by
  cases pair with
  | none=>simp
  | some data_ =>
    obtain ⟨a,b⟩:=data_
    simp only [Option.some.injEq,Prod.mk.injEq,Option.map_some]
    constructor
    · rintro ⟨_,_,⟨rfl,rfl⟩,left|right⟩
      · exact ⟨_,rfl,Or.inl ⟨congrArg (fun j=>(finProdFinEquiv (p,j)).val) left.1.symm,congrArg Fin.val left.2.symm⟩⟩
      · exact ⟨_,rfl,Or.inr ⟨congrArg (fun j=>(finProdFinEquiv (p,j)).val) right.1.symm,congrArg Fin.val right.2.symm⟩⟩
    · rintro ⟨_,rfl,edge⟩
      refine ⟨_,_,⟨rfl,rfl⟩,?_⟩
      rcases edge with l|rgt
      · exact Or.inl ⟨congrArg Prod.snd (finProdFinEquiv.injective (Fin.ext l.1.symm)),Fin.ext l.2.symm⟩
      · exact Or.inr ⟨congrArg Prod.snd (finProdFinEquiv.injective (Fin.ext rgt.1.symm)),Fin.ext rgt.2.symm⟩

variable {H D₀ a b : ℕ} (previous : Fintype.card input.V≤H) (peers : Fin H→Fin D₀→Option (Fin H))
local notation "padded" => (vertexCode).trans (Fin.castLEEmb previous)
local notation "named" => (Z).rawHostRank T padded
local notation "parts" => (Z).hostFields T padded

/-- A single scanner at the raw old-host/shape coordinate, before classification or
compaction, reports the other shape of precisely its retained signed stems. -/
theorem raw_slot_word (u : Host) (x : Fin (H*size)) (s : Bool) (slot : Slot) (key_ : Cell a)
    (read : key_.val=DescentResetStemKey.code ((oldStemAt B u s slot).map (stemTicket B s)))
    (room : (D₀+1)*size<2^b) :
    (∃j, Candidates.candidate peers (named u.1.2) j=some x ∧
      (DescentResetStemPeerChip.bits (tpl s) D₀ ((parts u.1.2).2) key_ : Cell b).val=j.val+1) ↔
    ∃e,oldStemAt B u s slot=some e ∧ eitherDirection (rank u.1.2).val x.val (stemPair B s e) := by
  let p:=(parts u.1.2).1
  let q:=(parts u.1.2).2
  change (∃j,Candidates.candidate peers (finProdFinEquiv (p,q)) j=some x ∧ _) ↔ _
  rw [raw_pair peers (tpl s) p q x key_ room,coded_pair p q x]
  have same:=(decoded_stem_pair B u s slot key_ read)
  change (decoded (tpl s) key_.val).map (fun z=>((finProdFinEquiv (p,z.1)).val,(finProdFinEquiv (p,z.2)).val))=_ at same
  rw [same]
  cases hit : oldStemAt B u s slot <;> simp; rfl

/-- Uniform incidence receipt for the native peer-directory union. The group and block
variables are simply the two factors of the true old common high coordinate. -/
theorem stem_ticket_evidence (v : B.next.V) (x : Fin (H*size))
    (keys : Host→Bool→Slot→Cell a)
    (source : ∀u s t,(keys u s t).val=DescentResetStemKey.code ((oldStemAt B u s t).map (stemTicket B s)))
    (room : (D₀+1)*size<2^b) :
    (∃u : Host, ∃s t j,u.1.2=v ∧ Candidates.candidate peers (named v) j=some x ∧
      (DescentResetStemPeerChip.bits (tpl s) D₀ (parts v).2 (keys u s t) : Cell b).val=j.val+1) ↔
      ∃e,rawPeer B (stemParent B e) (named v).val x.val := by
  change _ ↔ ∃e,rawPeer B (stemParent B e) (rank v).val x.val
  rw [←stem_raw_seen B v x.val]
  constructor
  · rintro ⟨u,s,t,j,at_,ed,signal⟩
    subst v
    obtain ⟨e,old,edge⟩:=(raw_slot_word B previous peers u x s t (keys u s t) (source u s t) room).1 ⟨j,ed,signal⟩
    exact ⟨u,s,t,e,rfl,old,edge⟩
  · rintro ⟨u,s,t,e,at_,old,edge⟩
    subst v
    obtain ⟨j,ed,signal⟩:=(raw_slot_word B previous peers u x s t (keys u s t) (source u s t) room).2 ⟨e,old,edge⟩
    exact ⟨u,s,t,j,rfl,ed,signal⟩

end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
