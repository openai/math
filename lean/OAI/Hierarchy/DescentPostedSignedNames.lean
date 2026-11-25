import OAI.Hierarchy.DescentCalendarPreviousFields
import OAI.Hierarchy.DescentHostRosterOrder
import OAI.Hierarchy.DescentNamedStemSector
import OAI.Hierarchy.DescentDatedVenueSources

namespace OAI
/-! # The reset's compact and sparse successor labels produce the same physical signed word -/
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentDenseHostOrder DescentSIMDLookup DescentSharedCableNames
open DescentStageEdgeReceipt DescentPacking.PackedMatch.Local.Stage
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false

private theorem packed_lt (a b x y m : ℕ) (hx:x< m) (hy:y< m) :
    a*m+x<b*m+y ↔ a<b ∨ a=b ∧ x<y :=by
  rcases lt_trichotomy a b with low|same|high
  · have lim:=(Nat.mul_le_mul_right m low : (a+1)*m≤b*m)
    rw [Nat.succ_mul] at lim
    omega
  · subst b;simp
  · have lim:=(Nat.mul_le_mul_right m high : (b+1)*m≤a*m)
    rw [Nat.succ_mul] at lim
    omega

private theorem compact_lt {V : Type*} [Fintype V] (id : V↪ℕ) (x y : V) :
    (DescentRosterOrder.compact id x).val<(DescentRosterOrder.compact id y).val ↔ id x< id y :=by
  classical
  rw [DescentRosterOrder.compact_read,DescentRosterOrder.compact_read]
  have mono {x y : V} (lt : id x< id y) :
      (Finset.univ.filter (fun z=>id z< id x)).card<(Finset.univ.filter (fun z=>id z< id y)).card:=by
    apply Finset.card_lt_card
    refine (Finset.ssubset_iff_of_subset ?_).2 ⟨x,by simpa using lt,by simp⟩
    exact fun z mem=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,lt_trans (Finset.mem_filter.mp mem).2 lt⟩
  rcases lt_trichotomy (id x) (id y) with lo|equal|hi
  · exact iff_of_true (mono lo) lo
  · simp [equal]
  · exact iff_of_false (mono hi).not_gt hi.not_gt

private theorem packed_names {J V : Type} [Fintype J] [Fintype V] [DecidableEq J] [DecidableEq V] (k : ℕ)
    (j : J↪ℕ) (a b : V↪ℕ) (ranks : ∀x y,a x<a y ↔ b x<b y)
    (x y : Stage.Host J V k) :
    cableNames k (groupRank j a) x<cableNames k (groupRank j a) y ↔
      cableNames k (groupRank j b) x<cableNames k (groupRank j b) y :=by
  classical
  let idx (rank : V↪ℕ) :=groupRank j rank
  have bound (rank : V↪ℕ) (v : V) : rank v<pitch rank:=Nat.lt_succ_of_le (Finset.le_sup (Finset.mem_univ v))
  have first:(idx a) x.1<(idx a) y.1 ↔ (idx b) x.1<(idx b) y.1:=by
    change j x.1.1*pitch a+a x.1.2<j y.1.1*pitch a+a y.1.2 ↔
      j x.1.1*pitch b+b x.1.2<j y.1.1*pitch b+b y.1.2
    rw [packed_lt _ _ _ _ _ (bound a _) (bound a _),packed_lt _ _ _ _ _ (bound b _) (bound b _),ranks]
  have tie: (idx a) x.1=(idx a) y.1 ↔ (idx b) x.1=(idx b) y.1:=by simp
  change (idx a) x.1*2^k+x.2.val<(idx a) y.1*2^k+y.2.val ↔
    (idx b) x.1*2^k+x.2.val<(idx b) y.1*2^k+y.2.val
  rw [packed_lt _ _ _ _ _ x.2.isLt y.2.isLt,packed_lt _ _ _ _ _ x.2.isLt y.2.isLt,first,tie]

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail wire hist H : ℕ}
  {old : Reached W G q ε S k i z D wire hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset old ctl) (room : Fintype.card B.next.V≤H)
local notation "next" => B.next.placement
local notation "ord" => B.next.order.trans Fin.valEmbedding
local notation "host" => B.next.vertex.trans (Fin.castLEEmb room)
local notation "newID" => (host).trans Fin.valEmbedding
local notation "oldID" => (B.reset.rawHostRank B.terminals (B.frame.host.symm.toEmbedding.trans old.vertex)).trans Fin.valEmbedding
local notation "names" => cableNames k (groupRank (Fin.valEmbedding (n:=S.groupCount (i+1))) newID)
local notation "place" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k

theorem posted_signed_names (a b : place) : fieldNames B a<fieldNames B b ↔ names a<names b :=by
  apply packed_names
  intro v u
  exact (compact_lt oldID v u).symm

theorem posted_signed_panel (p : place) (j : Fin (2*(next).cap)) :
    Stage.signedPanel (next) ord S B.next.valid (fieldNames B) p j =
      Stage.signedPanel (next) ord S B.next.valid names p j :=by
  unfold Stage.signedPanel
  dsimp only
  split
  next hit=>
    apply congrArg some
    let q:=hit.choose
    let a:=Stage.ofPort (next) ord p q
    have nslot:(Stage.neighbors (next) ord (fieldNames B)).slot p a=(Stage.neighbors (next) ord names).slot p a:=by
      apply Fin.ext
      change (Ends.neighborOrder (Stage.near (next)) (fieldNames B) (Stage.near_room (next)) p _).val=
        (Ends.neighborOrder (Stage.near (next)) names (Stage.near_room (next)) p _).val
      rw [nb_val,nb_val]
      apply congrArg Finset.card
      ext x
      simp only [Finset.mem_filter,posted_signed_names B room]
    change Stage.live (next) ord S B.next.valid (fieldNames B) p q=Stage.live (next) ord S B.next.valid names p q
    exact congrArg (fun n=>{(Stage.live (next) ord S B.next.valid names p q) with neighbor:=n}) nslot
  next=>rfl

theorem posted_prepare_word (x : Block k) (j : Fin (2*(next).cap)) (h₀ : Fin H) (g₀ : Fin (S.groupCount (i+1))) :
    (rackOf B host h₀).bind (fun v=>Stage.signedPanel (next) ord S B.next.valid (fieldNames B) ((g₀,v),x) j)=
      Prepare.signed (next) ord S B.next.valid (Function.Embedding.refl _) host x j h₀ g₀ :=by
  classical
  unfold Prepare.signed Prepare.spreadField
  split
  next seen=>
    have h₁:seen.choose.1=g₀:=seen.choose_spec.1
    have h₂:host seen.choose.2=h₀:=seen.choose_spec.2
    have present:=rack_present B host seen.choose.2
    rw [h₂] at present
    rw [present]
    dsimp only [Option.bind]
    have atGroup : (g₀,seen.choose.2)=seen.choose := Prod.ext h₁.symm rfl
    exact (posted_signed_panel B room ((g₀,seen.choose.2),x) j).trans
      (congrArg (fun t : Fin (S.groupCount (i+1)) × B.next.V =>
        Stage.signedPanel (next) ord S B.next.valid names (t,x) j) atGroup)
  next absent=>
    have miss:∀v,host v≠h₀:=by
      intro v name;exact absent ⟨(g₀,v),rfl,name⟩
    rw [rack_missing B host h₀ miss]
    rfl
end
end Hierarchy.DescentSixParty.ClosedReset.Window

end OAI
