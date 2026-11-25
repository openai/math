import OAI.Hierarchy.DescentResetParentOriginHosts

namespace OAI
/-! # One genuine dyadic high coordinate for all installed roots at a receiver -/
noncomputable section
namespace Hierarchy.DescentSixParty.ClosedReset.Window
open DescentCompiler DescentColonies DescentSharedCableNames DescentParallelBase DescentChosenRouter
open scoped Classical
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {G : PoweredGadget F} {q ε : ℝ} {S : AtomSchedule} {k i z D n h C f g cut tail w hist : ℕ}
  {input : Reached W G q ε S k i z D w hist} {ctl : ResetRates G S k D n h C f g cut tail}
  (B : ClosedReset input ctl)
set_option quotPrecheck false
local notation "R" => B.reset.placement
local notation "Z" => B.reset
local notation "T" => B.terminals
local notation "vertex" => B.frame.host.symm.toEmbedding.trans input.vertex
local notation "birth" => DescentOrderedReset.grains W B.count B.order
local notation "coarse" => (Z).orderedReentry T birth
local notation "Host" => Stage.Host (Fin (S.groupCount (i+1))) B.next.V k
local notation "rows" => blocks B

/-- The original root used by the allocated terminal or base digit of each
nonstem instruction. The direct contact always uses its left socket. -/
def originSite (e : (coarse).graph.Edge) : Option (R).Site :=
  match motherNames B e with
  | .inl _=>none
  | .inr (.inl t)=>some (.inr t)
  | .inr (.inr (.inl c))=>some ((R).owner false c)
  | .inr (.inr (.inr ⟨(_,g₀),_⟩))=>some g₀

theorem originSite_host (e : (coarse).graph.Edge) :
    (originSite B e).map ((Z).rootVertex T)=originHost B e := by
  unfold originSite originHost
  rcases motherNames B e with j|t|c|⟨⟨s,g₀⟩,j⟩ <;> rfl

def originInterval : (R).Site→ℕ×ℕ
  | .inl g₀=>((R).b g₀.val.1,g₀.val.2.val)
  | .inr t=>((T).code t).2.1

theorem interval_block (a : (R).Site) :
    (originInterval B a).2/2^((originInterval B a).1-(T).commonDepth)=((Z).rootBlock T a).val := by
  cases a <;> rfl

theorem originInterval_legal (a : (R).Site) :
    (T).commonDepth≤(originInterval B a).1 ∧ (originInterval B a).1≤(Z).k ∧
      (originInterval B a).2<2^(originInterval B a).1 := by
  cases a with
  | inl g₀=>exact ⟨(T).commonLow g₀.val.1,(R).depth g₀.val.1,g₀.val.2.isLt⟩
  | inr t=>exact (T).codeLegal t

theorem contact_origin_block (u : Host) (c : (R).Contact)
    (atEnd : (rows).src (contactParent B c)=u ∨ (rows).dst (contactParent B c)=u) :
    (Z).rootBlock T ((R).owner false c)=(receiverRoot B u).2 := by
  rcases atEnd with left|right
  · have read:=contact_endpoint_root B c false
    change receiverRoot B ((rows).src (contactParent B c))=_ at read
    rw [left] at read
    exact (congrArg Prod.snd read).symm
  · have read:=contact_endpoint_root B c true
    change receiverRoot B ((rows).dst (contactParent B c))=_ at read
    rw [right] at read
    exact (Fin.ext ((T).coarseLinks c)).trans (congrArg Prod.snd read).symm

theorem trunk_center_block (u : Host) (t : (Z).Fallback)
    (atEnd : (rows).src (trunkParent B t)=u ∨ (rows).dst (trunkParent B t)=u) :
    (Z).rootBlock T (.inr t)=(receiverRoot B u).2 := by
  let e:=trunkParent B t
  have source : ((Z).blockId T ((coarse).graph.src e)).val=((Z).rootBlock T (.inr t)).val :=
    congrArg (fun a : ℕ×ℕ×ℕ×ℕ×ℕ×ℕ×Bool=>a.2.2.2.1) ((Z).trunkArchive T vertex birth t)
  obtain ⟨left,right⟩:=endpoint_root B e
  rcases atEnd with here|there
  · rw [here] at left
    exact (Fin.ext source).symm.trans (congrArg Prod.snd left).symm
  · rw [there] at right
    exact (Fin.ext source).symm.trans (((Z).block_edges T e).trans (congrArg Prod.snd right).symm)

theorem origin_site_block (u : Host) (e : (coarse).graph.Edge) (a : (R).Site)
    (atSite : (rows).src e=u ∨ (rows).dst e=u) (present : originSite B e=some a) :
    (Z).rootBlock T a=(receiverRoot B u).2 := by
  obtain ⟨tag,rfl⟩:=(motherNames B).symm.surjective e
  simp only [originSite,Equiv.apply_symm_apply] at present
  rcases tag with j|t|c|⟨⟨s,g₀⟩,j⟩
  · cases present
  · cases present
    exact trunk_center_block B u t atSite
  · cases present
    exact contact_origin_block B u c atSite
  · have same := (congrArg Prod.snd (private_owner B u ⟨(s,g₀),j⟩ atSite)).symm
    cases present
    exact same

theorem origin_interval_high (u : Host) (x : Local rows u) (a : (R).Site) (present : originSite B x.val=some a) :
    (originInterval B a).2/2^((originInterval B a).1-(T).commonDepth)=(receiverRoot B u).2.val :=
  (interval_block B a).trans (congrArg Fin.val (origin_site_block B u x.val a x.property.2 present))

theorem origin_intervals_same (u : Host) (x y : Local rows u) (a b : (R).Site)
    (left : originSite B x.val=some a) (right : originSite B y.val=some b) :
    (originInterval B a).2/2^((originInterval B a).1-(T).commonDepth)=
      (originInterval B b).2/2^((originInterval B b).1-(T).commonDepth) :=
  (origin_interval_high B u x a left).trans (origin_interval_high B u y b right).symm

end Hierarchy.DescentSixParty.ClosedReset.Window
end

end OAI
