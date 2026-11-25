import OAI.Hierarchy.DescentPackedTicketChronology
import OAI.Hierarchy.DescentSiteNameRead
import OAI.Hierarchy.DescentTerminalCableOrder

namespace OAI
/-! # A native order key for fine wires at a fixed unordered terminal pair -/
namespace Hierarchy.DescentTerminalPeerChronology
open DescentPacking DescentSixParty DescentCompiler DescentSharedCableNames DescentPackedTicketChronology
open DescentTerminalCableOrder DescentOrderedWords DescentChosenRouter DescentColonies Computability.BorderVNP.Crossing
open scoped Classical

/-- The sender's side in the canonical ordered pair of host numbers. -/
def side (first host : ℕ) := if first=host then 0 else 1

def cell (group first host block blockCount : ℕ) :=
  (group*2+side first host)*blockCount+block

def key (site cap outgoing within : ℕ) := (site*cap+outgoing)*cap+within

private theorem digit_eq {a b u v p : ℕ} (hu:u<p) (hv:v<p) :
    a*p+u=b*p+v ↔ a=b ∧ u=v := by
  have l:=digit_lt (a:=a) (b:=b) hu hv
  have r:=digit_lt (a:=b) (b:=a) hv hu
  omega

private theorem side_lt {lo hi a b : ℕ} (sorted:lo≤hi) (x:a=lo ∨ a=hi) (y:b=lo ∨ b=hi) :
    side lo a<side lo b ↔ a<b := by
  rcases x with hx | hx <;> rcases y with hy | hy <;>
    subst a <;> subst b <;> by_cases same : lo = hi <;> simp [side, same] <;> omega

private theorem side_eq {lo hi a b : ℕ} (sorted:lo≤hi) (x:a=lo ∨ a=hi) (y:b=lo ∨ b=hi) :
    side lo a=side lo b ↔ a=b := by
  have left:=side_lt sorted x y
  have right:=side_lt sorted y x
  omega

theorem cell_lt {g h u v a b H K lo hi : ℕ} (uRoom:u<H) (vRoom:v<H)
    (aRoom:a<K) (bRoom:b<K) (sorted:lo≤hi) (one:u=lo ∨ u=hi) (two:v=lo ∨ v=hi) :
    (g*H+u)*K+a<(h*H+v)*K+b ↔ cell g lo u a K<cell h lo v b K := by
  have us:side lo u<2:=by unfold side;split <;> omega
  have vs:side lo v<2:=by unfold side;split <;> omega
  simp only [cell,digit_lt aRoom bRoom,digit_lt uRoom vRoom,digit_eq uRoom vRoom,
    digit_lt us vs,digit_eq us vs,side_lt sorted one two,side_eq sorted one two]

theorem key_lt (left right : ℕ) {cap out₁ out₂ within₁ within₂ : ℕ}
    (a:out₁<cap) (b:out₂<cap) (c:within₁<cap) (d:within₂<cap) :
    key left cap out₁ within₁<key right cap out₂ within₂ ↔
      before left out₁ within₁ right out₂ within₂ := by
  simp only [key,DescentPackedTicketChronology.before,digit_lt c d,digit_lt a b,digit_eq a b]
  tauto

noncomputable section
variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V] {groups d k Hn : ℕ}
    {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F} {price ε:ℝ}
    (A : GroupStage W G price ε (Fin groups) V k)
    (hosts : V↪Fin Hn)
    {i : ℕ} (S : AtomSchedule) (ready : A.StateBounds S i)
    (native : W.graph.Edge↪Fin (Fintype.card W.graph.Edge))

def sender (lo : ℕ) (u : W.graph.Site) :=
  cell (A.pos u).1.val lo (hosts (A.pos u).2).val (A.block u).val (2^k)

/-- Original physical site IDs compare lexicographically in group, compact host and block.
The public host allocation can extend the dense earlier numbering. -/
def SiteOrder : Prop := ∀u v,originalId W.graph.Site u<originalId W.graph.Site v ↔
  ((A.pos u).1.val*Hn+(hosts (A.pos u).2).val)*2^k+(A.block u).val <
    ((A.pos v).1.val*Hn+(hosts (A.pos v).2).val)*2^k+(A.block v).val

theorem site_order (vertex : V↪Fin (Fintype.card V)) (agrees:∀v,(hosts v).val=(vertex v).val)
    (coord:Function.Injective (fun v=>(A.pos v,A.block v)))
    (named:∀v,originalId W.graph.Site v=(A.site vertex coord v).val) : SiteOrder A hosts := by
  intro u v
  rw [named,named]
  change DescentPhysicalOrder.physical (DescentSiteTape.rank (A.siteSlot vertex coord)) u<
    DescentPhysicalOrder.physical (DescentSiteTape.rank (A.siteSlot vertex coord)) v ↔ _
  rw [DescentPhysicalOrder.physical_lt_iff]
  change (A.siteSlot vertex coord u).val<(A.siteSlot vertex coord v).val ↔ _
  rw [A.siteSlot_val,A.siteSlot_val]
  simp only [digit_lt (A.block u).isLt (A.block v).isLt,
    digit_lt (vertex (A.pos u).2).isLt (vertex (A.pos v).2).isLt,
    digit_eq (vertex (A.pos u).2).isLt (vertex (A.pos v).2).isLt,
    digit_lt (hosts (A.pos u).2).isLt (hosts (A.pos v).2).isLt,
    digit_eq (hosts (A.pos u).2).isLt (hosts (A.pos v).2).isLt]
  simp only [agrees]

theorem sender_lt (named:SiteOrder A hosts) {lo hi : ℕ} (sorted:lo≤hi) (u v : W.graph.Site)
    (one:(hosts (A.pos u).2).val=lo ∨ (hosts (A.pos u).2).val=hi)
    (two:(hosts (A.pos v).2).val=lo ∨ (hosts (A.pos v).2).val=hi) :
    originalId W.graph.Site u<originalId W.graph.Site v ↔ sender A hosts lo u<sender A hosts lo v := by
  rw [named u v]
  exact cell_lt (hosts _).isLt (hosts _).isLt (A.block u).isLt (A.block v).isLt sorted one two

def grainKey (lo : ℕ) (z : Stage.Grain A) :=
  key (sender A hosts lo (W.graph.src z.1)) A.cap (outgoingSlot A S ready native z).val z.2.val

theorem grain_order (named:SiteOrder A hosts) (order:SourceSorted W native) {lo hi:ℕ} (ascending:lo≤hi) (x y:Stage.Grain A)
    (one:(hosts (A.pos (W.graph.src x.1)).2).val=lo ∨ (hosts (A.pos (W.graph.src x.1)).2).val=hi)
    (two:(hosts (A.pos (W.graph.src y.1)).2).val=lo ∨ (hosts (A.pos (W.graph.src y.1)).2).val=hi) :
    native x.1<native y.1 ∨ x.1=y.1 ∧ x.2.val<y.2.val ↔
      grainKey A hosts S ready native lo x<grainKey A hosts S ready native lo y := by
  have forward:=sender_lt A hosts named ascending _ _ one two
  have reverse:=sender_lt A hosts named ascending _ _ two one
  have same : originalId W.graph.Site (W.graph.src x.1)=originalId W.graph.Site (W.graph.src y.1) ↔
      sender A hosts lo (W.graph.src x.1)=sender A hosts lo (W.graph.src y.1) := by omega
  rw [←earlier_grain A native,actual_before A S ready native order]
  unfold grainKey
  rw [key_lt _ _ (outgoingSlot A S ready native x).isLt (outgoingSlot A S ready native y).isLt
    (x.2.isLt.trans_le (Stage.grain_room A (native.trans Fin.valEmbedding) S ready _))
    (y.2.isLt.trans_le (Stage.grain_room A (native.trans Fin.valEmbedding) S ready _))]
  simp only [DescentPackedTicketChronology.before,forward,same]

end
end Hierarchy.DescentTerminalPeerChronology

end OAI
