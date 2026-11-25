import OAI.Hierarchy.DescentPackedChildNeighborMachine

namespace OAI
/-! # Native two-stage peer lookup on the compact successor roster -/
namespace Hierarchy.DescentOrdinaryCompactPeer
open DescentPackedChildNeighbor DescentHaloWalkRAM DescentSIMDLookup
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
open private DescentPackedChildNeighbor.find_at DescentPackedChildNeighbor.at_index DescentPackedChildNeighbor.previous_le
  DescentPackedChildNeighbor.index_fit DescentPackedChildNeighbor.find_fit from OAI.Hierarchy.DescentPackedChildNeighborMachine
noncomputable section
variable {N H L Q D w : ℕ}
abbrev Key (H L Q : ℕ) := Fin H × (Fin L × Fin Q)
def index (H L Q : ℕ) : Key H L Q ≃ Fin (H*(L*Q)) :=
  ((Equiv.refl _).prodCongr finProdFinEquiv).trans finProdFinEquiv

def value (ends : Fin N→Fin L→Option (Fin N)) (roster : Fin H→Fin D→Option (Fin H))
    (pitch : ℕ) (old : Fin N) (h : Fin H) (ticket : Fin L) (low : Fin Q) : ℕ :=
  let other:=previous ends old ticket
  if other=N then D else search (fun j=>number (roster h j)) Fin.val (other*pitch+low.val) D (List.finRange D)

/-- The outer guard omits padded successor rows that have no corresponding prior rack. -/
def expr (B : DescentPackedChildNeighbor.Banks) (live : Bank) (N L D : ℕ) : Expr :=
  .branch .eq (.lookup live .row) (.lit 0) (.lit D) (DescentPackedChildNeighbor.body B N L D)

theorem work (B : DescentPackedChildNeighbor.Banks) (live : Bank) (N L D : ℕ) :
    (expr B live N L D).work=15+36*L+D*(30+36*L) := by
  change 7+1+1+(DescentPackedChildNeighbor.body B N L D).work+1=_
  rw [DescentPackedChildNeighbor.work]
  omega

structure Room (B : DescentPackedChildNeighbor.Banks) (live : Bank) (N H L Q D pitch w out : ℕ) : Prop where
  shapes : ∀b∈[live,B.oldOffset,B.ticket,B.low,B.newOffset],b.Fits w out ∧ H*(L*Q)≤b.size
  ranks : B.ranks.Fits w out ∧ N*L≤B.ranks.size
  ends : B.endpoints.Fits w out ∧ N*L≤B.endpoints.size
  roster : B.roster.Fits w out ∧ H*D≤B.roster.size
  scale : B.timesPitch.Fits w out ∧ N≤B.timesPitch.size
  priorFit : N<2^w
  hostFit : H<2^w
  ticketFit : L<2^w
  targetFit : ∀u : Fin N,∀g : Fin Q,u.val*pitch+g.val<2^w
  last : out+H*(L*Q)<2^w
  wordPos : 0<w

structure Mounted (B : DescentPackedChildNeighbor.Banks) (live : Bank) (pitch : ℕ) (rack : Fin H→Option (Fin N))
    (endAt : Fin N→Fin L→Option (Fin N)) (roster : Fin H→Fin D→Option (Fin H)) (m : Memory w) : Prop where
  active : ∀z : Key H L Q,m (live.base+(index H L Q z).val)=(((rack z.1).isSome.toNat:ℕ):Word w)
  old : ∀z : Key H L Q,∀v,rack z.1=some v→m (B.oldOffset.base+(index H L Q z).val)=((v.val*L:ℕ):Word w)
  query : ∀z : Key H L Q,m (B.ticket.base+(index H L Q z).val)=(z.2.1.val:Word w)
  lower : ∀z : Key H L Q,m (B.low.base+(index H L Q z).val)=(z.2.2.val:Word w)
  current : ∀z : Key H L Q,m (B.newOffset.base+(index H L Q z).val)=((z.1.val*D:ℕ):Word w)
  cost : ∀v : Fin N,m (B.timesPitch.base+v.val)=((v.val*pitch:ℕ):Word w)
  prior : ∀v j,m (B.ranks.base+(v.val*L+j.val))=(rank endAt v j:Word w)
  finish : ∀v j,m (B.endpoints.base+(v.val*L+j.val))=(number (endAt v j):Word w)
  neighbors : ∀v j,m (B.roster.base+(v.val*D+j.val))=(number (roster v j):Word w)

theorem eval_live (B : DescentPackedChildNeighbor.Banks) (live : Bank) (pitch out : ℕ) (rack : Fin H→Option (Fin N))
    (ok : Room B live N H L Q D pitch w out) (ends : Fin N→Fin L→Option (Fin N))
    (roster : Fin H→Fin D→Option (Fin H)) (m : Memory w) (present : Mounted (Q:=Q) B live pitch rack ends roster m)
    (z : Key H L Q) (v : Fin N) (occupied : rack z.1=some v) :
    (DescentPackedChildNeighbor.body B N L D).eval m ((index H L Q z).val:Word w)=(value ends roster pitch v z.1 z.2.1 z.2.2:Word w) := by
  let i:=index H L Q z
  let here:=z.1
  let t:=z.2.1
  let low:=z.2.2
  have cold:=ok.shapes B.oldOffset (by simp);have cur:=ok.shapes B.newOffset (by simp)
  have query:=ok.shapes B.ticket (by simp);have lo:=ok.shapes B.low (by simp)
  have readRank (j : Fin L) :=(DescentPackedChildNeighbor.at_index B.ranks B.oldOffset ok.ranks.1 cold.1 v j i.val (i.isLt.trans_le cold.2) ok.ranks.2 m (present.old z v occupied)).trans (present.prior v j)
  have readEnd (j : Fin L) :=(DescentPackedChildNeighbor.at_index B.endpoints B.oldOffset ok.ends.1 cold.1 v j i.val (i.isLt.trans_le cold.2) ok.ends.2 m (present.old z v occupied)).trans (present.finish v j)
  have test : B.ticket.read m (i.val:Word w)=(t.val:Word w):=(DescentPackedZip.bank_read _ _ (i.isLt.trans_le query.2) query.1).trans (present.query z)
  have short (j : Fin L) : rank ends v j<2^w:=(Ranks.bound _ _ _).trans ok.ticketFit
  have lower := DescentPackedChildNeighbor.find_at (fun j : Fin L => atIndex B.ranks B.oldOffset j.val)
    (fun j : Fin L => atIndex B.endpoints B.oldOffset j.val)
    (.lookup B.ticket .row) N t.val (rank ends v) (fun j => number (ends v j)) m
    (i.val : Word w) test (t.isLt.trans ok.ticketFit) readRank short readEnd (List.finRange L)
  change (prev B N L).eval m (i.val : Word w)=(previous ends v t : Word w) at lower
  have le := DescentPackedChildNeighbor.previous_le ends v t
  have eqn : (previous ends v t : Word w)=(N : Word w) ↔ previous ends v t=N := by
    rw [Fin.ext_iff,Fin.val_cast_of_lt (le.trans_lt ok.priorFit),Fin.val_cast_of_lt ok.priorFit]
  have flag : DescriptorExpr.Comparison.eq.test ((prev B N L).eval m (i.val : Word w)) (N : Word w)=true ↔
      previous ends v t=N := by
    rw [lower]
    simpa only [DescriptorExpr.Comparison.test,beq_iff_eq] using eqn
  let item := Expr.op .add (.lookup B.timesPitch (prev B N L)) (.lookup B.low .row)
  let candidate := findWord (fun j : Fin D => atIndex B.roster B.newOffset j.val) (fun j => .lit j.val)
    item D (List.finRange D)
  change (if DescriptorExpr.Comparison.eq.test ((prev B N L).eval m (i.val : Word w)) (N : Word w)
      then (D : Word w) else candidate.eval m (i.val : Word w)) =
    (((if previous ends v t=N then D else search (fun j => number (roster here j)) Fin.val
      (previous ends v t*pitch+low.val) D (List.finRange D)) : ℕ) : Word w)
  by_cases empty : previous ends v t=N
  · rw [ite_eq_left (flag.mpr empty),ite_eq_left empty]
  · rw [ite_eq_right (fun hit => empty (flag.mp hit)),ite_eq_right empty]
    let u : Fin N := ⟨previous ends v t,lt_of_le_of_ne le empty⟩
    have mul : B.timesPitch.read m (u.val:Word w)=((u.val*pitch:ℕ):Word w):=(DescentPackedZip.bank_read _ _ (u.isLt.trans_le ok.scale.2) ok.scale.1).trans (present.cost u)
    have rest : B.low.read m (i.val:Word w)=(low.val:Word w):=(DescentPackedZip.bank_read _ _ (i.isLt.trans_le lo.2) lo.1).trans (present.lower z)
    have target : item.eval m (i.val:Word w)=((u.val*pitch+low.val:ℕ):Word w):=by
      change (B.timesPitch.read m ((prev B N L).eval m (i.val:Word w)))+(B.low.read m (i.val:Word w))=_
      rw [lower,mul,rest,Nat.cast_add]
    have bound : u.val*pitch+low.val<2^w:=ok.targetFit u low
    have rd (j : Fin D) : (atIndex B.roster B.newOffset j.val).eval m (i.val:Word w)=(number (roster here j):Word w) := (DescentPackedChildNeighbor.at_index B.roster B.newOffset ok.roster.1 cur.1 here j i.val (i.isLt.trans_le cur.2) ok.roster.2 m (present.current z)).trans (present.neighbors here j)
    have noWrap (j : Fin D) : number (roster here j)<2^w:=by cases hj:roster here j with | none=>exact ok.hostFit | some a=>exact a.isLt.trans ok.hostFit
    exact DescentPackedChildNeighbor.find_at (fun j : Fin D => atIndex B.roster B.newOffset j.val) (fun j => .lit j.val)
      item D (u.val*pitch+low.val) (fun j => number (roster here j)) Fin.val m (i.val : Word w)
      target bound rd noWrap (fun _ => rfl) (List.finRange D)

theorem fits (B : DescentPackedChildNeighbor.Banks) (live : Bank) (pitch out : ℕ) (ok : Room B live N H L Q D pitch w out) :
    (expr B live N L D).Fits w out := by
  have b:=ok.shapes B.oldOffset (by simp);have query:=ok.shapes B.ticket (by simp);have l:=ok.shapes B.low (by simp);have curr:=ok.shapes B.newOffset (by simp)
  have old : (prev B N L).Fits w out :=
    DescentPackedChildNeighbor.find_fit (fun i : Fin L => atIndex B.ranks B.oldOffset i.val)
      (fun i : Fin L => atIndex B.endpoints B.oldOffset i.val) (.lookup B.ticket .row) N out
      (fun i => DescentPackedChildNeighbor.index_fit _ _ i.val out ok.ranks.1 b.1) (fun i => DescentPackedChildNeighbor.index_fit _ _ i.val out ok.ends.1 b.1)
      ⟨query.1,trivial⟩ (List.finRange L)
  let target := Expr.op .add (.lookup B.timesPitch (prev B N L)) (.lookup B.low .row)
  have targetFits : target.Fits w out := ⟨⟨ok.scale.1,old⟩,l.1,trivial⟩
  have base : (DescentPackedChildNeighbor.body B N L D).Fits w out := ⟨old,trivial,trivial,DescentPackedChildNeighbor.find_fit (fun j : Fin D => atIndex B.roster B.newOffset j.val)
    (fun j : Fin D => .lit j.val) target D out
    (fun j => DescentPackedChildNeighbor.index_fit _ _ j.val out ok.roster.1 curr.1) (fun _ => trivial) targetFits (List.finRange D)⟩

  exact ⟨⟨(ok.shapes live (by simp)).1,trivial⟩,trivial,trivial,base⟩

theorem eval (B : DescentPackedChildNeighbor.Banks) (live : Bank) (pitch out : ℕ) (rack : Fin H→Option (Fin N))
    (ok : Room B live N H L Q D pitch w out) (ends : Fin N→Fin L→Option (Fin N)) (roster : Fin H→Fin D→Option (Fin H))
    (m : Memory w) (present : Mounted (Q:=Q) B live pitch rack ends roster m) (z : Key H L Q) :
    (expr B live N L D).eval m ((index H L Q z).val:Word w)=
       ((rack z.1).elim D (fun v=>value ends roster pitch v z.1 z.2.1 z.2.2):Word w) := by
  let i:=index H L Q z
  have active : live.read m (i.val : Word w) = (((rack z.1).isSome.toNat : ℕ) : Word w) :=
    (DescentPackedZip.bank_read _ m (i.isLt.trans_le (ok.shapes live (by simp)).2)
    (ok.shapes live (by simp)).1).trans (present.active z)
  change (if DescriptorExpr.Comparison.eq.test (live.read m (i.val : Word w)) ((0 : ℕ) : Word w)
    then (D : Word w) else (DescentPackedChildNeighbor.body B N L D).eval m (i.val : Word w)) = _
  rw [active]
  cases h:rack z.1 with
  | none => simp [DescriptorExpr.Comparison.test]
  | some v=>
    have one:(1:Word w)≠0:=by
      apply Fin.ne_of_val_ne
      have wide : 1 < 2^w := Nat.one_lt_two_pow_iff.mpr (Nat.ne_of_gt ok.wordPos)
      change 1 % (2^w) ≠ 0
      rw [Nat.mod_eq_of_lt wide]
      decide
    have rd:=eval_live B live pitch out rack ok ends roster m present z v h
    simpa [h, DescriptorExpr.Comparison.test, one, i] using rd

theorem run (B : DescentPackedChildNeighbor.Banks) (live : Bank) (pitch out : ℕ) (rack : Fin H→Option (Fin N))
    (ok : Room B live N H L Q D pitch w out) (ends : Fin N→Fin L→Option (Fin N)) (roster : Fin H→Fin D→Option (Fin H))
    (m : Memory w) (present : Mounted (Q:=Q) B live pitch rack ends roster m) :
    let op:=expr B live N L D
    let n:=H*(L*Q)
    let done:=image out n op m
    (scan w out n op).Exec m done (4+n*(2*op.work+4)) ∧
      (∀z : Key H L Q,done (out+(index H L Q z).val)=
        ((rack z.1).elim D (fun v=>value ends roster pitch v z.1 z.2.1 z.2.2):Word w)) ∧
      (∀p,p<out ∨ out+n≤p→done p=m p) ∧ CheapCode (scan w out n op) := by
  refine ⟨scan_exec _ _ _ _ (fits B live pitch out ok) ok.last,?_,?_,?_⟩
  · intro z
    apply (ProtocolRAMGeneratedWrite.read_image _ _ _ _ (index H L Q z)).trans
    exact eval B live pitch out rack ok ends roster m present z
  · exact fun p hp=>ProtocolRAMGeneratedWrite.frame_image _ _ _ _ p hp
  · exact @scan_cheap _ _ _ _

end
end Hierarchy.DescentOrdinaryCompactPeer

end OAI
