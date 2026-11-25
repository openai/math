import OAI.Hierarchy.DescentPreparedRotorInputs
import OAI.Hierarchy.DescentPreparedFallbackRanks
import OAI.Hierarchy.DescentContactSenderRead

namespace OAI
/-! # Original sender operands at the attained reset root memory -/
namespace Hierarchy.DescentFallbackPeriod.Projected
open DescentResetReciprocalPeer DescentSharedLeafLookup DescentSharedBookScan DescentSIMDLookup DescentPackedColony DescentPackedZip
open DescentSixParty.Chronology DescentResetHostSize DescentContactSenderDate DescentRotorWindowArchive
open DescentIssuedTerminalId
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {D L cap N n r c H G K R M h l t b Ht w : ℕ}

namespace RootSources
variable (src : RootSources D L cap)

/-- The immutable repeat dictionary also supplies a constant one with a zero-padded final group. -/
def ones (book : Header) : Expr := .lookup book.broadcast (.op .add (.lookup book.cut .row) (.lit 1))

private def senderMatrix (hosts : ℕ) : DescentRotorWindowArchive.Input D L cap → Expr
  | .inl (.inl (.inl i)) => .lookup (src.here i) .row
  | .inl (.inl (.inr (j,i))) => peerExpr src.peers (src.tagged i) hosts j
  | .inl (.inr (i,j)) => .lookup (src.signed i j) .row
  | .inr (.inl (i,j)) => src.oldOrder i j
  | .inr (.inr (p,j,f)) => src.reservation p j f

private theorem senderMatrix_eq (source : RootSources D (2^r) cap) (hosts : ℕ)
    (i : DescentRotorWindowArchive.Input D (2^r) cap) :
    senderMatrix source hosts i=source.matrixFields hosts i := by
  rcases i with (((i|⟨j,i⟩)|⟨i,j⟩)|(⟨i,j⟩|⟨p,j,f⟩)) <;> rfl

def senderPrior (H n r : ℕ) (oldId : Bank) (book : Header) : Prior D L cap n r :=
  ⟨fun i=>(finSumFinEquiv.symm i).elim (fun j=>senderMatrix src H (DescentRotorWindowArchive.ix.symm j)) (DescentSharedLeafLookup.source book),
    src.peers,src.signed,.lookup oldId .row,ones book⟩

def senderWords (matrix : Fin H→Fin G→Fin (DescentRotorWindowArchive.count D L cap)→Cell b)
    (rank : Fin H→Fin (width r (2^n) D)→Cell b) (h : Fin H) (g : Fin G) (j : Fin (DescentOldContactSender.count D L cap n r)) :=
  (finSumFinEquiv.symm j).elim (matrix h g) (rank h)

theorem sender_decode (matrix : Fin H→Fin G→Fin (DescentRotorWindowArchive.count D L cap)→Cell b)
    (rank : Fin H→Fin (width r (2^n) D)→Cell b) (h : Fin H) (g : Fin G) :
    DescentOldContactSender.decode (senderWords matrix rank h g)=(fun i=>matrix h g (DescentRotorWindowArchive.ix i),rank h) := by
  apply Prod.ext <;>funext j <;>simp [senderWords,DescentOldContactSender.decode]

theorem ones_read {out N : ℕ} (m : Memory w) (hdr : Header) (space : Readable hdr N H G M b w out)
    (fixed : Fixed hdr N H G M b m) (wide : 0<b) :
    Source (ones hdr) (fun (_ : Fin H) (_ : Fin G)=>(1:Cell b)) M m := by
  intro p
  let pos : Word w:=(row H G M p).val
  have read:= (lookup_nat _ m pos .row _ rfl ((row H G M p).isLt.trans_le space.cuts) (space.fit _ (by simp)).2.1).trans (fixed.cut p)
  have one : (1:Cell b).val=1:=Fin.val_cast_of_lt (Nat.one_lt_two_pow wide.ne')
  have small : repeatAddr (usedRow p) (1:Cell b)<(M+1)*2^b :=
    (Nat.add_lt_add_left (1:Cell b).isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ (usedRow p).isLt)
  have literal:=fixed.broadcast (usedRow p) (1:Cell b)
  rw [repeater (fun _=>(1:Cell b))] at literal
  apply (lookup_nat _ m pos _ (repeatAddr (usedRow p) (1:Cell b)) _ (small.trans_le space.repeats)
    (space.fit _ (by simp)).2.1).trans literal
  change (Expr.lookup hdr.cut .row).eval m pos+(1:Word w)=_
  rw [read,repeatAddr,one,Nat.cast_add,Nat.cast_one]

end RootSources
namespace Receiver
variable (a : Receiver D cap N n r c H G K R M h l t b Ht w) (book : RootBook n r D (2^r) cap b)
local notation "groups" => 2^c
local notation "cnt" => width r (2^n) D
local notation "arena" => RootTemplates.arena (a.headerEnd book) H groups M r n D
variable (space : a.PreparedFits book) (m : Memory w) (root : Code r×Option (Fin (2^n)))
local notation "pg" => ((false,.inr root):RootPage r (2^n))
local notation "rid" => (rootIndex r (2^n) pg).val
local notation "hdr" => book.rankHeader a.projectionEnd H groups M pg
local notation "dst" => a.preparedImage book space m
local notation "mid" => a.preparedMid book space m
local notation "rank" => fun (u : Fin H) (j : Fin cnt)=>((ranks (a:=r) (Y:=2^n) (D:=D) (book.common a.projectionEnd H) (2^Ht) (Ht+2) mid u j).val:Cell b)

/-- Both later gathers for this fallback job start strictly above its scalar rank page.
The disjoint root schedule leaves that page available to the donor phase. -/
theorem final_rank_words (low : Ht+2<w) (size : Ht+2≤b) (u : Fin H) (j : Fin cnt) :
    dst ((hdr).ranks.base+(u.val*cnt+j.val))=((rank u j).val:Word w) := by
  let z:=(arena).first rid+(u.val*cnt+j.val)
  have index : u.val*cnt+j.val<H*cnt := (Nat.add_lt_add_left j.isLt _).trans_le
    (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ u.isLt)
  have first : (arena).first rid≤z:=Nat.le_add_right ..
  have below : z<(arena).middle rid:= (Nat.add_lt_add_left index _).trans_le (Nat.add_le_add_left (RootArena.le_span _) _)
  have last : z<(arena).output rid:=below.trans_le (Nat.le_add_right ..)
  have all:=a.prepared_root book space m pg z ((min_le_left ..).trans first)
    (below.trans_le ((Nat.le_add_right ..).trans ((le_max_left ..).trans (le_max_right ..))))
  change dst z=_
  rw [all]
  exact (ProtocolRAMGeneratedWrite.frame_image _ _ _ _ z (Or.inl last)).trans
    ((ProtocolRAMGeneratedWrite.frame_image _ _ _ _ z (Or.inl below)).trans
      (a.fallback_rank_words book space m false root low size u j))

theorem final_sender_prior (src : RootSources D (2^r) cap) (oldId : Bank)
    (matrix : Fin H→Fin groups→Fin (DescentRotorWindowArchive.count D (2^r) cap)→Cell b)
    (next : Adj H D) (raw : Fin (2^r)→Fin (2*cap)→Fin H→Fin groups→Cell b)
    (low : Ht+2<w) (wide : Ht+2≤b)
    (oldMatrix : ∀i,Source (src.matrixRow H i) (fun h g=>matrix h g i) M dst)
    (oldSign : ∀x j,Reads (src.signed x j) (raw x j) M dst)
    (routes : Mounted src.peers next dst groups M)
    (idFit : oldId.Fits w a.origin) (idRoom : H*chunks groups M≤oldId.size)
    (oldName : ∀p : Row H groups M,m (oldId.base+(row H groups M p).val)=(p.1.val:Word w)) (start : ℕ) :
    (Layout.mk start H groups M : Layout D (2^r) cap n r Ht b).Before (src.senderPrior H n r oldId hdr)
      (RootSources.senderWords matrix rank) next raw dst := by
  have read:=(a.fallback_rank_fixed book space m false root).2
  have fixed:=(a.prepared_shared_final book space m pg).2.2
  refine ⟨?_,routes,oldSign,?_,RootSources.ones_read dst hdr read fixed (by omega)⟩
  · intro j
    obtain ⟨j,rfl⟩:=finSumFinEquiv.surjective j
    cases j with
    | inl i=>simpa only [RootSources.senderPrior,RootSources.senderWords,Equiv.symm_apply_apply,Sum.elim_inl,
        RootSources.senderMatrix_eq,RootSources.matrixRow] using oldMatrix i
    | inr i=>
      have known:=repeated_source hdr _ dst read fixed rank (a.final_rank_words book space m root low wide) i
      simpa only [RootSources.senderPrior,RootSources.senderWords,Equiv.symm_apply_apply,Sum.elim_inr] using known
  · intro p
    have seen:=((a.prepared_any book space m).2.2 _ (.inl ((Nat.add_lt_add_left ((row H groups M p).isLt.trans_le idRoom) _).trans_le idFit.2.2))).trans (oldName p)
    exact (bank_read _ _ ((row H groups M p).isLt.trans_le idRoom) idFit).trans seen

end Receiver
end
end Hierarchy.DescentFallbackPeriod.Projected

end OAI
