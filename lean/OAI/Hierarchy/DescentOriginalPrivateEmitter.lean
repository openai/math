import OAI.Hierarchy.DescentOriginalSectorRetention
import OAI.Hierarchy.DescentResetOriginalPosted

namespace OAI
/-! The actual private chronology table with retained metadata, self rank and the printed slot address. -/
namespace Hierarchy.DescentDatedAddressBook.CandidateSheets.OriginalInputs
open DescentPackedZip DescentSIMDLookup DescentResetFieldAssembler DescentResetOriginalSlots
open DescentResetPublicParentWord DescentResetMixedWordRAM OriginalDate ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open scoped Fin.CommRing
noncomputable section
set_option quotPrecheck false
variable {s : CandidateSheets} {w : ℕ} (u : s.OriginalInputs) (base : ℕ)
local notation "O" => s.original base
local notation "S₀" => s.stemFormatEnd base
local notation "P₀" => u.publicSide base
local notation "T₀" => u.stemSide base
local notation "A₀" => u.privateSide base
local notation "prefix_" m => u.prefixOutput base m
local notation "published" m => (P₀).dst (prefix_ m)
local notation "rooted" m => (T₀).image (published m)
local notation "end_" m => DescentUniformSlotOperands.result S₀ s.privates s.hosts s.groups s.lanes s.argBits (rooted m)
local notation "cut_" => s.inputDonorsEnd base

theorem private_operand_read {b : ℕ} (room : u.Room base w) (m : Memory w)
    (op : Expr) (values : Fin s.hosts→Fin s.groups→Cell b) (fit : op.Fits w cut_)
    (seen : Source op values s.lanes (prefix_ m)) : Source op values s.lanes (end_ m):=by
  have lp:=room.pitches
  have public_:=((P₀).any room.public_ (prefix_ m)).2.2
  have stem:=((T₀).any room.stem (published m)).2.2
  have aa:s.privateArgsEnd base≤O:=Nat.le_add_right ..
  have bb:O≤ s.originalEnd base:=Nat.le_add_right ..
  have args:=DescentUniformSlotOperands.produce S₀ s.privates s.hosts s.groups s.lanes s.argBits
    (rooted m) room.args (aa.trans_lt (bb.trans_lt room.private_.endFits))
  intro pos
  exact (eval_below _ _ _ _ fit (fun i lo=>(args.2.2.1 i (.inl (lo.trans_le (lp.1.trans lp.2.1)))).trans
    ((stem i (.inl (lo.trans_le lp.1))).trans (public_ i (.inl lo))))).trans (seen pos)

theorem private_number_at (room : u.Room base w) (m : Memory w) (x : Fin s.blocks) (j : Fin s.privates)
    (value : Fin s.hosts→Fin s.groups→Meta) (zero : Fin s.hosts→Fin s.groups→Bool)
    (rank : Fin s.hosts→Fin s.groups→Cell s.haloBits)
    (mb : 0<s.metaBits) (zb : 0<s.zeroBits)
    (mfit : (u.privateMeta x j).Fits w cut_) (zfit : (u.zero x).Fits w cut_) (hfit : (u.halo x).Fits w cut_)
    («meta» : Source (u.privateMeta x j) (fun v g=>raw s.metaBits (value v g)) s.lanes (prefix_ m))
    (zs : Source (u.zero x) (fun v g=>((zero v g).toNat:Cell s.zeroBits)) s.lanes (prefix_ m))
    (hs : Source (u.halo x) rank s.lanes (prefix_ m)) :
    Source (.lookup (bank O s.rows s.candidates x.val (u.privateShelf j).val) .row)
      (fun v g=>(privateWord u.geometry (value v g).live.toNat (zero v g).toNat (rank v g).val j.val:Cell u.resultBits))
      s.lanes (u.output base m):=by
  have aa:s.privateArgsEnd base≤O:=Nat.le_add_right ..
  have bb:O≤ s.originalEnd base:=Nat.le_add_right ..
  have args:=DescentUniformSlotOperands.produce S₀ s.privates s.hosts s.groups s.lanes s.argBits
    (rooted m) room.args (aa.trans_lt (bb.trans_lt room.private_.endFits))
  have fm:=private_operand_read u base room m _ _ mfit «meta»
  have fz:=private_operand_read u base room m _ _ zfit zs
  have fh:=private_operand_read u base room m _ _ hfit hs
  have read:=(A₀).posted room.private_ (end_ m) x j rfl value zero rank (fun _ _=>(j.val:Cell s.argBits))
    mb zb rfl (by simpa only [privateSide, Equiv.symm_apply_apply] using fm) (by
      simp only [privateSide, Equiv.symm_apply_apply]
      convert fz using 1
      funext host grp
      apply Fin.ext
      rfl)
    (by simpa only [privateSide, Equiv.symm_apply_apply] using fh) (by simpa only [privateSide, Equiv.symm_apply_apply] using args.2.1 j)
  change Source _ _ s.lanes ((A₀).dst (end_ m))
  simp only [privateSide, Date.output, Fin.val_cast_of_lt (j.isLt.trans_le room.args)] at read ⊢
  convert read using 1
  funext host grp
  apply Fin.ext
  rfl

end
end Hierarchy.DescentDatedAddressBook.CandidateSheets.OriginalInputs

end OAI
