import OAI.Hierarchy.DescentPhysicalResetOriginalSeries

namespace OAI
/-! The three physical original-number passes write disjoint sectors of the same shelf. -/
open scoped Fin.CommRing
set_option quotPrecheck false

namespace Hierarchy.DescentResetNumberStem.Layout
open DescentResetOriginalSlots ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {X J K w : ℕ} (L : Layout X J K)

theorem other_slot (r : L.Room w) (m : Memory w) (x : Fin X) (j : Fin K)
    (missing : ∀t,L.shelf t≠j) (i : Fin L.rows) :
    let a:=offset L.original L.rows K x.val j.val+i.val
    L.image m a=m a:=by
  intro a
  have pos:L.original≤L.endAddress:=Nat.le_add_right ..
  have room:=r.separate.trans_lt (pos.trans_lt r.fits)
  obtain ⟨_,_,_,keep,_⟩:=DescentOperandPairBook.mounted L.laws L.M L.header m room
  exact (frame_slot L.shelf L.original L.rows L.term _ x j missing i).trans (keep a (.inr
    (r.separate.trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..)))))
end
end Hierarchy.DescentResetNumberStem.Layout

namespace Hierarchy.DescentResetOriginalSlots
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
theorem bank_at_word {w X K : ℕ} (base rows : ℕ) (x : Fin X) (j : Fin K) (i : Fin rows)
    (roof : finish base rows X K<2^w) (m : Memory w) :
    (.lookup (bank base rows K x.val j.val) .row:Expr).eval m (i.val:Word w)=
      m (offset base rows K x.val j.val+i.val):=by
  let n:=stride rows
  have before : x.val*K+j.val<X*K:=by
    have xn:=Nat.mul_le_mul_right K x.isLt
    rw [Nat.succ_mul] at xn
    omega
  have interval:=Nat.mul_le_mul_right n before
  rw [Nat.succ_mul] at interval
  have endAt : offset base rows K x.val j.val+n≤finish base rows X K:=by
    unfold offset finish
    change base+(x.val*K+j.val)*n+n≤base+X*K*n
    omega
  have fit : (bank base rows K x.val j.val).Fits w (finish base rows X K):=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt (endAt.trans_lt roof),endAt⟩
  exact bank_read _ m (i.isLt.trans_le (rows_le _)) fit

end Hierarchy.DescentResetOriginalSlots

namespace Hierarchy.DescentDatedAddressBook.CandidateSheets.OriginalInputs
open DescentPackedZip DescentSIMDLookup DescentResetOriginalSlots ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
noncomputable section
variable {s : CandidateSheets} {w : ℕ} (u : s.OriginalInputs) (base : ℕ)
local notation "P₀" => u.publicSide base
local notation "T₀" => u.stemSide base
local notation "A₀" => u.privateSide base
local notation "O" => s.original base
local notation "S₀" => s.stemFormatEnd base
local notation "publicImage" m:arg => (P₀).dst (u.prefixOutput base m)
local notation "stemImage" m:arg => (T₀).image (publicImage m)
local notation "slotsImage" m:arg => DescentUniformSlotOperands.result S₀ s.privates s.hosts s.groups s.lanes s.argBits (stemImage m)
local notation "slotRead" x:arg j:arg => (.lookup (bank O s.rows s.candidates (x).val (j).val) .row:Expr)

private theorem after_args (m : Memory w) (room : u.Room base w) (x : Fin s.blocks) (j : Fin s.candidates)
    (i : Fin s.rows) :
    let a:=offset O s.rows s.candidates x.val j.val+i.val
    (slotsImage m) a=(stemImage m) a:=by
  intro a
  have lim:s.privateArgsEnd base≤O:=Nat.le_add_right ..
  have roof:O≤ s.originalEnd base:=Nat.le_add_right ..
  have res:=DescentUniformSlotOperands.produce S₀ s.privates s.hosts s.groups s.lanes s.argBits
    (stemImage m) room.args (lim.trans_lt (roof.trans_lt room.private_.endFits))
  exact res.2.2.1 a (.inr (lim.trans ((Nat.le_add_right ..).trans (Nat.le_add_right ..))))

/-- The donor prefix is below every subsequent public, stem and private write. -/
theorem suffix_frame (m : Memory w) (room : u.Room base w) (i : ℕ) (low : i<s.inputDonorsEnd base) :
    u.output base m i=u.prefixOutput base m i:=by
  obtain ⟨a,b,c⟩:=room.pitches
  have below:=low.trans_le (a.trans b)
  have stop₀:s.privateArgsEnd base≤O:=Nat.le_add_right ..
  have stop₁:O≤ s.originalEnd base:=Nat.le_add_right ..
  have pub:=((P₀).any room.public_ (u.prefixOutput base m)).2.2 i (.inl low)
  have stem:=((T₀).any room.stem (publicImage m)).2.2 i (.inl (low.trans_le a))
  have slot:=(DescentUniformSlotOperands.produce S₀ s.privates s.hosts s.groups s.lanes s.argBits
    (stemImage m) room.args (stop₀.trans_lt (stop₁.trans_lt room.private_.endFits))).2.2.1 i (.inl below)
  have priv:=((A₀).any room.private_ (slotsImage m)).2.2 i (.inl (below.trans_le c))
    (fun p=>Or.inl ((below.trans_le (c.trans stop₀)).trans_le (Nat.le_add_right ..)))
  exact priv.trans (slot.trans (stem.trans pub))

/-- A preserved old read at the end of numbering also holds immediately after
the donor prefix, in the same packed row and lane convention. -/
theorem prefix_from_return {bits : ℕ} (m : Memory w) (room : u.Room base w) (op : Expr)
    (v : Fin s.hosts→Fin s.groups→Cell bits) (fit : op.Fits w (s.inputDonorsEnd base))
    (previousRead : Source op v s.lanes (u.output base m)) : Source op v s.lanes (u.prefixOutput base m):=by
  intro pos
  exact (eval_below op _ _ _ fit (fun i lo=>(u.suffix_frame base m room i lo).symm)).trans (previousRead pos)

/-- A public slot retains the preceding value across every stem, argument and private write. -/
theorem return_public {bits : ℕ} (m : Memory w) (room : u.Room base w)
    (x : Fin s.blocks) (j : Fin (s.contacts+1)) (value : Fin s.hosts→Fin s.groups→Cell bits)
    (separate : ∀t,u.stemShelf t≠u.publicShelf j) (privateOff : ∀t,u.privateShelf t≠u.publicShelf j)
    (posted : Source (slotRead x (u.publicShelf j)) value s.lanes (publicImage m)) :
    Source (slotRead x (u.publicShelf j)) value s.lanes (u.output base m):=by
  intro p
  let i:=row s.hosts s.groups s.lanes p
  let t:=u.publicShelf j
  have raw : ∀v:Memory w,(slotRead x t).eval v (i.val:Word w)=v (offset O s.rows s.candidates x.val t.val+i.val):=
    bank_at_word O s.rows x t i room.private_.endFits
  exact (raw _).trans (((A₀).frame_slot room.private_ (slotsImage m) x t privateOff i).trans
    ((after_args u base m room x t i).trans (((T₀).other_slot room.stem (publicImage m) x t separate i).trans
      ((raw _).symm.trans (posted p)))))

theorem return_stem {bits : ℕ} (m : Memory w) (room : u.Room base w)
    (x : Fin s.blocks) (j : Fin u.stems) (value : Fin s.hosts→Fin s.groups→Cell bits)
    (privateOff : ∀t,u.privateShelf t≠u.stemShelf j)
    (posted : Source (slotRead x (u.stemShelf j)) value s.lanes (stemImage m)) :
    Source (slotRead x (u.stemShelf j)) value s.lanes (u.output base m):=by
  intro p
  let i:=row s.hosts s.groups s.lanes p
  let t:=u.stemShelf j
  have raw : ∀v:Memory w,(slotRead x t).eval v (i.val:Word w)=v (offset O s.rows s.candidates x.val t.val+i.val):=
    bank_at_word O s.rows x t i room.private_.endFits
  exact (raw _).trans (((A₀).frame_slot room.private_ (slotsImage m) x t privateOff i).trans
    ((after_args u base m room x t i).trans ((raw _).symm.trans (posted p))))

end
end Hierarchy.DescentDatedAddressBook.CandidateSheets.OriginalInputs

end OAI
