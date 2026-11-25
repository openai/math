import OAI.Hierarchy.DescentTerminalFrozenRosterRAM

namespace OAI
/-! # The same stable cohort census feeds the local scalar arity and the pin lookup -/
namespace Hierarchy.DescentTerminalFrozenRoster
open DescentCensusRAM Computability.BorderVNP.FragmentBucket DescentTerminalPacketSlotRAM DescentTerminalExteriorPackets
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {w n H f:ℕ} (bank:Bank) (ord:ProtocolRAMEndpointSort.Layout) (m:Memory w) (alive:0<H)
local notation "mid" => sorted bank ord H n alive m
local notation "filled" => after ord n H mid

theorem count_read (fit:SortRoom bank ord w n H) (home:Fin n→Fin H)
    (source:∀u,bank.read m (u.val:Word w)=((home u).val:Word w)) (s:Fin H) :
    filled (ord.counts+s.val)=(count home s:Word w) := by
  have eqn : observed (n:=n) bank H m alive=home := by
    funext j;apply Fin.ext
    simp [observed,source,Fin.val_cast_of_lt ((home j).isLt.trans fit.height),(home j).isLt]
  have keep:ord.counts+s.val<out ord n H := by
    have a:=fit.fits.count_safe;have b:=fit.fits.prefix_safe
    unfold out
    have:=s.isLt;omega
  rw [show filled (ord.counts+s.val)=mid (ord.counts+s.val) from ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl keep)]
  unfold sorted
  rw [eqn]
  exact (buckets ord fit.fits home _ s).2

def fromSort (n H:ℕ) (ord:ProtocolRAMEndpointSort.Layout) (frozen off product:Bank) : Shelf :=
  ⟨DescentTerminalPacketSlotRAM.bank ord.sorted n,DescentTerminalPacketSlotRAM.bank ord.src n,
    DescentTerminalPacketSlotRAM.bank (out ord n H) n,frozen,off,product⟩

theorem old_from_sort (fit:SortRoom bank ord w n H) (space:out ord n H+n<2^w) (home:Fin n→Fin H)
    (frozen:Fin n→Fin (2^f)) (source:∀u,bank.read m (u.val:Word w)=((home u).val:Word w))
    (fbank offsets product:Bank) (static:∀u:Fin n,fbank.read filled (u.val:Word w)=((frozen u).val:Word w)) :
    Old home frozen (fromSort n H ord fbank offsets product) filled := by
  have eqn : observed (n:=n) bank H m alive=home := by
    funext j;apply Fin.ext
    simp [observed,source,Fin.val_cast_of_lt ((home j).isLt.trans fit.height),(home j).isLt]
  have a:=fit.fits.src_safe;have b:=fit.fits.count_safe;have c:=fit.fits.prefix_safe;have d:=fit.fits.room
  have span:n≤(DescentTerminalPacketSlotRAM.bank 0 n).size:=Nat.le_pow_clog (by decide) _
  have shelf (addr:ℕ) (u:Fin n) : (DescentTerminalPacketSlotRAM.bank addr n).read filled (u.val:Word w)=filled (addr+u.val):=by
    have inside : u.val<(DescentTerminalPacketSlotRAM.bank addr n).size := u.isLt.trans_le span
    change filled (addr+(u.val:Word w).val%(DescentTerminalPacketSlotRAM.bank addr n).size)=filled (addr+u.val)
    rw [Fin.val_cast_of_lt (by have hi:=u.isLt; omega : u.val<2^w),Nat.mod_eq_of_lt inside]
  have keep (a:ℕ) (before:a<out ord n H) : filled a=mid a:=
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl before)
  refine ⟨?_,?_,?_,static⟩
  · intro i
    change (DescentTerminalPacketSlotRAM.bank ord.sorted n).read filled _=_
    rw [shelf,keep _ (by unfold out;have:=i.isLt;omega)]
    unfold sorted
    rw [eqn]
    exact ProtocolRAMEndpointSort.read ord fit.fits home _ i
  · intro i
    change (DescentTerminalPacketSlotRAM.bank ord.src n).read filled _=_
    rw [shelf,keep _ (by unfold out;have:=i.isLt;omega)]
    unfold sorted;rw [eqn]
    rw [ProtocolRAMEndpointSort.frame _ fit.fits home _ _ (.inl (by have:=i.isLt;omega))
      (.inl (by have:=i.isLt;omega)) (.inl (by have:=i.isLt;omega))]
    simpa only [eqn] using guarded_keys bank ord H n m alive fit.height i
  · intro i
    change (DescentTerminalPacketSlotRAM.bank (out ord n H) n).read filled _=_
    rw [shelf];exact (truthful_slot bank ord m alive fit home source i).1

theorem published_counts (fit:SortRoom bank ord w n H) (space:out ord n H+n<2^w)
    (home:Fin n→Fin H) (frozen:Fin n→Fin (2^f))
    (source:∀u,bank.read m (u.val:Word w)=((home u).val:Word w))
    (S:Banks w n (H+1)) (K:ℕ) (cap:∀s,count home s≤K)
    (fbank offsets product:Bank) (static:∀u:Fin n,fbank.read filled (u.val:Word w)=((frozen u).val:Word w))
    (before:ord.counts+H≤S.first)
    (lits:Literals f K (fromSort n H ord fbank offsets product) filled)
    (kf:(tag (fromSort n H ord fbank offsets product) S.bins H).Fits w S.first)
    (vf:(value (fromSort n H ord fbank offsets product)).Fits w S.first) :
    let L:=fromSort n H ord fbank offsets product
    ∃out_,(program S L).Exec filled out_ (tallyCost S (tag L S.bins H) (value L)) ∧
      (∀s:Fin H,out_ (S.bins+s.val)=((book home frozen s).val:Word w) ∧ out_ (ord.counts+s.val)=(count home s:Word w)) ∧
      ∀a<S.first,out_ a=filled a := by
  have old:=old_from_sort bank ord m alive fit space home frozen source fbank offsets product static
  obtain ⟨final,run,books,frame⟩:=published S _ filled kf vf home frozen K cap old lits
  exact ⟨final,run,fun s=>⟨books s,(frame _ (by have:=s.isLt;omega)).trans (count_read bank ord m alive fit home source s)⟩,frame⟩

end
end Hierarchy.DescentTerminalFrozenRoster

end OAI
