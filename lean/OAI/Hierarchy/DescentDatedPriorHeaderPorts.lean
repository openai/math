import OAI.Hierarchy.DescentDatedPriorHeaderReceipt

namespace OAI
/-! Shared prior geometry windows remain usable at each later physical
client, for either raw paths or deduplicated donor paths. -/
namespace Hierarchy.DescentDatedAddressBook.PriorHeader
open DescentSixParty.Chronology DescentHaloWalkRAM DescentPackedColony DescentSIMDLookup DescentDyadicSpan
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w H G M D:ℕ} (base:ℕ) (adj:Bank)
local notation "P"=>breadth D
local notation "N"=>H*P
local notation "J"=>H*(P*P)
local notation "n"=>H*chunks G M
local notation "top"=>endAddress H G M D base
local notation "old"=>ports H G M D base
local notation "visited₀"=>uniquePorts H G M D base
local notation "ranks₀"=>rankBanks H G M D base
local notation "out"=>image H G M D base adj
variable (ok:Room adj H G M D base w) (m:Memory w) (R:Fin H→Fin D→Option (Fin H))
  (initial:∀(v : Fin H) (j : Fin D),m (adj.base+v.val*D+j.val)=(number (R v j):Word w))
local notation "R₄"=>Gather.reaching R

include ok initial in
theorem mounted:Mounted old R₄ (out m) G M ∧ Mounted visited₀ (Gather.select R₄) (out m) G M:=by
  have caps:=limits H G M D
  have ids (p:Row H G M) (j:Fin P):
      out m (((old).ids j).base+(DescentSIMDLookup.row H G M p).val)=((p.1.val*P+j.val:ℕ):Word w):=by
    obtain ⟨h,c⟩:=p
    have value:=literal_word base adj ok m (13+j.val) (by have:=j.isLt;omega) (DescentSIMDLookup.row H G M (h,c)).val
      ((DescentSIMDLookup.row H G M (h,c)).isLt.trans_le caps.2.2.2.2)
    refine value.trans (congrArg (fun x : ℕ => (x : Word w)) ?_)
    change digits G M D (13+j.val) (finProdFinEquiv (h,c)).val = h.val*P+j.val
    rw [rect h c]
    simp (disch := omega) only [digits,ite_eq_right,dite_eq_right,quot,show 13+j.val-13=j.val by omega]
  have off (v:Fin H):out m ((old).offsets.base+v.val)=((chunks G M*v.val:ℕ):Word w):=by
    change out m ((bank H G M D base 11).base+v.val)=(digits G M D 11 v.val : Word w)
    exact literal_word base adj ok m 11 (by omega) v.val (v.isLt.trans_le caps.2.1)
  have chunk (p:Row H G M):out m ((old).chunks.base+(DescentSIMDLookup.row H G M p).val)=(p.2.val:Word w):=by
    obtain ⟨h,c⟩:=p
    have value:=literal_word base adj ok m 12 (by omega) (DescentSIMDLookup.row H G M (h,c)).val
      ((DescentSIMDLookup.row H G M (h,c)).isLt.trans_le caps.2.2.2.2)
    refine value.trans (congrArg (fun x : ℕ => (x : Word w)) ?_)
    change (finProdFinEquiv (h,c)).val % chunks G M = c.val
    rw [rect h c,rem h.val c]
  refine ⟨⟨ids,(four_words base adj ok m R initial).endpoints,off,chunk⟩,⟨ids,?_,off,chunk⟩⟩
  intro v j
  change out m ((visited H G M D base).base+(v.val*P+j.val))=
    (number (Gather.select R₄ v j) : Word w)
  simpa only [Ranks.id,rect] using visits base adj ok m R initial v j

theorem accessible_at (roof:top<2^w) (B:Bank) (stop:ℕ) (order:top≤ stop) (bank:B.Fits w stop) (size:n≤B.size):
    Accessible old B H G M w stop ∧ Accessible visited₀ B H G M w stop:=by
  have cap:=limits H G M D
  have f (i:ℕ) (lt:i<P+20):(PriorHeader.bank H G M D base i).Fits w stop:=by
    have old_:=at_bank H G M D base i _ lt roof
    exact ⟨old_.1,old_.2.1,old_.2.2.trans order⟩
  have ids (i:Fin P):=(f (13+i.val) (by have:=i.isLt;omega))
  exact ⟨⟨ids,fun _=>cap.2.2.2.2,f _ (by omega),cap.2.2.1,f _ (by omega),cap.2.1,
    f _ (by omega),cap.2.2.2.2,bank,size⟩,⟨ids,fun _=>cap.2.2.2.2,f _ (by omega),cap.2.2.1,
    f _ (by omega),cap.2.1,f _ (by omega),cap.2.2.2.2,bank,size⟩⟩

include ok in
theorem accessible (B:Bank) (stop:ℕ) (order:top≤ stop) (bank:B.Fits w stop) (size:n≤B.size):
    Accessible old B H G M w stop ∧ Accessible visited₀ B H G M w stop:=
  accessible_at (G:=G) (M:=M) (D:=D) base ok.roof B stop order bank size

include ok in
theorem rank_fits (stop:ℕ) (early:top≤ stop) (wide:stop+J<2^w):
    DescentOrdinaryDonorRankDirectory.Fits ranks₀ stop H P w:=by
  have c:=limits H G M D
  have f (i:ℕ) (lt:i<P+20):(bank H G M D base i).Fits w stop:=by
    have was:=at_bank H G M D base i _ lt ok.roof
    exact ⟨was.1,was.2.1,was.2.2.trans early⟩
  exact ⟨⟨f _ (by omega),f _ (by omega),f _ (by omega),f _ (by omega),c.2.2.1,c.2.2.2.1,c.2.2.2.1,c.2.1,ok.hosts,wide⟩,
    f _ (by omega),f _ (by omega),f _ (by omega),c.2.2.1,c.2.2.1,c.2.2.2.1⟩

end
end Hierarchy.DescentDatedAddressBook.PriorHeader

end OAI
