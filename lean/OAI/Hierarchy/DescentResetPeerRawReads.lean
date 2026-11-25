import OAI.Hierarchy.DescentResetPeerRawTables

namespace OAI
/-! # Simultaneous lane readback from consecutive raw peer evidence mounts -/
namespace Hierarchy.DescentResetPeerUnionRAM.RawTables
open DescentSIMDLookup DescentPackedColony DescentDenseHostOrder DescentDyadicSpan ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure Computability.VPVNP.BurstRAM PrivateRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {n h K w : ℕ} (board : NonlinearExpanders.Graph n h) (r depth : ℕ)
variable (L : Layout) (templ : Bool→Fin K→Option (Fin L.shapes×Fin L.shapes))
local notation "H" => L.hosts
local notation "W" => L.shapes
local notation "M" => L.lanes
local notation "G" => L.groups
local notation "P" => L.privateSlots
local notation "b" => L.privateBits
local notation "a" => L.keyBits
local notation "d" => L.ticketBits
local notation "D" => L.degree

def ReadsAt {l : ℕ} (val : Fin (H*W)→Fin G→Cell l) (at_ : Fin (chunks G M)→Expr) (m : Memory w) :=
  ∀c (v : Fin (H*W)),(at_ c).eval m (v.val:Word w)=((data («M»:=M) val (v,c)).val:Word w)

theorem reads_before {l : ℕ} (val : Fin (H*W)→Fin G→Cell l) (at_ : Fin (chunks G M)→Expr)
    {bound : ℕ} {before after : Memory w} (fit : ∀c,(at_ c).Fits w bound)
    (stable : ∀i,i < bound → after i=before i) (old : ReadsAt L val at_ before) :
    ReadsAt L val at_ after := by
  intro c v
  exact (eval_below _ _ before after (fit c) stable).trans (old c v)

theorem retained {bound : ℕ} (m : Memory w) (prior : bound ≤ L.first) :
    ∀i,i < bound → image board r depth L templ m i=image₀ L m i := by
  intro i hi
  obtain ⟨_,b₁,b₂,_⟩:=L.bounds
  have h₁:=hi.trans_le prior
  exact (frame₃ board r depth L templ m i (.inl ((h₁.trans_le b₁).trans_le b₂))).trans
    ((frame₂ L templ m i (.inl (h₁.trans_le b₁))).trans (frame₁ L templ m i (.inl h₁)))

theorem private_reads (m : Memory w) (room : L.endAddress < 2^w) (bank : Bank)
    (val : Fin H→Fin G→Cell (b*(P*5))) (low : bank.Fits w L.base) (size : H*chunks G M ≤ bank.size)
    (old : Reads bank val M m) (slot : Fin P) :
    let output:=fun c : Fin (chunks G M)=>PrivateEvidence.operand L.base H W P b M bank slot c.val
    (∀c,(output c).Fits w L.endAddress) ∧ ReadsAt L (fun v g=>
      let q:=finProdFinEquiv.symm v
      PrivateEvidence.word D W b P d q.2 slot (val q.1 g)) output (image board r depth L templ m) := by
  intro output
  obtain ⟨_,t,u,v⟩:=L.bounds
  have later:=(t.trans u).trans v
  have issued:=(PrivateEvidence.run L.base H W D P b M d G m (later.trans_lt room)).2.2.2.2 bank val low size old
  have saved (c) : (output c).Fits w L.first:=(issued slot c).1
  refine ⟨fun c=>ProtocolRAMGeneratedWrite.fits_mono _ later (saved c),?_⟩
  exact reads_before L _ output saved (retained board r depth L templ m le_rfl) (fun c v=>(issued slot c).2 v)

def stemAddress (side : Bool) := if side then L.second else L.first
def stemOperand (side : Bool) (src : Expr) :=
  DescentResetStemPeerChip.dataExpr W (stemAddress L side) H a M src

theorem stem_after_private (m : Memory w) (room : L.endAddress < 2^w) (side : Bool)
    (src : Fin (chunks G M)→Expr) (val : Fin (H*W)→Fin G→Cell a)
    (old : ReadsAt L val src (image₀ L m)) (early : ∀c,(src c).Fits w L.first) :
    let output:=fun c=>stemOperand L side (src c)
    (∀c,(output c).Fits w L.endAddress) ∧ ReadsAt L (fun v g=>
       (DescentResetStemPeerChip.bits (templ side) D
         ((finProdFinEquiv.symm v : Fin H×Fin W).2) (val v g):Cell d))
         output (image board r depth L templ m) := by
  intro output
  obtain ⟨x,y,z,t⟩:=L.bounds
  cases side with
  | false=>
    have mid:=DescentResetStemPeerChip.run (templ false) L.first src (image₀ L m) val old
      early («b»:=d) («D»:=D) (by
        change L.first+span (H*W)+span (W*2^(a*M)) < 2^w
        simpa only [Layout.second,Layout.stemWords,Nat.add_assoc] using (z.trans t).trans_lt room)
    have fit (c) : (output c).Fits w L.second := by
      simpa only [output,stemOperand,stemAddress,Bool.false_eq_true,ite_false,Layout.second,Layout.stemWords,
        DescentResetStemPeerChip.endAddress,DescentResetStemPeerChip.start,Nat.add_assoc] using mid.2.1 c
    refine ⟨fun c=>ProtocolRAMGeneratedWrite.fits_mono _ (z.trans t) (fit c),?_⟩
    refine reads_before L _ output fit (before:=image₁ L templ m) ?_ mid.2.2.1
    intro i hi
    exact (frame₃ board r depth L templ m i (.inl (hi.trans_le z))).trans (frame₂ L templ m i (.inl hi))
  | true=>
    have old₁:=reads_before L val src early (fun i hi=>frame₁ L templ m i (.inl hi)) old
    have mid:=DescentResetStemPeerChip.run (templ true) L.second src (image₁ L templ m) val old₁
      (fun c=>ProtocolRAMGeneratedWrite.fits_mono _ y (early c)) («b»:=d) («D»:=D) (by
        change L.second+span (H*W)+span (W*2^(a*M)) < 2^w
        simpa only [Layout.trunk,Layout.stemWords,Nat.add_assoc] using t.trans_lt room)
    have fit (c) : (output c).Fits w L.trunk := by
      simpa only [output,stemOperand,stemAddress,ite_true,Layout.trunk,Layout.stemWords,
        DescentResetStemPeerChip.endAddress,DescentResetStemPeerChip.start,Nat.add_assoc] using mid.2.1 c
    refine ⟨fun c=>ProtocolRAMGeneratedWrite.fits_mono _ t (fit c),?_⟩
    exact reads_before L _ output fit (fun i hi=>frame₃ board r depth L templ m i (.inl hi)) mid.2.2.1

theorem trunk_reads (m : Memory w) (room : L.endAddress < 2^w) (shape : W=(roster board r depth).card)
    (src : Fin (chunks G M)→Expr) (val : Fin (H*(roster board r depth).card)→Fin G→Cell 1)
    (old : ∀c (v : Fin (H*(roster board r depth).card)),(src c).eval m (v.val:Word w)=((data («M»:=M) val (v,c)).val:Word w))
    (early : ∀c,(src c).Fits w L.base) :
    let output:=fun c=>DescentResetTrunkChip.dataExpr board r depth L.trunk H M (src c)
    (∀c,(output c).Fits w L.endAddress) ∧
    ∀c (v : Fin (H*(roster board r depth).card)),(output c).eval (image board r depth L templ m) (v.val:Word w)=
      ((data («M»:=M) (fun v g=>(DescentResetTrunkChip.bits board r depth D
         ((finProdFinEquiv.symm v : Fin H×Fin (roster board r depth).card).2) (val v g):Cell d)) (v,c)).val:Word w) := by
  intro output
  obtain ⟨x,y,z,t⟩:=L.bounds
  have prev (j) (hj : j < L.base) : image₂ L templ m j=m j :=
    (frame₂ L templ m j (.inl (hj.trans_le (x.trans y)))).trans
      ((frame₁ L templ m j (.inl (hj.trans_le x))).trans (frame₀ L m j (.inl hj)))
  have mid:=DescentResetTrunkChip.run board r depth L.trunk src (image₂ L templ m) val
    (fun c v=>(eval_below _ _ _ _ (early c) prev).trans (old c v))
    (fun c=>ProtocolRAMGeneratedWrite.fits_mono _ ((x.trans y).trans z) (early c)) («D»:=D) («b»:=d) (by
      simpa only [Layout.endAddress,Layout.trunkWords,shape,DescentResetTrunkChip.endAddress,
        DescentResetTrunkChip.start,Nat.add_assoc] using room)
  constructor
  · intro c
    simpa only [Layout.endAddress,Layout.trunkWords,shape,DescentResetTrunkChip.endAddress,
      DescentResetTrunkChip.start,Nat.add_assoc] using mid.2.1 c
  · simpa only [image,DescentResetTrunkChip.memory,Layout.trunkWords,shape] using mid.2.2.1

end
end Hierarchy.DescentResetPeerUnionRAM.RawTables

end OAI
