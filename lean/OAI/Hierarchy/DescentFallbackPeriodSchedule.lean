import OAI.Hierarchy.DescentFallbackPeriodBanks
import OAI.Hierarchy.DescentHostCountMask

namespace OAI
/-! # Shared count scan, per-group window gather, and private reset output in one memory -/
namespace Hierarchy.DescentFallbackPeriod
open DescentSIMDLookup DescentPackedZip DescentPackedPrivateMenu DescentPackedFallbackTree.Image
open DescentPackedColony DescentSharedLeafLookup DescentSharedBookScan DescentSharedCableNames.Stage
open DescentFallbackRankRAM DescentResetHostSize DescentPacking.PackedMatch.Local.Gather ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {D L cap n h r Ht l field H G M w : ℕ}

/-- The count directory is shared over all groups. Only true preceding physical source
columns accompany the public expression layout; the five device fields are computed here. -/
theorem run_banks (board : NonlinearExpanders.Graph n h) (C b width₀ : ℕ)
    (side : Bool) (ticket : Code r×Option (Fin (2^n))) (chart : Chart) (books : Header)
    (ports : Ports D) (here : Fin L→Expr) (tagged : Fin L→Bank) (sign : Fin L→Fin (2*cap)→Expr)
    (tabs : Fin (inputCount D L cap n r)→Tables) (menu : DescentSIMDLookup.Banks) (at₀ mid out : ℕ)
    (prior : Fin H→Fin G→Fin L→ℕ) (roster : Fin H→Fin D→Option (Fin H))
    (signs : Fin H→Fin G→Fin L→Fin (2*cap)→Option (Live D cap)) (m : Memory w) (pos : 0<M)
    (smallCount : Ht+2<w) (countBits : Ht+2≤field)
    (chartFits : (record chart H D (2^Ht) (Ht+2)).Fits w at₀)
    (totalFits : at₀+H*DescentSharedBookScan.width r (2^n) D<2^w) (rowBase : books.ranks.base=at₀)
    (sourceLow : ∀i,(here i).Fits w at₀) (signLow : ∀i z,(sign i z).Fits w at₀)
    (access : ∀i,Accessible ports (tagged i) H G M w at₀)
    (neighbors : Mounted ports roster m G M)
    (self : ∀i,Source (here i) (fun h g=>(prior h g i:Cell field)) M m)
    (peers : ∀i,Reads (tagged i) (fun h g=>((prior h g i+1:ℕ):Cell field)) M m)
    (realSigns : ∀i z,Source (sign i z) (fun h g=>((DescentSignedCableCodec.encode (signs h g i z)).val:Cell field)) M m)
    (reader : Readable books (DescentSharedBookScan.width r (2^n) D) H G M field w mid)
    (rConstants : Fixed books (DescentSharedBookScan.width r (2^n) D) H G M field m)
    (startLow : books.start.base+H*chunks G M≤at₀) (cutLow : books.cut.base+H*chunks G M≤at₀)
    (broadcastLow : books.broadcast.base+(M+1)*2^field≤at₀)
    (bounds : Bounds (w:=w) (d:=field) (M:=M) tabs
      (fun j=>operand (H:=H) ports books here tagged sign (number.symm j)) mid)
    (setLaw : ∀j,Static (tabs j) (setField (d:=field) j) M m)
    (shiftLow : ∀j,(tabs j).shift.base+2^((field*inputCount D L cap n r)*M)≤at₀)
    (lawLow : ∀j,(tabs j).apply.base+2^((field*inputCount D L cap n r+field)*M)≤at₀)
    (room : mid+H*chunks G M<2^w)
    (fit : Fits menu (field*inputCount D L cap n r)
      (fieldBits board r Ht (L*(2*cap)) l C b*(width₀*5)) M H G w out)
    (rom : resident (law board r Ht l C b width₀ side ticket (D:=D) (L:=L) (cap:=cap) (field:=field)) menu H G M m)
    (dictLow : menu.dictionary.base+2^((field*inputCount D L cap n r)*M)≤at₀)
    (maskLow : menu.mask.base+H*chunks G M≤at₀) (beforeMid : at₀≤ mid) (wired : menu.source.base=mid) :
    let N:=DescentSharedBookScan.width r (2^n) D
    let paid:=record chart H D (2^Ht) (Ht+2)
    let rows:=H*chunks G M
    let reads:=fun j=>operand (H:=H) (n:=n) (r:=r) ports books here tagged sign (number.symm j)
    let act:=assembly tabs reads
    let m₁:=image at₀ (H*N) paid m
    let dst:=imageBank H G M out menu (image mid rows act m₁)
    let xs:=inputs (field:=field) prior roster signs (fun u j=>(ranks (a:=r) (Y:=2^n) (D:=D) chart (2^Ht) (Ht+2) m u j).val)
    ((body chart H D (2^Ht) w (Ht+2) at₀ (H*N)).seq
      ((scan w mid rows act).seq (DescentSIMDLookup.program menu out H G M w))).Exec m dst
       ((4+H*N*(2*paid.work+4))+((4+rows*(2*act.work+4))+(4+44*rows))) ∧
    (∀a g (u : Fin width₀) (j : Fin 5),digit (fieldBits board r Ht (L*(2*cap)) l C b)
      (finProdFinEquiv (u,j)).val
      (digit (fieldBits board r Ht (L*(2*cap)) l C b*(width₀*5)) (lane g pos).val
        (dst (out+(row H G M (position a g pos)).val)).val)=
      values board r Ht (L*(2*cap)) l C b side u.val (key side ticket (xs a g)) j) ∧
    ∀z,(z<at₀ ∨ at₀+H*N≤z)→(z< mid ∨ mid+rows≤z)→(z<out ∨ out+rows≤z)→dst z=m z := by
  let N:=DescentSharedBookScan.width r (2^n) D
  let paid:=record chart H D (2^Ht) (Ht+2)
  let m₁:=image at₀ (H*N) paid m
  let rank:=ranks (a:=r) (Y:=2^n) (D:=D) (H:=H) chart (2^Ht) (Ht+2) m
  let xs:=inputs (field:=field) prior roster signs (fun h j=>(rank h j).val)
  let reads:=fun j=>operand (H:=H) (n:=n) (r:=r) ports books here tagged sign (number.symm j)
  have high (addr : ℕ) (below : addr<at₀) : m₁ addr=m addr :=
    ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (.inl below)
  have raw (e : Expr) (lo : e.Fits w at₀) (p : Row H G M) :
      e.eval m₁ ((row H G M p).val:Word w)=e.eval m ((row H G M p).val:Word w) :=
    eval_below e _ m m₁ lo high
  obtain ⟨pref,counts,frame⟩:=scalar_prefix (field:=field) chart books Ht H D r n at₀ m smallCount countBits chartFits totalFits rowBase
  have repeated : Fixed books N H G M field m₁ := by
    refine ⟨fun p=>?_,fun p=>?_,fun t x=>?_⟩
    · rw [high _ (by have:=(row H G M p).isLt;omega)]
      exact rConstants.start p
    · rw [high _ (by have:=(row H G M p).isLt;omega)]
      exact rConstants.cut p
    · have inside : repeatAddr t x<(M+1)*2^field := by
        exact (Nat.add_lt_add_left x.isLt _).trans_le (by rw [←Nat.succ_mul];exact Nat.mul_le_mul_right _ t.isLt)
      rw [high _ (by omega)]
      exact rConstants.broadcast t x
  have loaded : ∀j,Source (reads (number j)) (fun u g=>xs u g j) M m₁ := by
    intro j
    simp only [reads,Equiv.symm_apply_apply]
    rcases j with (i|⟨k,i⟩)|(⟨i,z⟩|j)
    · intro p;exact (raw _ (sourceLow i) p).trans (self i p)
    · have access₀:=access i
      have peerFits : (peerExpr ports (tagged i) H k).Fits w at₀ := by
        simp [peerExpr,neighborID,Expr.Fits,access₀.ids,access₀.roster,access₀.offsets,access₀.chunks,access₀.source]
      have earlier:=peerSource ports (tagged i) at₀ access₀ roster m neighbors _ (peers i) k
      have agree (v : Fin H) (g : Fin G) :
          (roster v k).elim (0:Cell field) (fun t=>((prior t g i+1:ℕ):Cell field))=xs v g (.inl (.inr (k,i))) := by
        cases hit:roster v k <;> simp [xs,inputs,hit]
      intro p
      exact (raw _ peerFits p).trans (by simpa only [agree] using earlier p)
    · intro p;exact (raw _ (signLow i z) p).trans (realSigns i z p)
    · exact repeated_source books mid m₁ reader repeated (fun h j=>((rank h j).val:Cell field)) counts j
  have sets : ∀j,Static (tabs j) (setField (d:=field) j) M m₁ := by
    intro j
    exact ⟨fun a=>(high _ (by have:=a.isLt;have:=shiftLow j;omega)).trans ((setLaw j).1 a),
      fun a=>(high _ (by have:=a.isLt;have:=lawLow j;omega)).trans ((setLaw j).2 a)⟩
  have fixed : resident (law board r Ht l C b width₀ side ticket (D:=D) (L:=L) (cap:=cap) (field:=field)) menu H G M m₁ :=
    ⟨fun j=>(high _ (by have:=j.isLt;omega)).trans (rom.1 j),
     fun j=>(high _ (by have:=j.isLt;omega)).trans (rom.2 j)⟩
  obtain ⟨scanRun,fieldReads,kept⟩:=run board C b width₀ side ticket tabs reads menu mid out xs pos m₁ bounds sets
    loaded room fit fixed (dictLow.trans beforeMid) (maskLow.trans beforeMid) wired
  exact ⟨pref.then scanRun,fieldReads,fun z a b c=>(kept z b c).trans (frame z a)⟩

end
end Hierarchy.DescentFallbackPeriod

end OAI
