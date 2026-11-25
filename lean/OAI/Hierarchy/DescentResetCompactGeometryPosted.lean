import OAI.Hierarchy.DescentResetCompactGeometryPhase

namespace OAI
/-! # Both signed-root scalar observations are available on the final compact geometry state -/
namespace Hierarchy.DescentResetCompactGeometry.Chart
open DescentSIMDLookup DescentPackedZip ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {w : ℕ} (C : Chart)

def onHost {N : ℕ} (v : Fin N→Cell C.bits) (h : Fin C.hosts) : Cell C.bits:=if l:h.val<N then v ⟨_,l⟩ else 0

theorem posted (r : C.Room w) (m : Memory w) (N : ℕ) (name : Fin N→Fin C.raw) (root : Fin N→Fin C.oldHosts)
    (shape : Fin N→Cell C.bits) (self : Fin C.oldHosts→Cell C.bits) (hn : N≤C.hosts)
    (inv : ∀i,m (C.inverse.base+i.val)=((name i).val:Word w)) (count : m C.count.base=(N:Word w))
    (ranked : ∀i,m (C.ranks.base+i.val)=((self i).val:Word w))
    (extent : N≤C.inverse.size) (ranks : C.oldHosts≤C.ranks.size)
    (oldHost : ∀j,(name j).val/C.shapes=(root j).val) (rawShape : ∀j,(name j).val%C.shapes=(shape j).val) :
    let actual : Fin 2→Fin C.hosts→Cell C.bits:=fun t=>if t=0 then C.onHost shape else C.onHost (fun i=>self (root i))
    ∀t,(C.port t).Fits w C.top ∧ Source (C.port t) (fun h (_ : Fin C.groups)=>actual t h) C.lanes (C.finalMem m):=by
  intro actual
  have end_ : C.broadcast+C.size<2^w:=C.cut r
  have selfEnd : C.self.base+C.hosts≤C.broadcast:=(Nat.add_le_add_left r.selfRows _).trans r.selfBank.2.2
  have small : C.self.base+C.hosts<2^w:=selfEnd.trans_lt ((Nat.le_add_right ..).trans_lt end_)
  have head : stop C.geometry C.hosts<2^w:=r.selfAfter.trans_lt ((Nat.le_add_right ..).trans_lt small)
  have observed:=DescentResetCompactGeometry.read C.inverse C.count C.base C.raw C.shapes C.geometry C.hosts m N name hn count inv
    r.here r.cnt extent r.header head
  have lower:=(DescentResetCompactGeometry.any C.inverse C.count C.base C.raw C.shapes C.geometry C.hosts m r.here r.cnt r.header head).2.2
  have early : C.base≤C.self.base:=(Nat.le_add_right ..).trans (r.header.trans ((Nat.le_add_right ..).trans r.selfAfter))
  have original (B : Bank) (fit : B.Fits w C.base) : B.Fits w C.self.base:=⟨fit.1,fit.2.1,fit.2.2.trans early⟩
  have oldCount:C.first m C.count.base=(N:Word w):=(lower _ (.inl (by have :=r.cnt.1;have :=r.cnt.2.2;omega))).trans count
  have oldRank (j : Fin C.oldHosts):C.first m (C.ranks.base+j.val)=((self j).val:Word w):=
    (lower _ (.inl (by have hi:=j.isLt;have :=r.ranks.2.2;omega))).trans (ranked j)
  have owner (i : Fin N) : C.first m ((output C.geometry C.hosts 1).base+i.val)=((root i).val:Word w):=by
    simpa [first,value,i.isLt,oldHost] using observed (i.castLE hn) 1
  have ready:=pull_self C.count (output C.geometry C.hosts 1) C.ranks C.self.base (C.first m) N C.oldHosts root self oldCount owner oldRank
    (original _ r.cnt) (C.shelf r 1) (original _ r.ranks) (hn.trans (DescentResetOriginalSlots.rows_le C.hosts)) ranks hn small
  have bank (t : Fin 2) : (C.choose t).Fits w C.broadcast:=by
    by_cases h:t=0
    · have q:=C.shelf r 0
      simp only [choose,ite_eq_left h]
      exact ⟨q.1,q.2.1,q.2.2.trans ((Nat.le_add_right ..).trans selfEnd)⟩
    · simpa [choose,h] using r.selfBank
  have enough (t : Fin 2) : C.hosts≤(C.choose t).size:=by
    by_cases h:t=0
    · simp only [choose,ite_eq_left h];exact DescentResetOriginalSlots.rows_le C.hosts
    · simpa [choose,h] using r.selfRows
  have held (t : Fin 2) (h : Fin C.hosts) : C.second m ((C.choose t).base+h.val)=((actual t h).val:Word w):=by
    by_cases yes:t=0
    · subst t
      have safe:=(C.shelf r 0).2.2
      have inside:h.val<(output C.geometry C.hosts 0).size:=h.isLt.trans_le (DescentResetOriginalSlots.rows_le C.hosts)
      have kept : C.second m ((output C.geometry C.hosts 0).base+h.val)=
          C.first m ((output C.geometry C.hosts 0).base+h.val) := by
        simpa only [second,pull] using
          ready.2.2.1 ((output C.geometry C.hosts 0).base+h.val) (.inl (by omega))
      rw [show C.choose 0=output C.geometry C.hosts 0 from rfl,kept]
      by_cases l:h.val<N <;>
        simpa [first,actual,onHost,value,l,rawShape] using observed h 0
    · have got:=ready.2.1 h
      by_cases l:h.val<N <;>simpa [second,pull,actual,onHost,choose,yes,l] using got
  have both := DescentResetCompactGeometry.broadcast (G:=C.groups) (M:=C.lanes)
    C.choose actual C.broadcast (C.second m) bank enough held r.broad
  intro t
  refine ⟨DescentResetHaloBroadcast.schema_fit (C.choose t) C.broadcast C.hosts C.groups
    C.lanes C.bits (bank t) r.broad,?_⟩
  simpa only [port,finalMem,lit,size] using both.2.1 t

end
end Hierarchy.DescentResetCompactGeometry.Chart

end OAI
