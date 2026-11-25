import OAI.Hierarchy.ProbeNativePacketRows
import OAI.Hierarchy.ProbeNativeBatchFunds
import OAI.Hierarchy.ProtocolRAMPortPadding

namespace OAI
/-! # Recover the chosen packet and all its signed width fields from a committed row -/

noncomputable section
namespace Hierarchy.ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM RepairHistogram AdaptiveProbe Calendar Calendar.StockCommit
open LinearAlgebra.SpectralBooks.ChordGraph
open ThreeFlat.Diagonal.MotifOuterTerms
open scoped Classical BigOperators Fin.CommRing

variable {F E A : Type*} [Field F] [Fintype E] [Fintype A] {k : ℕ} [Nonempty (Fin k)]
  {edge : E→Chord k} {req : A→E} {w d rows D extra : ℕ} {st : StockCommit} {mem : Memory w}

namespace Calendar.StockCommit.NativePacketRow
/-- A committed physical row already satisfies both the range and mass tests.
Thus the controller's histogram comes from decoding its field words. -/
def ofCommitted (P : Probe.Packet F edge req) (b : Batch (P.terms+extra) d)
    (layout : PortPlan st b mem rows) (j : Fin rows) (live : j∈liveRows b mem rows)
    (arity : (b.termCount.read mem (b.packet.eval mem (j.val:Word w))).val=P.terms)
    (ports : E ↪ Fin d)
    (entries : ∀e t,(layout.tabs (ports e) t).eval mem (j.val:Word w)=(padCounts P.count extra t e:Word w))
    (need : ∀e,((b.need (ports e)).eval mem (j.val:Word w)).val=debited req (b.copies*P.width) e)
    (unused : ∀v,(∀e,ports e≠v)→
      installedBits st.columns mem (layout.enum ⟨j,v⟩)=0 ∧ consumedBits st.columns mem (layout.enum ⟨j,v⟩)=0)
    (bound : ∀t e,P.count t e≤b.maxWidth) (fit : b.maxWidth<2^w) (wide : b.copies*b.maxWidth<2^w) :
    NativePacketRow P extra b layout j := by
  have active : committed b mem (j.val:Word w) := (Finset.mem_filter.mp live).2
  have decoded := decodeHistogram (n:=P.terms) (extra:=extra) (t:=b.copies) (fun t=>((b.field t).eval mem (j.val:Word w)).val) active.2.2
    (fun t=>by
      have lim:=active.2.1 (Fin.natAdd P.terms t)
      simpa [arity,Fin.val_natAdd] using lim)
  exact ⟨live,decoded.exists.choose,ports,fun t=>(decoded.exists.choose_spec t).symm,
    entries,need,unused,bound,fit,wide⟩

end Calendar.StockCommit.NativePacketRow
namespace StripDirectory
variable [Nonempty E] {box : Set (E→ℝ)} {ε tree : ℝ} {N digits : ℕ}

/-- ROM slots below the real selected alphabet contain the true single-copy
width, while all higher slots contain zero under the same native numbering. -/
theorem installedBits_pad (menu : Probe.FixedMenu F edge req box ε tree N) (i : menu.index)
    (e : E) (t : Fin ((menu.packet i).terms+extra)) :
    StripDirectory.installedBits menu i e t=padCounts (menu.packet i).count extra t e := by
  refine Fin.addCases (fun t=>?_) (fun t=>?_) t
  · simp [StripDirectory.installedBits,padCounts,t.isLt]
  · simp [StripDirectory.installedBits,padCounts,Fin.val_natAdd]

/-- Rebuild a true packet row for either strip geometry at the native common
role count D. Its only geometry-dependent inputs are its actual role
numbering and its installed coefficient-ROM expression. -/
def nativeRow (menu : Probe.FixedMenu F edge req box ε tree N) (i : menu.index) (test : StripTest digits)
    (terms codes enabled selectors stocks : Bank) (copies width : ℕ)
    (slot : Fin (Fintype.card E)→Option Expr) (roomD : Fintype.card E≤D)
    (mem : Memory w) (j : Fin rows) (st : StockCommit)
    (menuRoom : 1+Fintype.card menu.index≤2^w) (size : width<2^w) (full : copies*width<2^w)
    (needCap : ∀e,useBits menu i e≤width) (cap : ∀t e,(menu.packet i).count t e≤width) :
    let q:=(menu.packet i).terms+extra
    let fields:=(Fintype.equivFin E).symm
    let b:=batch (q:=q) menu test terms codes enabled selectors stocks .row copies width fields slot
    let pb:=PortPadding.batch D b
    ∀(layout : PortPlan st pb mem rows),
      layout.tabs=PortPadding.extend (wires menu b fields) (fun _=>.lit 0)→
      j∈liveRows pb mem rows→(pb.termCount.read mem (pb.packet.eval mem (j.val:Word w))).val=(menu.packet i).terms→
      (pb.packet.eval mem (j.val:Word w)).val=(Fintype.equivFin menu.index i).val+1 →
      NativePacketRow (menu.packet i) extra pb layout j := by
  intro q fields b pb layout table live arity hit
  let real : E ↪ Fin D := (Fintype.equivFin E).toEmbedding.trans (Fin.castLEEmb roomD)
  apply NativePacketRow.ofCommitted (menu.packet i) pb layout j live arity real _ _ _ cap size full
  · intro e t
    change (layout.tabs (PortPadding.inject roomD (Fintype.equivFin E e)) t).eval mem (j.val:Word w)=_
    rw [table,PortPadding.extend_real]
    have read:=(batch_entries (q:=q) menu test terms codes enabled selectors stocks .row copies width fields slot i
      mem (j.val:Word w) menuRoom (Fintype.equivFin E e) t hit).2
    simpa only [fields,Equiv.symm_apply_apply,installedBits_pad] using read
  · intro e
    change ((pb.need (PortPadding.inject roomD (Fintype.equivFin E e))).eval mem (j.val:Word w)).val=_
    rw [PortPadding.real_need]
    exact (batch_need (q:=q) menu test terms codes enabled selectors stocks .row copies width fields slot i
      (Fintype.equivFin E e) mem (j.val:Word w) menuRoom size (needCap _) full hit).trans
        (congrArg _ ((Fintype.equivFin E).symm_apply_apply e))
  · intro v unused
    have tail : Fintype.card E≤v.val := by
      by_contra! early
      let a : Fin (Fintype.card E) := ⟨v.val,early⟩
      apply unused ((Fintype.equivFin E).symm a)
      apply Fin.ext
      change ((Fintype.equivFin E) ((Fintype.equivFin E).symm a)).val = v.val
      rw [Equiv.apply_symm_apply]
    have take:=layout.read j v
    rw [take.1,take.2,table,PortPadding.wire b mem _ roomD size layout.termRoom layout.copyRoom layout.sumRoom,
      PortPadding.debit b mem _ roomD size layout.termRoom layout.copyRoom layout.sumRoom]
    simp [PortPadding.extend_tail _ _ _ tail]

end StripDirectory
end Hierarchy.ProtocolRAM
end

end OAI
