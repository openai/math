import OAI.Optimization.LinearProgramming.Geometry.BorderPacket
import OAI.Optimization.LinearProgramming.Geometry.MinorQuery

/-! One live, relocatable call to the compressed-minor service with complete scalar-word
accounting and the geometric memory frame, for arbitrary initial interactive history. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch

open RAM RAM.Block Matrix Compression Contract OracleSpec Contraction.Machine OracleSegments

variable {r s n k : ℕ}

/-- The physically emitted program includes the ordinary packet writer and one query instruction. -/
def submit : Segment := (Segment.core packetBlock).seq (.query 80 81 82 83)

/-- Serialize the actual minor and perform its request, preserving the raw signed tape,
the packed output prefix and the selected candidate. -/
theorem submit_runs (m : Memory ℚ) (P : ℚ → Prop) (o : ScalarOracle ℚ) (history : Contract.History ℚ)
    (D : Matrix (Fin r) (Fin n) ℚ) (E : Matrix (Fin s) (Fin n) ℚ) (J : Fin k → Fin n) (j : Fin n)
    (hr : k+1 ≤ r) (hrn : r ≤ n) (raw : circuitMinor (D.submatrix (Fin.castLE hr) id) J j ≠ 0)
    (base : ℕ) (hk : m.index 128=k) (hn : m.index 130=n) (hj : m.index 90=j.val)
    (hp : m.index 144=base) (hbase : 256 ≤ base) (hpiv : 128 ≤ m.index 136)
    (hJ : ∀ i : Fin k, m.index (m.index 136+i.val)=(J i).val) (hm : ∀ a,P (m.data a))
    (hnum : ∀ a ≤ n,P (a:ℚ)) (hz : P 0) (ho : P 1) (A : ℚ → Prop) (hAP : ∀q,A q → P q)
    (responds : Responds D E A o) :
    ∃ ans : Option ℚ, ∃ t cost, cost ≤ 6*k+31+n*(8*k+16)+2*n ∧
      Runs submit o (fun u => ∀ a,P (u.data a)) m history cost t
        ((keyPacket D E (prefixMinorKey J j),reply ans)::history) ∧ ExchangeOutput m t ans base ∧
      (∀ q, ans=some q → A q) := by
  obtain ⟨b,c,hc,eb,bo⟩ := packetBlock_eval m P J j base hk hn hj hp hbase hpiv hJ (hr.trans hrn) hm hnum
  obtain ⟨u,ukey,uw⟩ := prefixWords_spec D E hr J j raw
  let index := interfaceIndex D E u
  have key : keyPacket D E (prefixMinorKey J j)=packet index.val := by simp [keyPacket,ukey,index]
  have source : sentPacket b 80 81=packet index.val := by
    change registerPacket (b.atPC 0) 80 81=(MinorLog.words _).map Nat.cast
    rw [uw,bo.message]
  obtain ⟨ans,t,d,hd,er,out,qa⟩ := send_query b P A o history D E index source base bo.destination eb.safe_end hz ho hAP responds
  refine ⟨ans,t,c+d,by omega,?_,?_,qa⟩
  · rw [key]; exact (Runs.core eb o history).seq er
  · exact ⟨out.tag,out.value,out.destination,out.replySize,
      fun p hp ha before => (out.data p hp ha before).trans (bo.data p hp ha before),
      fun p h80 h81 h82 h83 rg => (out.index p h80 h81 h82 h83 rg).trans (bo.index p h80 h81 h82 rg)⟩

end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
