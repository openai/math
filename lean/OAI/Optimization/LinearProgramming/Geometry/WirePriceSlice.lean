import OAI.Optimization.LinearProgramming.Geometry.WirePriceHistory
import OAI.Optimization.LinearProgramming.Geometry.RecordedHistory
import OAI.Optimization.LinearProgramming.Geometry.QueryKeys
import OAI.Optimization.LinearProgramming.PriceGame.Model
import OAI.Optimization.LinearProgramming.Recovery.Restart
import OAI.Optimization.LinearProgramming.OracleSpec.PriceGame

/-! A segment of outer price words together with precisely the minor exchanges used to answer them. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Geometry
namespace BorderBatch
namespace Service

open Contract OracleSpec OracleSpec.MinorLog Matrix Recovery
variable {r s n : ℕ} {D : Matrix (Fin r) (Fin n) ℚ} {E : Matrix (Fin s) (Fin n) ℚ}

structure WordSlice (S : Service D E) (ev : List (Recovery.Event Word))
    (before final fresh : Contract.History ℚ) : Prop where
  history : final=fresh++before
  named : NamedTraffic D E fresh
  matched : answersMatch S.oracle before → answersMatch S.oracle final
  cuts : wireCuts fresh=Recovery.restartCount ev
  size : fresh.length≤ev.length*(r*n)
  labels : ∀ F : Index D E → ℚ, AgreesOnReplies D E fresh F →
    ∀ (q : PriceGame.Query n) b,(priceQuery q.index q.prices,some b)∈ev →
      (geometricLabel D E q.prices q.index).eval (fun u => F (interfaceIndex D E u))=b

theorem WordSlice.nil (S : Service D E) (h : Contract.History ℚ) : WordSlice S [] h h [] :=
  ⟨rfl,fun _ hw => (List.not_mem_nil hw).elim,id,rfl,by simp,fun _ _ _ _ he => (List.not_mem_nil he).elim⟩

theorem WordSlice.append {S : Service D E} {ev more : List (Recovery.Event Word)}
    {start middle finish first second : Contract.History ℚ}
    (a : WordSlice S ev start middle first) (b : WordSlice S more middle finish second) :
    WordSlice S (ev++more) start finish (second++first) := by
  refine ⟨?_,?_,fun ok => b.matched (a.matched ok),?_,?_,?_⟩
  · rw [b.history,a.history,List.append_assoc]
  · intro e he
    rcases List.mem_append.mp he with hs|hf
    · exact b.named e hs
    · exact a.named e hf
  · rw [wireCuts_append,a.cuts,b.cuts,Recovery.restartCount_append,Nat.add_comm]
  · simp only [List.length_append,Nat.add_mul]
    have h₁ := a.size
    have h₂ := b.size
    omega
  · intro F fit q flag he
    rcases List.mem_append.mp he with h₁|h₂
    · exact a.labels F (fun u v hw => fit u v (List.mem_append.mpr (Or.inr hw))) q flag h₁
    · exact b.labels F (fun u v hw => fit u v (List.mem_append.mpr (Or.inl hw))) q flag h₂

end Service
end BorderBatch
end Geometry
end LinearProgramming
end Optimization
end OAI
