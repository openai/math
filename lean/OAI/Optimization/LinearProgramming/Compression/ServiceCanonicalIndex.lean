import OAI.Optimization.LinearProgramming.Compression.ServiceCanonicalWords
import OAI.Optimization.LinearProgramming.OracleSpec.Companion

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace GeneratorTable

open OracleSpec

variable {d e n : ℕ}

theorem publicWords_of_index (D : Matrix (Fin d) (Fin n) ℚ) (E : Matrix (Fin e) (Fin n) ℚ)
    (u : MinorLog.Index D E) : publicWords (MinorLog.indexEquiv D E u).val = MinorLog.words u.val := by
  rcases u with ⟨a,ha⟩
  cases a with
  | inl a =>
    change publicWords (.inl (MinorLog.squareEquiv d n a)) = MinorLog.squareWords 0 a
    simp [publicWords,tag,order,rowWord,colWord,MinorLog.squareEquiv,MinorLog.squareWords]
    rfl
  | inr a =>
    change publicWords (.inr (MinorLog.squareEquiv e n a)) = MinorLog.squareWords 1 a
    simp [publicWords,tag,order,rowWord,colWord,MinorLog.squareEquiv,MinorLog.squareWords]
    rfl

end GeneratorTable
end Compression
end LinearProgramming
end Optimization
end OAI
