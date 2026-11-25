import OAI.ThreeFlat.Diagonal.TraceHeader
import OAI.ThreeFlat.Diagonal.TraceInitialCircuit

namespace OAI
/-! # Checking the initial native counter against the program stored in the input -/

namespace ThreeFlat.Diagonal.TraceProgram

open Computability.VPVNP.BurstRAM Computability.VPVNP.BurstRAM.PrivateRAM TraceBanks TraceRows TraceWords
open BinPackingGames.Foundations.Complexity.CookLevin.StatementCircuit (Expr)

variable {w p r k : ℕ} {σ : Type*}

/-- The start counter is selected by the header text word. A value outside
the program yields an empty set of matching alternatives. -/
def startFromText (hp : p ≤ 2^(w+1)) (text : Fin w → Expr σ)
    (state : Fin (w+1) → Expr σ) (raw : CodePin w r → Expr σ) : Expr σ :=
  Expr.disjoin (List.ofFn fun i : Fin p => (fieldIs text i.val).and (initialCheck hp i state raw))

theorem startFromText_true (hp : p ≤ 2^(w+1)) (text : Fin w → Expr σ)
    (state : Fin (w+1) → Expr σ) (raw : CodePin w r → Expr σ) (input : σ → Bool)
    (data : Memory w) (hread : ∀ j, (text j).eval input = bits (data 0) j) :
    (startFromText hp text state raw).eval input = true ↔
      ∃ i : Fin p, (data 0).val = i.val ∧ (initialCheck hp i state raw).eval input = true := by
  simp only [startFromText,Expr.eval_disjoin_true,List.mem_ofFn,exists_exists_eq_and,
    Expr.eval,Bool.and_eq_true,fieldIs_true _ _ _ _ hread]

/-- Valid input text forces exactly the same start-state test as its decoded program. -/
theorem startFromText_correct (hp : p ≤ 2^(w+1)) (text : Fin w → Expr σ)
    (state : Fin (w+1) → Expr σ) (raw : CodePin w r → Expr σ) (input : σ → Bool)
    {data : Memory w} {M : Machine w p r k} (hd : RAM.readProgram w p r k data = some M)
    (hread : ∀ j, (text j).eval input = bits (data 0) j) :
    (startFromText hp text state raw).eval input = (initialCheck hp M.entry state raw).eval input := by
  apply Bool.eq_iff_iff.mpr
  rw [startFromText_true hp text state raw input data hread]
  constructor
  · rintro ⟨i,he,hi⟩
    have eq : i = M.entry := Fin.ext (he.symm.trans (readProgram_entry hd).symm)
    simpa only [eq] using hi
  · intro ht
    exact ⟨M.entry,(readProgram_entry hd).symm,ht⟩

theorem startFromText_size (hp : p ≤ 2^(w+1)) (text : Fin w → Expr σ)
    (state : Fin (w+1) → Expr σ) (raw : CodePin w r → Expr σ)
    (ht : ∀ i, (text i).size ≤ 1) (hs : ∀ i, (state i).size ≤ 1) (hr : ∀ j, (raw j).size ≤ 1) :
    (startFromText hp text state raw).size ≤
      p*(10*w+1 + ((r+4)*((w+1)*10+2)+6) + 2) + 1 := by
  apply TraceFetch.fetch_size_le (fun i => fieldIs text i.val)
    (fun i => initialCheck hp i state raw) (fun i => fieldIs_size _ _ ht)
    (fun i => initialCheck_size hp i state raw hs hr)

end ThreeFlat.Diagonal.TraceProgram

end OAI
