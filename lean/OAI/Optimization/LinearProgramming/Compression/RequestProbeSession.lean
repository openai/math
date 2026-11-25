import OAI.Optimization.LinearProgramming.OracleSpec.PriceEncoding
import OAI.Optimization.LinearProgramming.Compression.RequestProbeDialogue
import OAI.Optimization.LinearProgramming.Lattice.BitProbeWidthEncoding

/-! Quantitative deployment of the graph residual dialogue. Every row write,
sign request, reply and stored continuation is present on a finite bit tape. -/

namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace RequestTable
namespace Dialogue

open ExactQuantumFactoring.BitStackProgram
open ExactQuantumFactoring.BitStackProgram.Procedure
open OracleSpec Lattice.Bit

def sourceWordSize (x : GridArg) :=
  (prodCode intRowCode intRowCode (gridRows x)).length

private theorem source_row_bound {p B : ℕ} (r : List ℤ) (hlen : r.length≤p)
    (hcode : (intRowCode r).length≤B) : Driver.Probe.RowBound p (2^B) r := by
  refine ⟨hlen,?_⟩
  intro z hz
  have sz : (intCode z).length=z.natAbs.size+3 := by
    simp [intCode,intData,prodCode,pairBits_length,boolCode,Nat.size_eq_bits_len]
    omega
  have he := (code_le_of_mem intCode hz).trans hcode
  rw [sz] at he
  exact (Nat.lt_size_self z.natAbs).le.trans (Nat.pow_le_pow_right (by decide) (by omega))

theorem startProbe_bounded (x : GridArg) : Driver.Probe.ActionBound (x.2.length+1)
    (gridDepth x) (2^(sourceWordSize x)) (startProbe x) := by
  let p := x.2.length+1
  let k := gridDepth x
  let B := sourceWordSize x
  let rs := gridRows x
  have work : (intRowCode rs.1).length≤B ∧ (intRowCode rs.2).length≤B := by
    simp only [B,sourceWordSize,rs,prodCode,pairBits_length];omega
  have hpiv : Driver.Probe.PivotBound p k (2^B) (probeParams x,rs.2) := by
    refine ⟨⟨le_rfl,le_rfl,⟨?_,?_⟩⟩,?_⟩
    · simp [probeParams]
    · intro row h; simp [probeParams] at h
    · exact source_row_bound _ (by simp [rs,gridRows,p]) work.2
  exact Driver.Probe.nextRow_single_bounded hpiv (Nat.zero_lt_succ _)
    (source_row_bound _ (by simp [gridRows]) work.1) (Nat.succ_le_succ (Nat.zero_le x.2.length))

def routedInputSize (x : GridArg) (p k B : ℕ) :=
  2*(gridArgCode x).length+Driver.Probe.probeWordSize p k B+1

noncomputable def routedSize (x : GridArg) (p k B : ℕ) :=
  let t := routedInputSize x p k B
  t+routeP.bound.eval t

theorem route_length {p k B : ℕ} (x : GridArg) {a : Driver.Probe.Action}
    (ha : Driver.Probe.ActionBound p k (2^B) a) :
    (actionCode (route x a)).length ≤ routedSize x p k B := by
  have h := Driver.Probe.actionCode_length ha
  have harg : (prodCode gridArgCode Driver.Probe.actionCode (x,a)).length ≤ routedInputSize x p k B := by
    simp only [routedInputSize,prodCode,pairBits_length];omega
  exact (routeP.output_length_le (x,a)).trans
    (Nat.add_le_add harg (eval_nat_mono routeP.bound harg))

/-- A source oracle may retain history. Each reply must provide the agreed sign
with a bounded code, while the query words are determined by the actual dispatch. -/
theorem session_of_probe_runs {I : Type} (ei : I → Word) (prepare : I → Prepared)
    (x : GridArg) (O : List ℤ → Bool) (oracle : WordOracle) (L p k B : ℕ)
    (hL : routedSize x p k B + 6 ≤ L)
    (allowed : List ℤ → Prop)
    (answer : ∀ hist row, allowed row → Driver.nonnegativeAnswer (oracle hist (Driver.signPacket row)) = O row ∧
      (oracle hist (Driver.signPacket row)).length≤2)
    {a : Driver.Probe.Action} {qs : List (List ℤ)} {r : Driver.Probe.Result}
    (run : Driver.Probe.Runs O a qs r) (allRows : ∀ row∈qs, allowed row)
    (ha : Driver.Probe.ActionBound p k (2^B) a)
    {s : I ⊕ (Word × Carry)} (state : dispatchWith prepare s = route x a)
    (hs : (WordDialogue.stateCode ei carryCode s).length ≤ L) (hist : Transcript) :
    ∃ fresh : Transcript, WordDialogue.Session ei carryCode (dispatchWith prepare) oracle L s hist
      (outputCode (represent x (r.2.headD 0))) (fresh++hist) (qs.length+1) ∧
      fresh.map Prod.fst = (qs.map Driver.signPacket).reverse := by
  induction run generalizing s hist with
  | done r =>
    have h := route_length x ha
    change (false :: outputCode (represent x (r.2.headD 0))).length ≤ _ at h
    exact ⟨[],.done state hs (by simp only [List.length_cons] at h;omega),by simp⟩
  | @ask row c qs r tail ih =>
    let word := Driver.signPacket row
    let response := oracle hist word
    obtain ⟨ho,hw⟩ := answer hist row (allRows row List.mem_cons_self)
    have codeSize := route_length x ha
    change (true :: prodCode (id : Word → Word) carryCode (word,(x,c))).length ≤ _ at codeSize
    simp only [List.length_cons,prodCode,pairBits_length,id_eq] at codeSize
    change response.length ≤ 2 at hw
    have nextSize : (WordDialogue.stateCode ei carryCode (.inr (response,(x,c)))).length ≤ L := by
      simp only [WordDialogue.stateCode,List.length_cons,List.length_append,OracleSpec.frame_length]
      omega
    have next : dispatchWith prepare (.inr (response,(x,c))) =
        route x (Driver.Probe.advance (O row) c) := by
      change route x (Driver.Probe.advance (Driver.nonnegativeAnswer response) c) = _
      exact congrArg (fun b => route x (Driver.Probe.advance b c)) ho
    obtain ⟨fresh,remaining,fh⟩ := ih (s := .inr (response,(x,c))) (hist := (word,response)::hist)
      (fun a h => allRows a (List.mem_cons_of_mem _ h))
      (Driver.Probe.advance_bounded (O row) ha.2) next nextSize
    have packetFits : word.length ≤ L := by omega
    have replyFits : response.length ≤ L := by omega
    refine ⟨fresh++[(word,response)],?_,?_⟩
    · rw [List.append_assoc]
      exact .query state hs packetFits replyFits remaining
    · simp [fh,word,List.reverse_cons]

end Dialogue
end RequestTable
end Compression
end LinearProgramming
end Optimization
end OAI
