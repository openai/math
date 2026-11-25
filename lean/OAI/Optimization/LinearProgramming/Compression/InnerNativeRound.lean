import OAI.Optimization.LinearProgramming.Compression.InnerPackets
import OAI.Optimization.LinearProgramming.Compression.InnerCoordinates
import OAI.Optimization.LinearProgramming.Compression.CachePadBounds
import OAI.Optimization.LinearProgramming.Lattice.BitRoundSession

/-! Native rounding sessions using the cache comparator's two-bit response. The transcript
contains only canonical sign words whose actual rescaled L¹ exponent fits the fixed cutoff. -/
namespace OAI
namespace Optimization
namespace LinearProgramming
namespace Compression
namespace Inner
open OracleSpec _root_.OAI.Optimization.LinearProgramming.Lattice Lattice.Bit SignType
open scoped BigOperators

theorem round_session_for {d : ℕ} (N M : ℕ) (hM : 0<M) (v : Fin d → ℝ)
    (negative : (Fin d → ℤ) → ℤ → Bool) (hn : ∀ a c, negative a c=true ↔ requestForm v a+c<0)
    (hfill : paperRadius N+7+(d+1)+queryCoefficientWidth (d+1) M ≤ manuscriptProxyFuel N)
    (o : WordOracle) (wire : ∀ h a, permitted N a → o h (signRowWord a) =
      signReply (orderOfSign (coordinateSign v a))) :
    ∃ hist count, WordDialogue.Session Driver.inputCode Driver.carryCode (Driver.dispatch Driver.actualKernels) o
      (Driver.frameBound.eval ((d+1)+M.size+12)) (.inl (d+1,M)) []
      (Driver.signPacket (List.ofFn (roundZFor M negative))) hist count ∧
      count≤(d+1)*(2*(d+1)+1+(d+1)*searchPrecision (d+1) M)+1 ∧ goodHistory N (d+1) hist := by
  let s := coordinateSign v
  let b := fun a => decide (0 ≤ s a)
  let t := lllRoundingProgram (d+1) M
  have ht : b=affineCommitReply negative := coordinateSign_test v negative hn
  have cap (a : Fin (d+1) → ℤ) (ha : a∈SignQueries.history b t) : permitted N a := by
    have hc := manuscript_rounding_query_l1 v hM (lllShortSelector M) (lllShortSelector_correct (Nat.succ_pos d) hM)
      negative hn a (by simpa only [ht,t,lllRoundingProgram] using ha) hfill
    simpa only [permitted,Fin.sum_univ_castSucc,add_comm (∑ i : Fin d, |a i.castSucc|) |a (Fin.last d)|] using hc
  obtain ⟨c,hc,hs⟩ := Driver.rounding_session_on_history (Nat.succ_pos d) hM
    (Fin.snoc v (1:ℝ)) s (fun _ => rfl) o (fun h a ha => wire h a (cap _ ha)) []
  let words := Driver.wordQueries b t
  let hist := (words.map (fun q => (q,Driver.signAnswer s q))).reverse
  refine ⟨hist,c+1,?_,Nat.add_le_add_right hc 1,?_⟩
  · change WordDialogue.Session _ _ _ _ _ _ _ (Driver.signPacket (List.ofFn (SignQueries.run (affineCommitReply negative) t))) hist _
    rw [← ht,Driver.signPacket_pack]
    simpa only [List.append_nil] using hs
  · intro ev he
    obtain ⟨q,hq,heq⟩ := List.mem_map.mp (List.mem_reverse.mp he)
    obtain ⟨a,ha,hqeq⟩ := List.mem_map.mp hq
    refine ⟨a,?_,cap a (List.mem_reverse.mp ha)⟩
    exact (congrArg Prod.fst heq).symm.trans hqeq.symm

theorem round_session {d : ℕ} (N M : ℕ) (hM : 0<M) (mag : Fin d → ℚ) (hm : ∀ i, 0 < mag i)
    (hfill : paperRadius N+7+(d+1)+queryCoefficientWidth (d+1) M ≤ manuscriptProxyFuel N)
    (o : WordOracle) (wire : ∀ h a, permitted N a → o h (signRowWord a) =
      signReply (orderOfSign (generatorSign (manuscriptProxyFuel N) (paperRadius N+7) mag a))) :
    ∃ hist count, WordDialogue.Session Driver.inputCode Driver.carryCode (Driver.dispatch Driver.actualKernels) o
      (Driver.frameBound.eval ((d+1)+M.size+12)) (.inl (d+1,M)) []
      (Driver.signPacket (List.ofFn (roundZ N M mag))) hist count ∧
      count≤(d+1)*(2*(d+1)+1+(d+1)*searchPrecision (d+1) M)+1 ∧ goodHistory N (d+1) hist := by
  let fuel := manuscriptProxyFuel N
  let p := paperRadius N+7
  apply round_session_for N M hM (generatorProxy fuel p mag) (requestMagnitudeNegative fuel p mag)
    (requestMagnitudeNegative_correct fuel p mag hm) hfill o
  intro h a ha
  rw [coordinateSign,← generatorSign_correct fuel p mag hm a]
  exact wire h a ha

end Inner
end Compression
end LinearProgramming
end Optimization
end OAI
