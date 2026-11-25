import OAI.Computability.BorderVNP.FiniteEvaluatorCellsPost
import OAI.Computability.BorderVNP.FiniteEvaluatorCubePacket
import OAI.Computability.BorderVNP.GeometryAdviceCharge

/-! # The complete local field multiplier of the positive diagonal branch

The actual finite sparse validator, its scalar readback, and the cube vertex
lookup share one native program and one chronological memory. The packet
lookup consumes the independently supplied cube vertex inputs.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace FiniteEvaluator.CellsCube

open VPVNP.BurstRAM RoutingISA FieldProcessor TeamContraction TeamRAM
open scoped BigOperators Classical

variable {w dim b h K s : ℕ} {F : Type*} [Field F] [Fintype F]

/-- Actual local positive-branch multiplication after routing and field report preparation. -/
def code : Code := .seq Cells.code CubePacket.code

/-- The additional single-word scalar input and its private clock fit uniformly
at large lengths, also at one processor. The field deck is fixed before the length. -/
theorem eventually_cube_width (F : Type*) [Fintype F] :
    ∀ᶠ n : ℕ in Filter.atTop, ∀ r w : ℕ, 1≤r → TeamScales.logWidth r n ≤ w →
      2*Fintype.card F < w ∧ 2*Fintype.card F < CompactMachine.nativeClock n ∧ 1 ≤ TeamScales.width n (1/2) := by
  filter_upwards [Filter.eventually_ge_atTop (2^(2*Fintype.card F):ℕ),Filter.eventually_ge_atTop (2*Fintype.card F+1:ℕ),Filter.eventually_ge_atTop (1:ℕ)] with n hp hn npos
  intro r w hr hw
  have log : Nat.clog 2 (n+1) ≤ TeamScales.logWidth r n := (GeometryAdviceRate.indexWidths hr npos).2.1
  have enough : 2*Fintype.card F < Nat.clog 2 (n+1) := (Nat.lt_clog_iff_pow_lt (by decide)).mpr (by omega)
  have pow : n ≤ n^25 := Nat.le_self_pow (by decide : 25≠0) n
  have rn : 1 ≤ (n:ℝ) := by exact_mod_cast npos
  refine ⟨enough.trans_le (log.trans hw),?_,?_⟩
  · unfold CompactMachine.nativeClock; omega
  · exact (Nat.le_floor_iff (by positivity : 0 ≤ (n:ℝ)^(1/2:ℝ))).mpr (by simpa using Real.one_le_rpow rn (by norm_num : (0:ℝ) ≤ 1/2))

variable (X : Cells.Inputs F) (Y : CubePacket.Inputs dim b h K s F)

/-- All native path weights of the linked field team, summed on their real
incoming memory and within the measured local time and burst bounds. The cube
reads its actual visit arrays from the memory left by the signed validators and
field report packs. -/
theorem prepared_value_for (codec : Cells.Codec) (pub : Arg → Word w) (bank : Bank w) (mem : Memory w) (n : ℕ)
    (cells : Cells.Prepared X pub mem n codec) (cube : CubePacket.Prepared Y pub (X.post mem))
    (wide : 2*Fintype.card F<w) (clock : 2*Fintype.card F<CompactMachine.nativeClock n)
    (oneWord : 1≤TeamScales.width n (1/2)) :
    let fuel := CompactMachine.nativeClock n
    let lib := Cells.library F codec
    let mac := TeamSiteEvents.macros lib fuel
    let f := CellDispatch.Frame.ofMemory pub mem
    ∃ paths : Finset (List (TeamRAM.Event w)),
      (∀ bs es, execute (code.program.fetch pub mac) ⟨0,bank⟩ mem bs = some es ↔ es∈paths ∧ es.map TeamRAM.Event.choices=bs) ∧
      (∀ es ∈ paths, Within (X.validatorCost pub mem+X.scalarCost+Y.cost) (TeamScales.width n (1/2)) (n^25) es) ∧
      (∑ es ∈ paths, weight pub lib (Cells.terminals F codec) fuel code bank es) =
        ((((f.ownedRows mem 0 f.count).map (fun i => (X.cells i).weight)).prod : ℤ) : F) * X.outputs.prod * ∏ i, Y.scalar i := by
  intro fuel lib mac f
  obtain ⟨initial,accept,cost,val⟩ := Cells.prepared_value_for X codec pub bank mem n cells
  have admit (es) : es∈initial ↔ ∃ z mz, Runs pub mac Cells.code bank mem es z mz := by
    constructor
    · intro hi
      exact ((Code.execute_iff_runs (by decide : Cells.code.withoutAccept=true)).mp
        ((accept (es.map TeamRAM.Event.choices) es).mpr ⟨hi,rfl⟩)).1
    · rintro ⟨_,_,r⟩; exact ((accept _ es).mp r.execute).1
  have later {es z mz} (r : Runs pub mac Cells.code bank mem es z mz) :
      ∃ gs t mt, Runs pub mac CubePacket.code z mz gs t mt ∧ Within Y.cost (TeamScales.width n (1/2)) (n^25) gs ∧
        weight pub lib (Cells.terminals F codec) fuel CubePacket.code z gs = ∏ i, Y.scalar i ∧
        ∀ fs v mv, Runs pub mac CubePacket.code z mz fs v mv → fs=gs := by
    obtain rfl := Cells.post_memory_for X codec cells r
    obtain ⟨gs,t,mt,path,limit,v,_,only⟩ := CubePacket.run Y pub (CompactMachine.siteLibrary codec.driver)
      (fun _ => signedReturn) fuel z (X.post mem) cube wide clock
    exact ⟨gs,t,mt,path,⟨limit.cost,fun e he => (limit.length e he).trans oneWord,
      fun e he => (limit.choices e he).trans (Nat.zero_le _)⟩,v,fun fs u mu rr => (only fs u mu rr).1⟩
  obtain ⟨paths,steps,limits,weighted⟩ := continue_histories pub lib (Cells.terminals F codec) fuel Cells.code CubePacket.code bank mem initial
    (X.validatorCost pub mem+X.scalarCost) Y.cost (TeamScales.width n (1/2)) (n^25) (∏ i, Y.scalar i)
    admit cost (fun a b => Cells.same_post a b) later
  refine ⟨paths,?_,limits,?_⟩
  · intro bs es
    exact (Code.execute_iff_runs (by decide : code.withoutAccept=true)).trans (and_congr_left fun _ => (steps es).symm)
  · exact weighted.trans (congrArg (· * ∏ i, Y.scalar i) val)

/-- Dense cell packets followed by the cube vertex lookups give the local product
of the validator weights, field reports, and cube entries. -/
theorem prepared_value (pub : Arg → Word w) (bank : Bank w) (mem : Memory w) (n : ℕ)
    (cells : Cells.Prepared X pub mem n) (cube : CubePacket.Prepared Y pub (X.post mem))
    (wide : 2*Fintype.card F<w) (clock : 2*Fintype.card F<CompactMachine.nativeClock n)
    (oneWord : 1≤TeamScales.width n (1/2)) :
    let fuel := CompactMachine.nativeClock n
    let lib := Cells.library F
    let mac := TeamSiteEvents.macros lib fuel
    let f := CellDispatch.Frame.ofMemory pub mem
    ∃ paths : Finset (List (TeamRAM.Event w)),
      (∀ bs es, execute (code.program.fetch pub mac) ⟨0,bank⟩ mem bs = some es ↔ es∈paths ∧ es.map TeamRAM.Event.choices=bs) ∧
      (∀ es ∈ paths, Within (X.validatorCost pub mem+X.scalarCost+Y.cost) (TeamScales.width n (1/2)) (n^25) es) ∧
      (∑ es ∈ paths, weight pub lib (Cells.terminals F) fuel code bank es) =
        ((((f.ownedRows mem 0 f.count).map (fun i => (X.cells i).weight)).prod : ℤ) : F) * X.outputs.prod * ∏ i, Y.scalar i :=
  prepared_value_for X Y .dense pub bank mem n cells cube wide clock oneWord

end FiniteEvaluator.CellsCube

end BorderVNP
end Computability
end OAI
