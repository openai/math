import OAI.Computability.BorderVNP.CubeISAOwnedSingleTape
import OAI.Computability.BorderVNP.DiagonalResidueRAMReplay

/-! # Recovering every singleton-row return from its actual private bit tape -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace Cube.Scatter.SingleRowData

open RoutingISA RoutingISA.Owned Physical Physical.Owned VPVNP.BurstRAM DiagonalResidueRAM

variable {w n d len : ℕ} (D : SingleRowData n d len)

/-- All fetched singleton-row instructions, including the symbolic candidate guard, have
the ordinary native opcode tag. -/
theorem native_tags (n : ℕ) : ∀ pc, (rowLoop (singleCandidate n) scatterSingle).program.tag pc = .native := by
  apply Code.program_tag_native
  have cand := (singleCandidate n).nativeOnly_of_unsigned (singleCandidate_frame n).1
  have body : scatterSingle.nativeOnly = true := by decide
  simp only [rowLoop,Code.nativeOnly,cand,body,Bool.and_self]

/-- On every returning singleton row, zero-extension of its actual chronological choice word
reconstructs the selected diagonal bits. This yields the exact memory, cursors, private-choice
sequence, event signs and tick bound, retaining all original crossing and off-row values. -/
theorem recover (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (src : Set ℕ)
    (initial : Bank w) (m₀ : Memory w) (entry : D.Entry initial)
    (prepared : D.PreparedRow src m₀) (frameZ : (pub 0).val+56 ∈ src) (frameBank : (pub 0).val+88 ∈ src)
    (zAt : readings m₀ ((pub 0).val+56) = d^(n+1)) (bankAt : readings m₀ ((pub 0).val+88) = D.bank)
    (frameFit : (pub 0).val+88 < 2^w) (keys : d^(n+1)*d^(n+1) ≤ 2^w)
    (allocation : D.bank+d^(n+1)*d^(n+1)*len < 2^w)
    {es t mt} (run : Runs pub mac (rowLoop (singleCandidate n) scatterSingle) initial m₀ es t mt) :
    let E := D.withTape (ChoiceTape.extend (es.flatMap TeamRAM.Event.choices))
    TraceOK es (rowChoices E.selected E.localBits) es.length ∧
      traceCost es ≤ (∑ t : Fin (singlePairTrials n d), (6*n+17+3 + if D.selected t then startSingle.slots+5*len+2 else 1))+1 ∧
      E.At initial m₀ (singlePairTrials n d) t mt := by
  intro E
  let bs := es.flatMap TeamRAM.Event.choices
  let tape := ChoiceTape.extend bs
  have start : E.Entry initial := ⟨entry.zero,entry.one,entry.radix,entry.tails,entry.place,entry.left,
    entry.right,entry.start,entry.bound,entry.width,entry.selector,entry.crossing⟩
  obtain ⟨fs,y,my,canon,tr,cost,state⟩ := E.scatterRow_run pub mac src initial m₀ start
    (D.prepared_withTape tape m₀ prepared) frameZ frameBank zAt bankAt frameFit keys allocation
  obtain ⟨a,a',compat⟩ := ChoiceTape.compatible bs (ChoiceTape.offset D.privateWidth (singlePairTrials n d))
  have agree := (congrArg (· ++ a) (tr.2.1.trans (D.withTape_choices tape))).trans compat
  obtain ⟨rfl,rfl,rfl⟩ := unique_returns (native_tags n) canon run agree
  exact ⟨tr,cost,state⟩

/-- Equal actual private bits determine a unique chronological singleton-row return. -/
theorem unique {pub : Arg → Word w} {mac : TeamOpcode.Macros w 8} {r m es t mt fs y my}
    (first : Runs pub mac (rowLoop (singleCandidate n) scatterSingle) r m es t mt)
    (second : Runs pub mac (rowLoop (singleCandidate n) scatterSingle) r m fs y my)
    (eqn : es.flatMap TeamRAM.Event.choices = fs.flatMap TeamRAM.Event.choices) :
    es = fs ∧ t = y ∧ mt = my :=
  unique_returns (native_tags n) first second (tail := []) (tail' := []) (by simpa using eqn)

end Cube.Scatter.SingleRowData

end BorderVNP
end Computability
end OAI
