import OAI.Computability.BorderVNP.TeamTapeInputRouteDispatch

/-! # Final owner banks and all-branch clock of the physical team router -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamTapeInputRoute

open VPVNP BurstRAM RAMTape RAMLayout RAMSerialization TeamTapeSorting

variable {d e w : ℕ}

/-- Both input suffixes are retained verbatim, and the verdict wrapper can read the actual
choice of virtual banks on its saved flag stack. -/
theorem ownerOutput_frame (a : Fields d e w) (v : Word d) (other : Option (Word d))
    (tail rest : List Bool) (s : Stacks Port) :
    let out := ownerOutput a v other tail rest s
    out metadata = tail ∧ out source = rest ∧ out secondFlag = other.isSome :: s secondFlag := by
  intro out
  cases other with
  | none =>
    let f := siteOutput false a v (false::tail) rest s
    have hf := siteOutput_frame false a v (false::tail) rest s
    exact ⟨by simp [out,ownerOutput,marked],hf.2.1,by
      change marked f false tail secondFlag = false :: s secondFlag
      simp only [marked,Function.update_self]
      exact congrArg (false :: ·) (hf.2.2.2.2.2.2.1 .size)⟩
  | some u =>
    let publicTail := Evaluator.InputBank.fieldBits (wordBits u) ++ tail
    let f := siteOutput false a v (true::publicTail) (rowBits a u ++ rest) s
    let mid := marked f true publicTail
    have hf := siteOutput_frame false a v (true::publicTail) (rowBits a u ++ rest) s
    have hu := siteOutput_frame true a u tail rest mid
    refine ⟨hu.1,hu.2.1,?_⟩
    apply (hu.2.2.2.2.2.2.1 .size).trans
    change marked f true publicTail secondFlag = true :: s secondFlag
    simp only [marked,Function.update_self]
    exact congrArg (true :: ·) (hf.2.2.2.2.2.2.1 .size)

/-- The primary virtual bank seen by the terminal sorter contains exactly the real
canonical emitted array, for either public presence bit. -/
theorem ownerOutput_primary (hw : 2 ≤ w) (a : Fields d e w) (v : Word d) (other : Option (Word d))
    (tail rest : List Bool) (s : Stacks Port) (rs : List (WordRecord w))
    (hb : s closedBlock = List.ofFn ((blockFormat (2^e) hw).encode (RecordBuffer.slots (2^e) rs)))
    (hz : ∀ i, s (.post false i) = []) :
    ownerOutput a v other tail rest s ∘ Port.post false = SitePost.prestate v (incoming a v)
      (outgoing a v) (SortReplay.emittedBlock hw e rs, []) (comparisonBits a v) := by
  cases other with
  | none => exact siteOutput_prestate hw false a v s (false::tail) rest rs hb hz
  | some u =>
    let pt := Evaluator.InputBank.fieldBits (wordBits u) ++ tail
    let f := siteOutput false a v (true::pt) (rowBits a u ++ rest) s
    let mid := marked f true pt
    have real := siteOutput_prestate hw false a v s (true::pt) (rowBits a u ++ rest) rs hb hz
    have virtual := siteOutput_frame true a u tail rest mid
    funext p
    exact (virtual.2.2.2.2.2.2.2 p).trans (congrFun real p)

/-- A present second bank sees the canonical vacant block and its own virtual address,
boundary messages and comparator suffix, independent of the contents of the real block. -/
theorem ownerOutput_secondary (hw : 2 ≤ w) (a : Fields d e w) (v u : Word d)
    (tail rest : List Bool) (s : Stacks Port) (rs : List (WordRecord w))
    (hb : s closedBlock = List.ofFn ((blockFormat (2^e) hw).encode (RecordBuffer.slots (2^e) rs)))
    (hz : ∀ i, s (.post true i) = []) :
    ownerOutput a v (some u) tail rest s ∘ Port.post true = SitePost.prestate u (incoming a u)
      (outgoing a u) (SortReplay.emittedBlock hw e [], []) (comparisonBits a u) := by
  let pt := Evaluator.InputBank.fieldBits (wordBits u) ++ tail
  let f := siteOutput false a v (true::pt) (rowBits a u ++ rest) s
  let mid := marked f true pt
  have hf := siteOutput_frame false a v (true::pt) (rowBits a u ++ rest) s
  exact siteOutput_prestate hw true a u mid tail rest rs (hf.2.2.2.2.2.1.trans hb)
    (fun i => (hf.2.2.2.2.2.2.2 i).trans (hz i))

/-- Quadratic clock envelope for a public router whose address width, word width, bucket,
and physical comparison-bit segment each fit within the processor's input length. -/
theorem loader_time_le (n : ℕ) (other : Option (Word d)) (hd : d ≤ n) (hw : w ≤ n)
    (hH : 2^e ≤ n) (hL : comparisonSize d e w ≤ n) :
    7*comparisonSize d e w + 9*Nat.clog 2 (n+1)+3 +
      (lanes other * siteTime d e w (blockBits (2^e) w) + 2) ≤ 600*(n+1)^2 := by
  have hc : Nat.clog 2 (n+1) ≤ n := Nat.clog_le_of_le_pow (Nat.lt_two_pow_self (n := n))
  have bytes : blockBits (2^e) w ≤ 20*(n*n) := by
    unfold blockBits
    rw [show 4*2^e*5*w = 20*(2^e*w) by ring]
    exact Nat.mul_le_mul_left 20 (Nat.mul_le_mul hH hw)
  have half : siteTime d e w (blockBits (2^e) w) ≤ 100*(n*n) + 143*n+49 := by
    unfold siteTime geometryTime rowTime
    omega
  have hlanes : lanes other ≤ 2 := by cases other <;> simp [lanes]
  have both := Nat.mul_le_mul hlanes half
  nlinarith only [both,hL,hc,Nat.zero_le n,Nat.zero_le (n*n)]

/-- On the processor's genuine public fields and raw links, all paths stop at the same
time. Exactly one return reaches the continuation. Its occupied banks are precisely the
prestates used by the physical sorting proof, and it preserves the two unread suffixes. -/
theorem loader_spec (n : ℕ) (hw₂ : 2 ≤ w) (a : Fields d e w) (v : Word d) (other : Option (Word d))
    (s : Stacks Port) (tail rest : List Bool) (rs : List (WordRecord w))
    (hd : d ≤ n) (hw : w ≤ n) (hH : 2^e ≤ n) (hL : comparisonSize d e w ≤ n)
    (hi : s metadata = metadataBits n e w v other ++ tail)
    (hs : s source = ownerBits a v other ++ rest)
    (ww : (s widthSource).length = w) (bc : (s bucket).length = 2^e) (hc : s .suffixSize = [])
    (hb : s (.entry (.inl .bits)) = []) (hh : s (.entry (.inl .high)) = [])
    (htmp : s (.entry (.inl .scratch)) = []) (hm : s (.work .count) = [])
    (ht : s (.work .tmp) = []) (hz : ∀ b i, s (.post b i) = [])
    (hblock : s closedBlock = List.ofFn ((blockFormat (2^e) hw₂).encode (RecordBuffer.slots (2^e) rs))) :
    ∃ t ≤ 600*(n+1)^2, ∃ out, loader.Runs t s out ∧
      out metadata = tail ∧ out source = rest ∧ out secondFlag = other.isSome :: s secondFlag ∧
      out ∘ Port.post false = SitePost.prestate v (incoming a v) (outgoing a v)
        (SortReplay.emittedBlock hw₂ e rs, []) (comparisonBits a v) ∧
      (∀ u, other = some u → out ∘ Port.post true = SitePost.prestate u (incoming a u)
        (outgoing a u) (SortReplay.emittedBlock hw₂ e [], []) (comparisonBits a u)) ∧
      (∀ c fuel, loader.body.count c (fuel+t) s = c fuel out) ∧
      ∀ c fuel, loader.body.AllStops c (fuel+t) s ↔ c fuel out := by
  let suffix := Evaluator.InputBank.fieldBits (wordBits v) ++ (secondId other ++ tail)
  let mid := sized s (comparisonSize d e w) suffix
  let out := ownerOutput a v other tail rest mid
  have hb' : mid closedBlock = _ := hblock
  have hz' (b i) : mid (.post b i) = [] := by simpa [mid,sized] using hz b i
  obtain ⟨t,tt,run⟩ := loader_runs n a v other s tail rest hL hi hs ww bc hc hb hh htmp hm ht hz
  have hlen : (s closedBlock).length = blockBits (2^e) w := by rw [hblock,List.length_ofFn]; rfl
  rw [hlen] at tt
  obtain ⟨hmeta,stream,flag⟩ := ownerOutput_frame a v other tail rest mid
  refine ⟨t,tt.trans (loader_time_le n other hd hw hH hL),out,run,hmeta,stream,flag,
    ownerOutput_primary hw₂ a v other tail rest mid rs hb' (hz' false),?_,run.count_eq,run.allStops_iff⟩
  rintro u rfl
  exact ownerOutput_secondary hw₂ a v u tail rest mid rs hb' (hz' true)

end TeamTapeInputRoute

end BorderVNP
end Computability
end OAI
