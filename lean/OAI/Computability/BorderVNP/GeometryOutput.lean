import OAI.Computability.BorderVNP.GeometryOutputLoad
import OAI.Computability.BorderVNP.DiagonalTallyBitsPack
import OAI.Computability.BorderVNP.RoutingISADeterministic

/-! # Scatter a shared Boolean geometry circuit's selected outputs

The interpreter checks the circuit's validity bit, gathers arbitrary wire
references, and packs each word in its allocated result array. Its linear cost
counts both indirect probes per gathered bit. All loops use native ISA guards.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace GeometryOutput

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA DiagonalResidueRAM
open DiagonalTallyBits (WordsAt BitsAt outputMemory)

variable {w : ℕ}

/-- After gathering, move the persistent header words into the packing ABI. -/
def packOperands : Code := .block [
  .copy 50 32, .copy 51 33, .copy 52 34, .copy 53 35, .copy 63 38]

/-- Scan the advised outputs into the temporary array, then pack the result. -/
def scatter : Code :=
  .seq (.whileLt 41 37 gatherBody) (.seq packOperands DiagonalTallyBits.pack)

/-- The geometry instruction path rejects when its dereferenced validity bit is zero. -/
def code : Code := .seq loadOutput (.ifEq 36 38 scatter .reject)

/-- Exact number of ticks on a valid geometry output. -/
def ticks (count width : ℕ) : ℕ :=
  24 + (7*(count*width)+1 + (5 + DiagonalTallyBits.ticks count width) + 1)

/-- The entire deterministic output pass has linear word-and-bit cost. -/
theorem ticks_le (count width : ℕ) : ticks count width ≤ 15*count*(width+1)+39 := by
  have := DiagonalTallyBits.ticks_le count width
  unfold ticks
  nlinarith

private theorem bitsAt_of_get (m : Memory w) (p : ℕ) (bs : List Bool)
    (h : ∀ i : Fin bs.length, (m (p+i.val)).val = bs[i.val].toNat) : BitsAt m p bs := by
  induction bs generalizing p with
  | nil => trivial
  | cons b bs ih =>
    refine ⟨by simpa using h ⟨0,by simp⟩,ih (p+1) ?_⟩
    intro i
    simpa [Nat.add_assoc,Nat.add_comm 1] using h ⟨i.val+1,by simp⟩

/-- Coordinate reads of the flattened bit stream supply every consecutive output word. -/
theorem wordsAt_of_get (m : Memory w) (p : ℕ) (xs : List (List Bool))
    (h : ∀ i : Fin xs.flatten.length, (m (p+i.val)).val = xs.flatten[i.val].toNat) :
    WordsAt m p xs := by
  induction xs generalizing p with
  | nil => trivial
  | cons b bs ih =>
    refine ⟨bitsAt_of_get _ _ _ (fun i => ?_), ih (p+b.length) ?_⟩
    · simpa [List.getElem_append_left i.isLt] using h ⟨i.val,by simp; omega⟩
    · intro i
      simpa [Nat.add_assoc,List.getElem_append_right] using h ⟨b.length+i.val, by simpa only [List.flatten_cons,List.length_append,Nat.add_lt_add_iff_left] using i.isLt⟩

/-- The concrete memory image of the bit gather followed by the word stores. -/
def resultMemory (m : Memory w) (l : Layout) (xs : List (List Bool)) : Memory w :=
  outputMemory (putBits m l.temp xs.flatten) l.dest xs

/-- The decoded output word in the specified result array. -/
theorem resultMemory_word (m : Memory w) (l : Layout) (xs : List (List Bool))
    (i : Fin xs.length) : resultMemory m l xs (l.dest+i.val) = word w (VPVNP.TapeWord.value xs[i.val]) :=
  DiagonalTallyBits.outputMemory_word _ _ _ _ i.isLt

/-- Both writes have disjoint explicit footprints. -/
theorem resultMemory_outside (m : Memory w) (l : Layout) (xs : List (List Bool)) (a : ℕ)
    (h₁ : a < l.dest ∨ l.dest+xs.length ≤ a) (h₂ : a < l.temp ∨ l.temp+xs.flatten.length ≤ a) :
    resultMemory m l xs a = m a :=
  (DiagonalTallyBits.outputMemory_outside _ _ _ _ h₁).trans (putBits_outside _ _ _ _ h₂)

/-- Width, address, and non-overlap requirements for the two output loops. -/
structure Layout.Fits (l : Layout) (w : ℕ) : Prop where
  /-- Requested output bits fit one native word. -/
  width : l.width ≤ w
  /-- The source-list sentinel is a valid address. -/
  refsEnd : l.refs+1+l.count*l.width < 2^w
  /-- The temporary output stream precedes the address list. -/
  tempEnd : l.temp+l.count*l.width ≤ l.refs+1
  /-- The result-array sentinel is a valid address. -/
  destEnd : l.dest+l.count < 2^w
  /-- Packing leaves all unread bits intact. -/
  separated : l.temp+l.count*l.width ≤ l.dest ∨ l.dest+l.count ≤ l.temp

private theorem packOperands_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (l : Layout) (valid : Bool)
    (hs : (l.gatherFrame valid).stable s) :
    ∃ z, Exact pub mac packOperands s m [] 5 z m ∧ z 50 = word w l.temp ∧
      z 51 = word w l.count ∧ z 52 = word w l.width ∧ z 53 = word w l.dest ∧ z 63 = 1 := by
  let e := effect false s m packOperands
  refine ⟨e.bank,⟨_,effect_runs pub mac false s m packOperands (by decide),?_⟩,?_⟩
  · simp [packOperands,Code.block,effect,TraceOK,tick]
  · simp [e,packOperands,Code.block,effect,Function.update]
    exact ⟨hs.1.1,hs.1.2.1,hs.1.2.2.1,hs.1.2.2.2.1,hs.2.1⟩

/-- A valid gate table supplies the actual source-address stream and the words
at those sources. The fixed machine produces exactly the packed array. -/
theorem code_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (l : Layout) (validAddr : ℕ) (sources : List (ℕ × Bool)) (xs : List (List Bool))
    (hf : l.Fits w) (hframe : l.loaded pub m) (hb : (pub 0).val+108 < 2^w)
    (ha : validAddr < 2^w) (href : m l.refs = word w validAddr) (hv : m validAddr = wordBit w true)
    (hsrc : sourcesAt m (l.refs+1) sources)
    (hdis : ∀ t ∈ sources, t.1 < l.temp ∨ l.temp+l.count*l.width ≤ t.1)
    (hbits : sources.map Prod.snd = xs.flatten) (hcount : xs.length = l.count)
    (hwords : ∀ b ∈ xs, b.length = l.width) :
    ∃ z, Exact pub mac code s m [] (ticks l.count l.width) z (resultMemory m l xs) := by
  have limit := hf.refsEnd
  have sep := hf.tempEnd
  have dest := hf.destEnd
  have hw : 1 < 2^w := by omega
  have len (ys : List (List Bool)) (hy : ∀ b ∈ ys, b.length = l.width) :
      ys.flatten.length = ys.length*l.width := by
    induction ys with
    | nil => simp
    | cons b bs ih =>
      simp only [List.flatten_cons,List.length_append,List.length_cons,Nat.succ_mul]
      rw [hy b (by simp),ih (fun t ht => hy t (by simp [ht])), Nat.add_comm]
  have hlen : sources.length = l.count*l.width := by
    simpa [len xs hwords,hcount] using congrArg List.length hbits
  obtain ⟨u,first,hu,h40,h41,h42⟩ :=
    loadOutput_runs pub mac s m l validAddr true hframe hb (by omega) ha href hv
  obtain ⟨t,gather,ht⟩ := gather_loop pub mac (l.gatherFrame true) u m l.temp (l.refs+1) 0 sources
    hu h40 h41 h42 (by simpa [Layout.gatherFrame] using hlen)
    (by change l.count*l.width < _; omega) hsrc (by omega) (by omega)
    (fun a ha => by simpa only [hlen] using hdis a ha)
  rw [hbits,hlen] at gather
  let mt := putBits m l.temp xs.flatten
  obtain ⟨p,install,hp₀,hp₁,hp₂,hp₃,hp₄⟩ := packOperands_runs pub mac t mt l true ht
  have bits : WordsAt mt l.temp xs := wordsAt_of_get _ _ _ fun i => by
    rw [show mt (l.temp+i.val) = _ from putBits_get m l.temp xs.flatten i,wordBit_val hw]
  obtain ⟨es,z,packed,tr,_,_,_⟩ := DiagonalTallyBits.pack_runs pub mac p mt xs
    (p := l.temp) (d := l.dest) (width := l.width)
    (hp₀ ▸ word_val _ _ (by omega)) (hp₃ ▸ word_val _ _ (by omega))
    (by rw [hp₁,word_val _ _ (by omega),hcount])
    (hp₂ ▸ word_val _ _ (hf.width.trans_lt (Nat.lt_pow_self (by decide))))
    (hp₄ ▸ word_val w 1 hw) hf.width hwords (by rw [hcount]; omega)
    (by rw [hcount]; exact dest) (by rw [hcount]; exact hf.separated) bits
  have packRun : Exact pub mac DiagonalTallyBits.pack p mt [] (DiagonalTallyBits.ticks l.count l.width) z
      (resultMemory m l xs) := ⟨es,packed,hcount ▸ tr⟩
  obtain ⟨fs,body,ticksBody⟩ := gather.seq (install.seq packRun)
  have ok : u 36 = u 38 := hu.1.2.2.2.2.1.trans hu.2.1.symm
  have branch : Exact pub mac (.ifEq 36 38 scatter .reject) u m []
      (7*(l.count*l.width)+1 + (5+DiagonalTallyBits.ticks l.count l.width)+1) z (resultMemory m l xs) :=
    ⟨_,.ifEq (by simpa only [ite_eq_left ok,scatter] using body),ticksBody.cons_tick⟩
  exact ⟨z,first.seq branch⟩

/-- A zero validity bit prevents any returning execution on any choice tape. -/
theorem invalid_no_run (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8) (s : Bank w) (m : Memory w)
    (l : Layout) (validAddr : ℕ) (hframe : l.loaded pub m) (hb : (pub 0).val+108 < 2^w)
    (hr : l.refs < 2^w) (ha : validAddr < 2^w) (href : m l.refs = word w validAddr)
    (hv : m validAddr = wordBit w false) {es z mz} : ¬ Runs pub mac code s m es z mz := by
  obtain ⟨u,⟨ds,first,_⟩,hu,_,_,_⟩ := loadOutput_runs pub mac s m l validAddr false hframe hb hr ha href hv
  have zero : u 36 = 0 := hu.1.2.2.2.2.1
  have ne : u 36 ≠ u 38 := by
    rw [zero,hu.2.1]
    intro h
    have hh := congrArg Fin.val h
    rw [show (1 : Word w).val = 1 from word_val w 1 (by omega)] at hh
    simp at hh
  intro r
  cases r with
  | atom h => cases h
  | seq a b =>
    obtain ⟨rfl,rfl,rfl⟩ := first.unique_of_deterministic (by decide) a
    cases b with
    | atom h => cases h
    | ifEq branch =>
      rw [ite_eq_right ne] at branch
      cases branch with
      | atom _ h => cases h

end GeometryOutput

end BorderVNP
end Computability
end OAI
