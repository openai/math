import OAI.Computability.BorderVNP.DiagonalTallyBits

/-! # Packing every claimed subtotal at its allocated physical destination -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace DiagonalTallyBits

open VPVNP.BurstRAM VPVNP.BurstRAM.PrivateRAM RoutingISA
open DiagonalResidueRAM (word word_val TraceOK effect effect_runs)
open VPVNP.TapeWord (value value_lt)

variable {w : ℕ}

/-- The input buffer is a list of consecutive little-endian words. -/
def WordsAt (m : Memory w) : ℕ → List (List Bool) → Prop
  | _, [] => True
  | p, b::bs => BitsAt m p b ∧ WordsAt m (p+b.length) bs

/-- Write the decoded words at successive destination addresses. -/
def outputMemory : Memory w → ℕ → List (List Bool) → Memory w
  | m, _, [] => m
  | m, d, b::bs => outputMemory (Function.update m d (word w (value b))) (d+1) bs

private theorem bits_congr (m m' : Memory w) (p : ℕ) (bs : List Bool) (hb : BitsAt m p bs)
    (he : ∀ j, p ≤ j → j < p+bs.length → m' j = m j) : BitsAt m' p bs := by
  induction bs generalizing p with
  | nil => trivial
  | cons b bs ih =>
    have h := he p le_rfl (by simp)
    refine ⟨h ▸ hb.1, ih _ hb.2 (fun j hj hn => he j (by omega) ?_)⟩
    simp at *; omega

/-- The encoded words can be read from any memory agreeing throughout the raw bit interval. -/
theorem words_congr (m m' : Memory w) (p width : ℕ) (xs : List (List Bool))
    (hx : WordsAt m p xs) (hw : ∀ b ∈ xs, b.length = width)
    (he : ∀ j, p ≤ j → j < p+xs.length*width → m' j = m j) : WordsAt m' p xs := by
  induction xs generalizing p with
  | nil => trivial
  | cons b xs ih =>
    have h := hw b List.mem_cons_self
    have he' : ∀ j, p ≤ j → j < p+width+xs.length*width → m' j = m j := by
      simpa [Nat.succ_mul, Nat.add_comm, Nat.add_left_comm, Nat.add_assoc] using he
    refine ⟨bits_congr _ _ _ _ hx.1 (fun j hj hh => he' j hj (by omega)),
      ih (p+b.length) hx.2 (fun l hl => hw _ (.tail _ hl)) ?_⟩
    intro j hj hn; exact he' j (by omega) (by omega)

/-- A complete word consumes three setup instructions, eight instructions per
bit including its loop test, a terminal bit-loop test, and three write instructions. -/
theorem wordBody_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (bs : List Bool) {p d i : ℕ}
    (hp : (s 50).val = p) (hd : (s 53).val = d) (hi : (s 54).val = i)
    (hw : (s 52).val = bs.length) (hone : (s 63).val = 1)
    (hfit : p+bs.length < 2^w) (hdfit : d+1 < 2^w) (hifit : i+1 < 2^w)
    (hb : BitsAt m p bs) :
    ∃ es t, Runs pub mac wordBody s m es t (Function.update m d (word w (value bs))) ∧
      TraceOK es [] (8*bs.length+7) ∧ Preserves scratch s t ∧
      (t 50).val = p+bs.length ∧ (t 53).val = d+1 ∧ (t 54).val = i+1 := by
  let a := effect false s m startWord
  have ha := effect_runs pub mac false s m startWord (by decide)
  change Runs pub mac startWord s m a.trace a.bank m at ha
  have a50 : (a.bank 50).val = p := by simpa [a,startWord,effect,Code.block,Function.update] using hp
  have a55 : (a.bank 55).val = 0 := by simp [a,startWord,effect,Code.block,Function.update]
  have a52 : (a.bank 52).val = 0+bs.length := by simpa [a,startWord,effect,Code.block,Function.update] using hw
  have a63 : (a.bank 63).val = 1 := by simpa [a,startWord,effect,Code.block,Function.update] using hone
  obtain ⟨fs,y,loop,ht,hy,hy50,hy56⟩ := bitLoop_runs pub mac a.bank m bs a50 a55 a52 a63 rfl hfit hb
  have h1 : s 63 = 1 := Fin.ext (by rw [hone, ← DiagonalResidueRAM.word_one]; exact
    (word_val w 1 (hone ▸ (s 63).isLt)).symm)
  have hyacc : y 56 = word w (value bs) := by
    simpa [a,startWord,Code.block,effect,Function.update,h1] using hy56
  have y53 : (y 53).val = d := by
    rw [hy 53 (by decide)]
    simpa [a,startWord,Code.block,effect,Function.update] using hd
  have y54 : (y 54).val = i := by
    rw [hy 54 (by decide)]
    simpa [a,startWord,Code.block,effect,Function.update] using hi
  have y63 : (y 63).val = 1 := (congrArg Fin.val (hy 63 (by decide))).trans a63
  let e := effect false y m finishWord
  have run := effect_runs pub mac false y m finishWord (by decide)
  change Runs pub mac finishWord y m e.trace e.bank e.mem at run
  have hem : e.mem = Function.update m d (word w (value bs)) := by
    simp [e,finishWord,Code.block,effect,y53,hyacc]
  rw [hem] at run
  refine ⟨_,e.bank,.seq ha (.seq loop run),?_,?_,?_,?_,?_⟩
  · have hta : TraceOK a.trace [] 3 := by simp [a,startWord,Code.block,effect,TraceOK,tick]
    have hte : TraceOK e.trace [] 3 := by simp [e,finishWord,Code.block,effect,TraceOK,tick]
    have he : 3 + (8*bs.length+1+3) = 8*bs.length+7 := by omega
    simpa only [List.nil_append, he] using hta.append (ht.append hte)
  · intro j hj
    have hd' : j ∉ digitScratch := fun h => hj (by simpa [scratch,digitScratch] using
      (show j = 50 ∨ j = 53 ∨ j = 54 ∨ j = 55 ∨ j = 56 ∨ j = 57 ∨ j = 59 ∨ j = 60 ∨ j = 61 from by
        simp [digitScratch] at h; tauto))
    have h₁ := hy j hd'
    simp [scratch] at hj
    simpa [e,finishWord,Code.block,effect,a,startWord,Function.update,hj] using h₁
  · simpa [e,finishWord,Code.block,effect,Function.update] using hy50
  · simp only [e,finishWord,Code.block,effect,BinaryOp.eval]
    simp [Function.update,Fin.val_add_eq_of_add_lt (show (y 53).val+(y 63).val < 2^w by omega),y53,y63]
  · simp only [e,finishWord,Code.block,effect,BinaryOp.eval]
    simp [Function.update,Fin.val_add_eq_of_add_lt (show (y 54).val+(y 63).val < 2^w by omega),y54,y63]

/-- All words are packed in sequence, on disjoint bounded input and output intervals.
The destination stores coincide with the mathematical little-endian interpretation. -/
theorem wordsLoop_runs (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (xs : List (List Bool)) {p d i width total : ℕ}
    (hp : (s 50).val = p) (hd : (s 53).val = d) (hi : (s 54).val = i)
    (hc : (s 51).val = total) (hw : (s 52).val = width) (hone : (s 63).val = 1)
    (hlen : i+xs.length = total) (hwidth : ∀ b ∈ xs, b.length = width)
    (hfit : p+xs.length*width < 2^w) (hdfit : d+xs.length < 2^w)
    (hsep : p+xs.length*width ≤ d ∨ d+xs.length ≤ p) (hb : WordsAt m p xs) :
    ∃ es t, Runs pub mac (.whileLt 54 51 wordBody) s m es t (outputMemory m d xs) ∧
      TraceOK es [] (xs.length*(8*width+8)+1) ∧ Preserves scratch s t ∧
      (t 50).val = p+xs.length*width ∧ (t 53).val = d+xs.length := by
  induction xs generalizing s m p d i with
  | nil =>
    have heq : s 54 = s 51 := Fin.ext (by simp_all)
    refine ⟨_,s,.whileDone (by simp [heq]),?_,(fun _ _ => rfl),by simpa using hp,by simpa using hd⟩
    simp [TraceOK,tick]
  | cons b xs ih =>
    obtain ⟨hbits,hrest⟩ := hb
    have hbwidth := hwidth b List.mem_cons_self
    have hn := fun l (h : l ∈ xs) => hwidth l (.tail b h)
    simp only [List.length_cons, Nat.succ_mul] at hlen hfit hdfit hsep
    have htotal : total < 2^w := hc ▸ (s 51).isLt
    have guard : s 54 < s 51 := by change (s 54).val < (s 51).val; omega
    obtain ⟨es,t,run,htrace,hp',ht50,ht53,ht54⟩ := wordBody_runs pub mac s m b hp hd hi
      (hw.trans hbwidth.symm) hone (by omega) (by omega) (by omega) hbits
    let m' := Function.update m d (word w (value b))
    have hr : WordsAt m' (p+b.length) xs :=
      words_congr m m' _ width xs hrest hn (fun j hj hj' => by
        have : j ≠ d := by omega
        simp [m',this])
    obtain ⟨fs,z,loop,hft,hpr,hz50,hz53⟩ := ih t m' ht50 ht53 ht54
      ((congrArg Fin.val (hp' 51 (by decide))).trans hc) ((congrArg Fin.val (hp' 52 (by decide))).trans hw)
      ((congrArg Fin.val (hp' 63 (by decide))).trans hone) (by omega) hn (by omega) (by omega)
      (by omega) hr
    refine ⟨_,z,.whileStep guard run loop,?_,hp'.trans hpr,by simp only [List.length_cons, Nat.succ_mul]; omega,by simp only [List.length_cons]; omega⟩
    have he : 8*b.length+7+(xs.length*(8*width+8)+1)+1 = (b::xs).length*(8*width+8)+1 := by rw [List.length_cons,Nat.succ_mul xs.length (8*width+8)]; omega
    simpa only [he, List.nil_append] using (htrace.append hft).cons_tick

end DiagonalTallyBits

end BorderVNP
end Computability
end OAI
