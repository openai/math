import OAI.Computability.BorderVNP.DiagonalPositiveHeaderRead
import OAI.Computability.BorderVNP.CubeRouteHeaderCapacity
import OAI.Computability.BorderVNP.PackedHistoryBroadcastRAM

/-! # Parsing the full physical positive header at its exact reserved width -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TeamContraction.JointHeader

open VPVNP.BurstRAM Cube.Physical Cube.DeclarationBits

/-- The three fields after the positive tag. The cube declaration uses only its
actual upper-triangle spelling. The final bank has one word per team and tally coordinate. -/
@[ext] structure PositiveFields (reserve axes groups cap teams dim tally : ℕ) where
  /-- Padded profile bank read by the geometry guard. -/
  profile : Fin reserve → Bool
  /-- Raw coordinate and all compact row declarations, before semantic checks. -/
  cube : Broadcast axes groups cap
  /-- All transmitted little-endian subtotal bits in row-major order. -/
  subtotals : Fin (teams*dim*tally) → Bool

namespace PositiveFields

variable {reserve axes groups cap teams dim tally : ℕ}
local notation "Fields" => PositiveFields reserve axes groups cap teams dim tally

/-- Full positive-header length including its single branch bit. -/
def width (reserve axes groups cap teams dim tally : ℕ) :=
  1+reserve+Cube.DeclarationBits.length axes groups cap+teams*dim*tally

/-- Raw input bits of this header, before evaluating any guessed field. -/
def bits (p : Fields) : List Bool :=
  true :: (List.ofFn p.profile ++ (Cube.DeclarationBits.spelling p.cube ++ List.ofFn p.subtotals))

theorem bits_length (p : Fields) : p.bits.length = width reserve axes groups cap teams dim tally := by
  simp only [bits,List.length_cons,List.length_append,List.length_ofFn,Cube.DeclarationBits.spelling_length,width]
  omega

private def listWord {width : ℕ} (xs : List Bool) (h : xs.length = width) (j : Fin width) : Bool :=
  xs[j.val]'(j.isLt.trans_eq h.symm)

private theorem ofFn_listWord {width : ℕ} (xs : List Bool) (h : xs.length = width) : List.ofFn (listWord xs h) = xs := by
  subst width
  exact List.ofFn_get xs

private theorem ofFn_wordEquiv (c : Broadcast axes groups cap) :
    List.ofFn (Cube.DeclarationBits.wordEquiv axes groups cap c) = Cube.DeclarationBits.spelling c :=
  ofFn_listWord _ (Cube.DeclarationBits.spelling_length c)

/-- Equal complete physical headers have equal raw profile, cube fields and subtotal bits. -/
theorem bits_injective : Function.Injective (bits (reserve:=reserve) (axes:=axes) (groups:=groups) (cap:=cap)
    (teams:=teams) (dim:=dim) (tally:=tally)) := by
  intro p q h
  have eq := (List.cons.inj h).2
  have cut := List.append_inj eq (by simp)
  have rest := List.append_inj cut.2 (by simp [Cube.DeclarationBits.spelling_length])
  exact PositiveFields.ext (List.ofFn_inj.mp cut.1) (Cube.DeclarationBits.spelling_injective rest.1)
    (List.ofFn_inj.mp rest.2)

/-- Every positive physical header of exactly the specified length has precisely
one raw parse, even when its cube codes or tally numbers are invalid. -/
theorem unique_parse (raw : List Bool) (size : raw.length = width reserve axes groups cap teams dim tally)
    (tag : raw.head? = some true) : ∃! p : Fields, p.bits = raw := by
  cases raw with
  | nil => simp at tag
  | cons first rest =>
    obtain rfl : first = true := by simpa using tag
    let D := Cube.DeclarationBits.length axes groups cap
    let x := rest.take reserve
    let y := (rest.drop reserve).take D
    let z := (rest.drop reserve).drop D
    have len : rest.length = reserve + D + teams*dim*tally := by simp only [List.length_cons,width] at size; dsimp [D]; omega
    have hx : x.length = reserve := by simp [x,len]; omega
    have hy : y.length = D := by simp [y,len]; omega
    have hz : z.length = teams*dim*tally := by simp [z,len]
    let cube := (Cube.DeclarationBits.wordEquiv axes groups cap).symm (listWord y hy)
    let p : Fields := ⟨listWord x hx,cube,listWord z hz⟩
    have hc : Cube.DeclarationBits.spelling cube = y := by
      rw [← ofFn_wordEquiv cube]
      exact (congrArg List.ofFn ((Cube.DeclarationBits.wordEquiv axes groups cap).apply_symm_apply _)).trans
        (ofFn_listWord y hy)
    have whole : p.bits = true :: rest := by
      change true :: (List.ofFn (listWord x hx) ++ (Cube.DeclarationBits.spelling cube ++ List.ofFn (listWord z hz))) = _
      rw [ofFn_listWord,hc,ofFn_listWord]
      simp [x,y,z]
    exact ⟨p,whole,fun q h => bits_injective (h.trans whole.symm)⟩

/-- The actual row-major fields fed to the tally bit decoder. -/
def tallyWords (p : Fields) := splitFields tally (teams*dim) (List.ofFn p.subtotals)

theorem tallyWords_flatten (p : Fields) : p.tallyWords.flatten = List.ofFn p.subtotals :=
  splitFields_flatten tally (teams*dim) _ List.length_ofFn

theorem tallyWords_length (p : Fields) : p.tallyWords.length = teams*dim := by simp [tallyWords,splitFields]

theorem tallyWords_width (p : Fields) : ∀ xs ∈ p.tallyWords, xs.length = tally :=
  splitFields_width tally (teams*dim) _ List.length_ofFn

/-- Read all three fields at the real addresses written by the physical startup copy. -/
theorem copied {w : ℕ} (hw : 0<w) (p : Fields) {mem : Memory w} {dst : ℕ} (h : FlatAt mem dst p.bits) :
    PackedHistoryCircuit.profileRAM mem dst = p.profile ∧
      FlatAt mem (dst+1+reserve) (Cube.DeclarationBits.spelling p.cube) ∧
      DiagonalTallyBits.WordsAt mem (dst+1+reserve+Cube.DeclarationBits.length axes groups cap) p.tallyWords := by
  have tail := FlatAt.right (xs:=[true]) (ys:=List.ofFn p.profile ++ (Cube.DeclarationBits.spelling p.cube ++ List.ofFn p.subtotals)) h
  have dcl : FlatAt mem (dst+1+reserve) (Cube.DeclarationBits.spelling p.cube ++ List.ofFn p.subtotals) := by
    simpa only [List.length_ofFn,List.length_cons,List.length_nil] using tail.right
  refine ⟨?_,dcl.left,?_⟩
  · funext i
    have hi := tail.left ⟨i.val,by simp⟩
    change mem (dst+1+i.val) = DiagonalResidueRAM.word w (List.ofFn p.profile)[i.val].toNat at hi
    simp only [List.getElem_ofFn] at hi
    change decide ((mem (dst+1+i.val)).val=1) = p.profile i
    rw [hi,DiagonalResidueRAM.word_val _ _ ((Bool.toNat_lt _).trans_le (Nat.one_lt_two_pow hw.ne'))]
    cases p.profile i <;> rfl
  · apply fieldsFromFlat hw
    rw [tallyWords_flatten]
    simpa only [Cube.DeclarationBits.spelling_length] using dcl.right

end PositiveFields
end TeamContraction.JointHeader

end BorderVNP
end Computability
end OAI
