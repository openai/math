import OAI.Computability.NearSquareRoot.ScheduleGeneratorSyntaxPublicRun
import OAI.Computability.NearSquareRoot.UniformMultiplicationRelease

/-! # Effective raw-tape interfaces for named multiplication bodies

The time and space certificates refer to the same command whose syntax is
emitted. The two fixed interfaces use only register zero.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace GeneratorSyntax.Pack

open IntegerMultiplication IntegerMultiplication.Code Space CommonRegisters

/-- Specification of a particular body and complexity constant inside a multiplication task. -/
def MultiplicationBody (p : Cmd) (T : ℕ → ℕ) (S C : ℕ) (z : MultiplicationInput → List Bool) : Prop :=
  ∀ i env r base, (∀ j, (letters r j).length ≤ base) →
    BoundedFits env p (pile 0 (send i.operands) r) (pile 0 (send (z i)) r)
      (C*(T i.width+1)) (base+C*(S*i.width+1)) (C*(S*i.width+1))

theorem multiplicationTask_iff (T : ℕ → ℕ) (S : ℕ) (z : MultiplicationInput → List Bool) :
    MultiplicationTask T S z ↔ ∃ p C, MultiplicationBody p T S C z := Iff.rfl

def multiplyWrap (p : Cmd) : Cmd := Schoolbook.loadCmd.join (p.join Schoolbook.unloadCmd)

theorem effective_multiplyWrap [Fintype Ltr] {X : Type} [Primcodable X] {p : X → Cmd}
    (h : Effective ltr p) : Effective ltr (fun j => multiplyWrap (p j)) :=
  (effective_const ltr Schoolbook.loadCmd).join (h.join (effective_const ltr Schoolbook.unloadCmd))

open private inList go codeX codeY outList from OAI.Computability.IntegerMultiplication.Interface

private theorem within_inList {R : ℕ} (hR : 0 < R) {a b : Cmd} (ha : Within R a) (hb : Within R b) :
    Within R (inList a b) := by
  refine ⟨hR,?_⟩
  rintro (_ | (b | _ | _)) <;> simp [Within,hR,ha,hb]

theorem within_multiplyWrap {R : ℕ} (hR : 0 < R) {p : Cmd} (hp : Within R p) :
    Within R (multiplyWrap p) := by
  refine ⟨?_,hp,?_⟩
  · unfold Schoolbook.loadCmd go
    refine ⟨?_,hR⟩
    apply within_inList hR _ (by trivial)
    exact ⟨within_inList hR (by trivial) hR,hR⟩
  · change Within R outList
    refine ⟨hR,?_⟩
    rintro (_ | (b | _ | _)) <;> refine ⟨hR,?_⟩ <;> try trivial
    refine ⟨hR,?_⟩
    rintro (_ | (b | _ | _)) <;> simp [Within,hR]

private theorem raw_height (s : List Ltr) (j : ℕ) : (Schoolbook.raw s j).length ≤ s.length := by
  by_cases h : j = 0 <;> simp [Schoolbook.raw,h]

/-- Physical input/output wrappers for one bounded run at one width. The
space allowance can depend arbitrarily on the operands. -/
theorem multiplyWrap_at {p : Cmd} {C allowance time : ℕ}
    (i : MultiplicationInput) (z : List Bool) (length : z.length = 2*i.width)
    (body : BoundedFits [] p (pile 0 (send i.operands) (fun _ => []))
      (pile 0 (send z) (fun _ => [])) (C*(time+1)) (C*(allowance+1)) (C*(allowance+1))) :
    let n := i.width
    let cap := C*(allowance+1)+64*(n+1)
    ∃ t ≤ (C+46)*(time+n+1), BoundedRun cap cap [] (multiplyWrap p)
      (Schoolbook.raw (rawPair i.operands.1 i.operands.2)) t (Schoolbook.raw (z.map Ltr.bit)) := by
  let n := i.width
  let x := i.operands.1
  let y := i.operands.2
  have hx : x.length = n := rfl
  have hy : y.length = n := i.val.property.symm
  let cap := C*(allowance+1)+64*(n+1)
  let src := rawPair x y
  have hload := Schoolbook.load_run x y []
  have loadHeight (j : ℕ) : (Schoolbook.raw src j).length + (17+11*(x.length+y.length)) ≤ cap := by
    apply (Nat.add_le_add_right (raw_height _ _) _).trans
    simp only [src,CommonAlphabet.Pipeline.srcWord,List.length_append,List.length_cons,
      List.length_map,hx,hy]
    dsimp only [cap]
    omega
  have loadDepth : 17+11*(x.length+y.length)+1 ≤ cap := by
    dsimp only [cap]
    rw [hx,hy]
    omega
  have load := BoundedRun.clock (depth := 17+11*(x.length+y.length)) hload loadHeight le_rfl
  obtain ⟨u,hu,core⟩ := body
  simp only [Schoolbook.letters_pile_empty] at core
  change u ≤ C*(time+1) at hu
  have core' := core.mono (show C*(allowance+1) ≤ cap by dsimp only [cap]; omega) le_rfl
  have encodedLength : (send z).spell.length = 4*n+1 := by
    rw [Tree.spell_length]
    change size _ = _
    rw [Bits.size_word,length]
    dsimp only [n]
    omega
  have endHeight (j : ℕ) : (Schoolbook.raw (send z).spell j).length + (6+12*z.length) ≤ cap := by
    have h := raw_height (send z).spell j
    rw [encodedLength] at h
    change z.length = 2*n at length
    rw [length]
    dsimp only [cap]
    omega
  have unload := BoundedRun.clock (cap := cap) (depth := cap) (Schoolbook.unload_run z [])
    endHeight (by change z.length = 2*n at length; rw [length]; dsimp only [cap]; omega)
  have all := load.join (core'.join unload (by dsimp only [cap,n]; omega)) loadDepth
  refine ⟨_,?_,all⟩
  change z.length = 2*n at length
  rw [hx,hy,length]
  change _ ≤ (C+46)*(time+n+1)
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_one] at hu ⊢
  omega

/-- Raw delimited operands are replaced by a clean full-width output on register
zero. The certificates retain the named body, the same register bank and the
specified MSF output, including leading zeroes. -/
theorem multiplyWrap_run {p : Cmd} {T : ℕ → ℕ} {S C : ℕ} {z : MultiplicationInput → List Bool}
    (body : MultiplicationBody p T S C z) (i : MultiplicationInput)
    (length : (z i).length = 2*i.width) :
    let n := i.width
    let cap := (C*(S+1)+128)*n
    ∃ t ≤ (C+46)*(T n+n+1), BoundedRun cap cap [] (multiplyWrap p)
      (Schoolbook.raw (rawPair i.operands.1 i.operands.2)) t (Schoolbook.raw ((z i).map Ltr.bit)) := by
  let n := i.width
  have positive : 1 ≤ n := i.property
  have run := body i [] (fun _ => []) 0 (by intro j; rfl)
  simp only [Nat.zero_add] at run
  obtain ⟨u,time,exec⟩ := multiplyWrap_at i (z i) length run
  have space : C*(S*n+1)+64*(n+1) ≤ (C*(S+1)+128)*n := by
    have hsn : S*n+1 ≤ (S+1)*n := by rw [Nat.add_mul]; omega
    have hc := Nat.mul_le_mul_left C hsn
    rw [Nat.add_mul,Nat.mul_assoc]
    omega
  exact ⟨u,time,exec.mono space space⟩

/-- Apply the wrapped body to arbitrary equal-width public operands. -/
theorem multiplyWrap_product {p : Cmd} {T : ℕ → ℕ} {S C : ℕ} {z : MultiplicationInput → List Bool}
    (body : MultiplicationBody p T S C z)
    (correct : ∀ i, (z i).length = 2*i.width ∧ bitValue (z i) = bitValue i.operands.1 * bitValue i.operands.2)
    (n : ℕ) (hn : 0 < n) (x y : List Bool) (hx : x.length = n) (hy : y.length = n) :
    let cap := (C*(S+1)+128)*n
    ∃ (out : List Bool) (t : ℕ), out.length = 2*n ∧ bitValue out = bitValue x * bitValue y ∧
      t ≤ (C+46)*(T n+n+1) ∧ BoundedRun cap cap [] (multiplyWrap p)
        (Schoolbook.raw (rawPair x y)) t (Schoolbook.raw (out.map Ltr.bit)) := by
  let i : MultiplicationInput := ⟨⟨(x,y),hx.trans hy.symm⟩,hx ▸ hn⟩
  have width : i.width = n := hx
  obtain ⟨len,value⟩ := correct i
  obtain ⟨t,time,run⟩ := multiplyWrap_run body i len
  rw [width] at len time run
  exact ⟨z i,t,len,value,time,run⟩

end GeneratorSyntax.Pack

end NearSquareRoot
end Computability
end OAI
