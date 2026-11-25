import OAI.Computability.BorderVNP.DiagonalTallySidecar
import OAI.Computability.BorderVNP.DiagonalTallyRAMTrace
import OAI.Computability.BorderVNP.RoutingISANatural

/-! # Native decoding of the delivered weighted-site directory -/

namespace OAI
namespace Computability
namespace BorderVNP

namespace TallySidecar

open VPVNP.BurstRAM VPVNP.TapeWord RoutingISA DiagonalResidueRAM DiagonalTallyBits

/-- The first field is the number of marked positions. The raw start, width, and
packed destination are passed by the bundle traversal in registers 16, 17 and 20. -/
def headerSetup : Code := .block [.copy 50 16,.constant 51 1,.copy 52 17,.copy 53 20,.constant 63 1]

/-- Compute the number of subsequent fields by reading the actual packed count. -/
def rowsSetup : Code := .block [.load 51 20,.constant 58 3,.binary .mul 51 51 58]

/-- Decode the count, then the indicated number of three-field rows. -/
def decode : Code := .block [headerSetup,pack,rowsSetup,pack]

/-- Decoding the literal string writes exactly the packed count and metadata fields.
Every other register below 40 is available to the surrounding bundle traversal. -/
theorem decode_runs {w : ℕ} (pub : Arg → Word w) (mac : TeamOpcode.Macros w 8)
    (s : Bank w) (m : Memory w) (p d H : ℕ) (ps : List Position)
    (hp : (s 16).val=p) (hh : (s 17).val=H) (hd : (s 20).val=d)
    (hw : H ≤ w) (room : 3<2^w)
    (hfit : p+(1+3*ps.length)*H<2^w) (hdest : d+(1+3*ps.length)<2^w)
    (sep : p+(1+3*ps.length)*H ≤ d ∨ d+(1+3*ps.length) ≤ p)
    (valid : Fits H ps) (raw : WordsAt m p (words H ps)) :
    ∃ es t, Runs pub mac decode s m es t (outputMemory m d (words H ps)) ∧
      traceCost es ≤ headerSetup.slots + DiagonalTallyBits.ticks 1 H + rowsSetup.slots + DiagonalTallyBits.ticks (3*ps.length) H ∧
      (∀ j : Reg, j.val<40 → t j=s j) ∧ (t 53).val=d+1+3*ps.length := by
  let head := wordBits (word H ps.length)
  let rest := (ps.flatMap Position.fields).map (fun k => wordBits (word H k))
  have hwords : words H ps=head::rest := rfl
  have hlen : rest.length=3*ps.length := by
    have e := fields_length ps
    simp only [fields,List.length_cons] at e
    simp only [rest,List.length_map]
    omega
  have headLen : head.length=H := by simp [head]
  have allLen : ∀ b∈rest,b.length=H := by
    intro b hb
    obtain ⟨k,_,rfl⟩ := List.mem_map.mp hb
    simp
  have headVal : value head=ps.length := by
    simp [head,value_wordBits,word_val H ps.length (valid ps.length (by simp [fields]))]
  rw [hwords] at raw ⊢
  have raw₁ : WordsAt m p [head] := ⟨raw.1,trivial⟩
  have raw₂ : WordsAt m (p+H) rest := headLen ▸ raw.2
  have space₁ : p+H<2^w := by simp only [Nat.add_mul,Nat.one_mul] at hfit; omega
  have hwpos : w≠0 := by rintro rfl; simp at room
  have lowScratch (j : Reg) (hj : j.val<40) : j∉scratch := by
    intro hin
    have lb : ∀ x∈scratch, 40 ≤ x.val := by decide
    have := lb j hin
    omega
  have safe : headerSetup.safeReadOnly w (readings pub) (readings m) (readings s) := by
    simp [headerSetup,Code.block,Code.safeReadOnly,hwpos]
  obtain ⟨a,s₁,r₁,c₁,e₁⟩ := headerSetup.runReadOnly pub mac m s safe
  have state₁ : (s₁ 50).val=p ∧ (s₁ 53).val=d ∧ (s₁ 51).val=1 ∧
      (s₁ 52).val=H ∧ (s₁ 63).val=1 := by
    change readings s₁ 50=p ∧ readings s₁ 53=d ∧ readings s₁ 51=1 ∧
      readings s₁ 52=H ∧ readings s₁ 63=1
    rw [e₁]
    simp [headerSetup,Code.block,Code.evalNat,readings,Function.update,hp,hh,hd]
  obtain ⟨sp,sd,sc,sw,sone⟩ := state₁
  have sep₁ : p+H ≤ d ∨ d+1 ≤ p := by simp only [Nat.add_mul,Nat.one_mul] at sep; omega
  obtain ⟨b,s₂,r₂,cb,pr₂,sp₂,sd₂⟩ := pack_runs pub mac s₁ m [head] sp sd sc sw sone hw
    (by simpa using headLen) (by simpa using space₁) (by simp; omega) (by simpa using sep₁) raw₁
  let m₂ := outputMemory m d [head]
  have val₂ : (m₂ d).val=ps.length := by
    have e := outputMemory_word_val m d [head] 0 (by simp) (by simpa using headLen.trans_le hw)
    simpa [headVal] using e
  have below₁ (j : Reg) (hj : j.val<40) : s₁ j=s j := Fin.ext ((congrFun e₁ j).trans
    (headerSetup.evalNat_protected _ _ _ (show headerSetup.protects 40 = true by decide) _ hj))
  have below₂ (j : Reg) (hj : j.val<40) : s₂ j=s j := (pr₂ j (lowScratch j hj)).trans (below₁ j hj)
  have d₂ : (s₂ 20).val=d := (congrArg Fin.val (below₂ 20 (by decide))).trans hd
  have safe₂ : rowsSetup.safeReadOnly w (readings pub) (readings m₂) (readings s₂) := by
    simp [rowsSetup,Code.block,Code.safeReadOnly,Code.evalNat,Function.update,readings,
      addressOpFits,d₂,val₂]
    omega
  obtain ⟨c,s₃,r₃,c₃,e₃⟩ := rowsSetup.runReadOnly pub mac m₂ s₂ safe₂
  have state₃ : (s₃ 50).val=p+H ∧ (s₃ 53).val=d+1 ∧ (s₃ 51).val=rest.length ∧
      (s₃ 52).val=H ∧ (s₃ 63).val=1 := by
    have sw₂ := (congrArg Fin.val (pr₂ 52 (by decide))).trans sw
    have one₂ := (congrArg Fin.val (pr₂ 63 (by decide))).trans sone
    change readings s₃ 50=p+H ∧ readings s₃ 53=d+1 ∧ readings s₃ 51=rest.length ∧
      readings s₃ 52=H ∧ readings s₃ 63=1
    rw [e₃]
    simp [rowsSetup,Code.block,Code.evalNat,Function.update,readings,addressOp,d₂,val₂,hlen,
      sw₂,one₂, Nat.mul_comm] at ⊢
    simpa using And.intro sp₂ sd₂
  have sep₂ : p+H+rest.length*H ≤ d+1 ∨ d+1+rest.length ≤ p+H := by
    rw [hlen]
    simp only [Nat.add_mul,Nat.one_mul] at sep
    omega
  have raw' : WordsAt m₂ (p+H) rest := words_congr m m₂ (p+H) H rest raw₂ allLen (by
    intro j hj hlo
    apply outputMemory_outside
    rw [hlen] at hlo
    simp only [Nat.add_mul,Nat.one_mul] at sep
    simp; omega)
  obtain ⟨sp₃,sd₃,sc₃,sw₃,one₃⟩ := state₃
  obtain ⟨e,t,r₄,ce,pr₄,_,dt⟩ := pack_runs pub mac s₃ m₂ rest sp₃ sd₃ sc₃ sw₃ one₃ hw allLen
    (by rw [hlen]; simpa [Nat.add_mul,Nat.add_assoc] using hfit)
    (by rw [hlen]; omega) sep₂ raw'
  have run := r₁.seq (r₂.seq (r₃.seq r₄))
  refine ⟨_,t,run,?_,?_,by simpa only [hlen] using dt⟩
  · have cb' := (DiagonalTallyRAM.ordinary_cost (show DiagonalTallyRAM.ordinary pack=true by decide) r₂).trans cb.1
    have ce' := (DiagonalTallyRAM.ordinary_cost (show DiagonalTallyRAM.ordinary pack=true by decide) r₄).trans ce.1
    simp only [List.length_singleton,hlen] at cb' ce'
    unfold traceCost
    simp only [VPVNP.RAMBuckets.cost_append]
    change traceCost a+(traceCost b+(traceCost c+traceCost e)) ≤ _
    omega
  · intro j hj
    have outside := lowScratch j hj
    exact (pr₄ j outside).trans ((Fin.ext ((congrFun e₃ j).trans
      (rowsSetup.evalNat_protected _ _ _ (show rowsSetup.protects 40=true by decide) _ hj))).trans (below₂ j hj))

end TallySidecar

end BorderVNP
end Computability
end OAI
