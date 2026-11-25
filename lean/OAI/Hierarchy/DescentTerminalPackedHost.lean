import OAI.Hierarchy.DescentTerminalPaidRows
import OAI.Hierarchy.DescentTerminalHost

namespace OAI
/-! # A single terminal host measured on the total number of purchased rows -/

namespace Hierarchy.DescentTerminalHost
open Catalyst CatalystSubstitution ThreeFlat Routing
open Computability.BorderVNP.Crossing DescentTerminalPorts ProtocolStackContraction Tagged
open scoped Classical BigOperators
noncomputable section

variable {G H P : Type} [Fintype H] {F : Type} [Field F] {geo rows word bins W k p h calls : ℕ} {bits : P→ℕ}

/-- Terminal graph, its actual local coefficients, and distinct locations
for its active cable bits in one purchased array shared by all choices. -/
structure PackedTerm (F : Type) (geo : ℕ) (P : Type) (bits : P→ℕ) (rows word : ℕ) where
  graph : Network geo P bits
  table : graph.Tables F
  addr : CableBit graph ↪ RowBit rows word

def PackedTerm.ofVolume (N : Network geo P bits) (table : N.Tables F)
    (code : N.Edge ↪ ℕ) (paid : (∑e,N.width e)≤rows*word) : PackedTerm F geo P bits rows word :=
  ⟨N,table,denseBits N code paid⟩

def countDigit {t : ℕ} (query : Fin t → Fin bins) (u : Fin bins × Fin W) :=
  (Finset.univ.filter (fun i=>query i=u.1)).card.testBit u.2.val

variable (width : Fin k→ℕ) (Y : Approximation F k (Tagged.pins h h))
    (verify : BitNetwork F (Fintype.card (Catalyst.Port p width ⊕ H))) (scalar : Fin bins→F)
    (dataPin : DescentTerminalLocalFactors.Pin (RowBit rows word) bins W→Catalyst.Port p width ⊕ H)
    (callsPin : Fin calls→Fin (Tagged.pins h h)→(Catalyst.Port p width ⊕ H) ⊕ Bool)

def packedHost := host width (CollapseOracle.tagCall h Y) calls (logic verify scalar dataPin) callsPin

theorem packedHost_size :
    hostSize (packedHost width Y verify scalar dataPin callsPin) =
      (verify.cells+verify.internal)+(rows*word+bins*W)+29*(calls*Tagged.pins h h)+
      Fintype.card H+Fintype.card (Catalyst.Port p width) := by
  calc
    _ = (logic verify scalar dataPin).cells+(logic verify scalar dataPin).internal+
          29*(calls*Tagged.pins h h)+Fintype.card H+Fintype.card (Catalyst.Port p width) :=
      host_price width (CollapseOracle.tagCall h Y) calls (logic verify scalar dataPin) callsPin
    _ = _ := by
      rw [logic_size verify scalar dataPin]
      simp only [RowBit,Fintype.card_prod,Fintype.card_fin]

theorem packedHost_value [Fintype G] (term : G→PackedTerm F geo P bits rows word) (weight : G→F)
    (x : Catalyst.Port p width→Bool) (outer : Ports bits) (count : G→ℕ) (fit : ∀t,count t<2^W)
    (query : ∀t,(RowBit rows word→Bool)→Fin (count t)→Fin bins)
    (entry : ∀t pay, (∏i,scalar (query t pay i))=weight t*
      ∏v,(term t).graph.read (term t).table (takeBits (term t).graph (term t).addr pay) outer v)
    (decode : (H→Bool)→Option (G×(RowBit rows word→Bool)))
    (unique : ∀st,∃! a,decode a=some st)
    (auth : ∀a,(∏i,coeff F h h (Sum.elim (Sum.elim x a) id ∘ callsPin i))*
      TypedWiring.value verify (Sum.elim x a)=if (decode a).isSome then 1 else 0)
    (digits : ∀a t pay,decode a=some (t,pay)→Sum.elim x a ∘ dataPin =
      DescentTerminalLocalFactors.pins (zeroMask (term t).graph (term t).addr) pay (countDigit (query t pay))) :
    exactValue _ (packedHost width Y verify scalar dataPin callsPin) x =
      ∑t,weight t*(term t).graph.value (term t).table outer := by
  let f (a : H→Bool) : F := (∏i,coeff F h h (Sum.elim (Sum.elim x a) id ∘ callsPin i))*
    TypedWiring.value (logic verify scalar dataPin) (Sum.elim x a)
  let g (st : G×(RowBit rows word→Bool)) : F :=
    let t:=term st.1
    weight st.1*(if ZeroUnused t.graph t.addr st.2 then
      ∏ v,t.graph.read t.table (takeBits t.graph t.addr st.2) outer v else 0)
  calc
    _ = ∑a,f a :=
      exact_host width (CollapseOracle.tagCall h Y) calls (logic verify scalar dataPin) callsPin x
    _ = ∑st,g st := by
      apply sum_decoded decode unique f g
      · intro a bad
        dsimp only [f]
        rw [logic_value,←mul_assoc,auth,bad]
        simp
      · rintro a ⟨t,pay⟩ good
        dsimp only [f,g]
        rw [logic_value,←mul_assoc,auth,good]
        simp only [Option.isSome_some,ite_true,one_mul]
        rw [digits a t pay good,DescentTerminalLocalFactors.network_value]
        rw [if_congr (mask_ok (term t).graph (term t).addr pay) rfl rfl]
        rw [show (∏b:Fin bins,∏j:Fin W,if countDigit (query t pay) (b,j) then scalar b^(2^j.val) else 1)=
          ∏i,scalar (query t pay i) from by
            convert (table_histogram_bits (query t pay) scalar W (by simpa using fit t)).symm using 1
            apply Finset.prod_congr rfl
            intro b _
            apply Finset.prod_congr rfl
            intro j _
            exact congrArg (fun s : Finset (Fin (count t)) =>
              if s.card.testBit j.val then scalar b^(2^j.val) else 1)
              (@Finset.filter_congr_decidable _ Finset.univ (fun i => query t pay i=b)
                (fun _ => inferInstance) (fun _ => Classical.propDecidable _))]
        rw [entry]
        split_ifs <;> simp
    _ = _ := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro t _
      dsimp only [g]
      rw [←Finset.mul_sum]
      apply congrArg (weight t * ·)
      refine Eq.trans ?_ (value_pool (term t).graph (term t).addr (term t).table outer)
      refine Finset.sum_congr ?_ (fun _ _ => rfl)
      exact congrArg (fun i : Fintype (RowBit rows word → Bool) =>
        @Finset.univ (RowBit rows word → Bool) i) (Subsingleton.elim _ _)

end
end Hierarchy.DescentTerminalHost

end OAI
