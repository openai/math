import OAI.Computability.BorderVNP.CellCQFPairCost
import OAI.Computability.BorderVNP.CellCQFPrimitiveCosts
import OAI.Computability.BorderVNP.CellCQFTabulateCost
import OAI.Computability.QuantumFactoring.BitStackListMapWith
import OAI.Computability.QuantumFactoring.BitStackListMapIdx

/-! # Actual cost of the private cell compiler's environment-indexed list maps

The program builds a quoted argument from the common environment, the current index, and
the selected list entry. Its child cost is charged only on that particular argument.
-/

namespace OAI
namespace Computability
namespace BorderVNP

namespace StackProcedure

open _root_.OAI.ExactQuantumFactoring _root_.OAI.ExactQuantumFactoring.BitStackProgram
open _root_.OAI.ExactQuantumFactoring.BitStackProgram.Procedure

variable {A B T : Type} (ea : A → List Bool) (eb : B → List Bool)

private abbrev mapEnvCode := prodCode ea (listCode eb)

private noncomputable abbrev mapIndex :=
  unaryToBits.comp (first unaryCode (mapEnvCode ea eb))

private noncomputable abbrev mapEnv := second unaryCode (mapEnvCode ea eb)

private noncomputable abbrev mapParam :=
  (first ea (listCode eb)).comp (mapEnv ea eb)

private noncomputable abbrev mapList :=
  (second ea (listCode eb)).comp (mapEnv ea eb)

private noncomputable abbrev mapGet (d : B) :=
  (listGet eb d).comp ((mapIndex ea eb).pair (mapList ea eb))

private noncomputable abbrev mapArg (d : B) :=
  (mapParam ea eb).pair (mapGet ea eb d)

private noncomputable abbrev mapIdxArg (d : B) :=
  (mapParam ea eb).pair ((mapIndex ea eb).pair (mapGet ea eb d))

private noncomputable abbrev mapInput (d : B) :=
  ((NativeAIG.Emission.listUnaryLength eb d).comp (second ea (listCode eb))).pair
    (identity (mapEnvCode ea eb))

private theorem map_arg_bounds (d : B) : ∃ K : ℕ, ∀ x : A × List B, ∀ i < x.2.length,
    (mapArg ea eb d).cost (i,x) ≤ K*((mapEnvCode ea eb x).length+1)^9 ∧
    (mapIdxArg ea eb d).cost (i,x) ≤ K*((mapEnvCode ea eb x).length+1)^9 := by
  let U := unaryToBits.bound.eval 1
  let G := (listGet eb d).bound.eval 1
  let K := 10^32 * (U + 4^9 * G + 1)
  refine ⟨K,fun x i hi => ?_⟩
  let s := (mapEnvCode ea eb x).length+1
  let r := s^9
  have hs : 0 < s := Nat.zero_lt_succ _
  have sr : s ≤ r := by simpa only [pow_one] using
    (Nat.pow_le_pow_right hs (show 1 ≤ 9 by decide))
  have s2 : s^2 ≤ r := Nat.pow_le_pow_right hs (by decide)
  have hbits : i.bits.length ≤ i := by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr Nat.lt_two_pow_self
  have hn := list_length_le_code eb x.2
  have henv : (mapEnvCode ea eb x).length = 2*(ea x.1).length + (listCode eb x.2).length + 1 := by
    simp only [mapEnvCode,prodCode,pairBits_length]
  have hi1 : i+1 ≤ s := by dsimp [s]; omega
  have hl : (listCode eb x.2).length+1 ≤ s := by dsimp [s]; omega
  have ha : (ea x.1).length+1 ≤ s := by dsimp [s]; omega
  have ht : (prodCode unaryCode (mapEnvCode ea eb) (i,x)).length+1 ≤ 4*s := by
    simp only [prodCode,pairBits_length,unaryCode,List.length_replicate]
    dsimp only [s] at hi1 ⊢
    omega
  have hb : (prodCode Nat.bits (listCode eb) (i,x.2)).length+1 ≤ 4*s := by
    simp only [prodCode,pairBits_length]; omega
  have hu := cost_unaryToBits i
  simp only [unaryCode,List.length_replicate] at hu
  have ui := hu.trans (Nat.mul_le_mul_left U ((Nat.pow_le_pow_left hi1 2).trans s2))
  have gi := (cost_listGet eb d (i,x.2)).trans
    (Nat.mul_le_mul_left G (Nat.pow_le_pow_left hb 9))
  rw [Nat.mul_pow] at gi
  have fi := cost_first unaryCode (mapEnvCode ea eb) (i,x)
  have ei := cost_second unaryCode (mapEnvCode ea eb) (i,x)
  have ax := cost_first ea (listCode eb) x
  have lx := cost_second ea (listCode eb) x
  have ci := cost_comp unaryToBits (first unaryCode (mapEnvCode ea eb)) (i,x)
  have ca := cost_comp (first ea (listCode eb)) (mapEnv ea eb) (i,x)
  have cl := cost_comp (second ea (listCode eb)) (mapEnv ea eb) (i,x)
  have cp := cost_pair (mapIndex ea eb) (mapList ea eb) (i,x)
  have cg := cost_comp (listGet eb d) ((mapIndex ea eb).pair (mapList ea eb)) (i,x)
  have cp' := cost_pair (mapIndex ea eb) (mapGet ea eb d) (i,x)
  have b := cost_pair (mapParam ea eb) (mapGet ea eb d) (i,x)
  have bi := cost_pair (mapParam ea eb) ((mapIndex ea eb).pair (mapGet ea eb d)) (i,x)
  change unaryToBits.cost i ≤ U*r at ui
  change (listGet eb d).cost (i,x.2) ≤ G*(4^9*r) at gi
  change (mapEnv ea eb).cost (i,x) ≤ _ at ei
  rw [Nat.mul_left_comm G (4^9) r] at gi
  change (mapIndex ea eb).cost (i,x) ≤ unaryToBits.cost i+(4*(unaryCode i).length+2)+_ at ci
  change (mapParam ea eb).cost (i,x) ≤ (first ea (listCode eb)).cost x+
    (4*(mapEnvCode ea eb x).length+2)+_ at ca
  change (mapList ea eb).cost (i,x) ≤ (second ea (listCode eb)).cost x+
    (4*(mapEnvCode ea eb x).length+2)+_ at cl
  change (mapGet ea eb d).cost (i,x) ≤ (listGet eb d).cost (i,x.2)+
    (4*(prodCode Nat.bits (listCode eb) (i,x.2)).length+2)+_ at cg
  change (first ea (listCode eb)).cost x ≤ 16*s at ax
  change (second ea (listCode eb)).cost x ≤ 64*s at lx
  change (mapArg ea eb d).cost (i,x) ≤ _ at b
  change (mapIdxArg ea eb d).cost (i,x) ≤ _ at bi
  change (mapArg ea eb d).cost (i,x) ≤ K*r ∧ (mapIdxArg ea eb d).cost (i,x) ≤ K*r
  have hr : 1 ≤ r := hs.trans_le sr
  have henv' : (mapEnvCode ea eb x).length+1 = s := rfl
  simp only [unaryCode,List.length_replicate] at ci
  simp only [K,Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.one_mul] at *
  norm_num at gi ⊢
  omega

private theorem map_input_bounds (d : B) : ∃ K : ℕ, ∀ x : A × List B,
    (mapInput ea eb d).cost x ≤ K*((mapEnvCode ea eb x).length+1)^2 := by
  let U := (NativeAIG.Emission.listUnaryLength eb d).bound.eval 1
  refine ⟨10^12*(U+1),fun x => ?_⟩
  let s := (mapEnvCode ea eb x).length+1
  have hl : (listCode eb x.2).length+1 ≤ s := by simp only [s,mapEnvCode,prodCode,pairBits_length]; omega
  have su : s ≤ s^2 := by simpa only [pow_one] using
    (Nat.pow_le_pow_right (Nat.zero_lt_succ _) (show 1 ≤ 2 by decide))
  have hu := (cost_listUnaryLength eb d x.2).trans
    (Nat.mul_le_mul_left U (Nat.pow_le_pow_left hl 2))
  have hp := cost_second ea (listCode eb) x
  have hc := cost_comp (NativeAIG.Emission.listUnaryLength eb d) (second ea (listCode eb)) x
  have hi := cost_identity (mapEnvCode ea eb) x
  have h := cost_pair ((NativeAIG.Emission.listUnaryLength eb d).comp (second ea (listCode eb)))
    (identity (mapEnvCode ea eb)) x
  change (mapInput ea eb d).cost x ≤ 10^9*(_+_+(mapEnvCode ea eb x).length+1) at h
  change (second ea (listCode eb)).cost x ≤ 64*s at hp
  change _ ≤ (NativeAIG.Emission.listUnaryLength eb d).cost x.2+(4*(listCode eb x.2).length+2)+_ at hc
  change (mapInput ea eb d).cost x ≤ 10^12*(U+1)*s^2
  have hs : 0 < s := Nat.zero_lt_succ _
  have hs' : (mapEnvCode ea eb x).length+1=s := rfl
  simp only [Nat.add_mul,Nat.mul_add,Nat.mul_assoc,Nat.one_mul]
  norm_num
  omega

/-- The tabulation wrapper charges the current argument preparation, the selected
child and the encoded table prefix. The constant depends only on the fixed
preparation code, result encoder and fallback value. -/
private theorem map_finish {D : Type} {ed : D → List Bool} {et : T → List Bool}
    {select : ℕ × (A × List B) → D} (arg : Procedure (prodCode unaryCode (mapEnvCode ea eb)) ed select)
    (d : B) (e : T) (H : ℕ)
    (hw : ∀ x : A × List B, ∀ i < x.2.length, (ed (select (i,x))).length ≤ 8*((mapEnvCode ea eb x).length+1))
    (hc : ∀ x : A × List B, ∀ i < x.2.length, arg.cost (i,x) ≤ H*((mapEnvCode ea eb x).length+1)^9) :
    ∃ K : ℕ, ∀ {f : D → T} (p : Procedure ed et f) (x : A × List B) {L C : ℕ},
    (∀ i < x.2.length, (et (f (select (i,x)))).length ≤ L) →
    (∀ i < x.2.length, p.cost (select (i,x)) ≤ C) →
    ((tabulate (f:=fun x i => f (select (i,x))) e (p.comp arg)).comp (mapInput ea eb d)).cost x ≤
      K*(x.2.length+1)*(C+((mapEnvCode ea eb x).length+1)^9+
        (tabSpan (mapEnvCode ea eb) x.2.length x L)^2+1) := by
  obtain ⟨I,hI⟩ := map_input_bounds ea eb d
  let M := 10^75*((listReverse et e).bound.eval 1+1)
  refine ⟨M*(H+35)+I+20,?_⟩
  intro f p x L C hL hC
  let s := (mapEnvCode ea eb x).length+1
  let n := x.2.length
  let span := tabSpan (mapEnvCode ea eb) n x L
  let V := C+s^9+span^2+1
  have hs : 0 < s := Nat.zero_lt_succ _
  have hsr : s ≤ s^9 := by simpa only [pow_one] using (Nat.pow_le_pow_right hs (show 1 ≤ 9 by decide))
  have hs2 : s^2 ≤ s^9 := Nat.pow_le_pow_right hs (by decide)
  have hn : n ≤ s := by
    have := list_length_le_code eb x.2
    simp only [n,s,mapEnvCode,prodCode,pairBits_length]; omega
  have hword : (prodCode unaryCode (mapEnvCode ea eb) (n,x)).length ≤ 4*s := by
    simp only [prodCode,pairBits_length,unaryCode,List.length_replicate]
    simp only [s,mapEnvCode,prodCode,pairBits_length] at hn ⊢; omega
  have hstep (i : ℕ) (hi : i < n) : (p.comp arg).cost (i,x) ≤ (H+34)*s^9+C := by
    have hp := cost_comp p arg (i,x)
    have hw' := hw x i hi
    have hc' := hc x i hi
    have hv := hC i hi
    change (ed (select (i,x))).length ≤ 8*s at hw'
    change arg.cost (i,x) ≤ H*s^9 at hc'
    rw [Nat.add_mul]
    omega
  have htab := cost_tabulate (f:=fun x i => f (select (i,x))) e (p.comp arg) n x hL hstep
  have hspan : (H+34)*s^9+C+span^2+1 ≤ (H+35)*V := by
    have hmono := Nat.mul_le_mul_left (H+34) (show s^9 ≤ V by dsimp [V]; omega)
    have hrest : C+span^2+1 ≤ V := by dsimp [V]; omega
    rw [show (H+35)*V=(H+34)*V+V by ring]
    omega
  have hb := htab.trans (Nat.mul_le_mul_left (M*(n+1)) hspan)
  let tab := tabulate (f:=fun x i => f (select (i,x))) e (p.comp arg)
  change tab.cost (n,x) ≤ M*(n+1)*((H+35)*V) at hb
  rw [show M*(n+1)*((H+35)*V)=(M*(H+35))*((n+1)*V) by ring] at hb
  have horig := cost_comp tab (mapInput ea eb d) x
  change (tab.comp (mapInput ea eb d)).cost x ≤ tab.cost (n,x)+
    (4*(prodCode unaryCode (mapEnvCode ea eb) (n,x)).length+2)+(mapInput ea eb d).cost x at horig
  have hVi : V ≤ (n+1)*V := by simpa using (Nat.mul_le_mul_right V (show 1 ≤ n+1 by omega))
  have hrV : s^9 ≤ V := by dsimp [V]; omega
  have him := (hI x).trans (Nat.mul_le_mul_left I ((hs2.trans hrV).trans hVi))
  change (tab.comp (mapInput ea eb d)).cost x ≤ (M*(H+35)+I+20)*(n+1)*V
  let Z := (n+1)*V
  rw [Nat.mul_assoc]
  change _ ≤ (M*(H+35)+I+20)*Z
  rw [Nat.add_mul (M*(H+35)+I) 20 Z, Nat.add_mul (M*(H+35)) I Z]
  change tab.cost (n,x) ≤ (M*(H+35))*Z at hb
  change (mapInput ea eb d).cost x ≤ I*Z at him
  change V ≤ Z at hVi
  omega

/-- Mapping a list with a common environment invokes the child once on each
actual list entry. A ninth power bounds indexed argument preparation, and a
quadratic term bounds manipulation of the partially constructed output table. -/
theorem cost_listMapWith (et : T → List Bool) (d : B) (e : T) :
    ∃ K : ℕ, ∀ {f : A → B → T} (p : Procedure (prodCode ea eb) et (fun y => f y.1 y.2))
      (x : A × List B) {L C : ℕ},
      (∀ b ∈ x.2, (et (f x.1 b)).length ≤ L) → (∀ b ∈ x.2, p.cost (x.1,b) ≤ C) →
      (listMapWith d e p).cost x ≤ K*(x.2.length+1)*
        (C+((prodCode ea (listCode eb) x).length+1)^9+
          (tabSpan (prodCode ea (listCode eb)) x.2.length x L)^2+1) := by
  obtain ⟨H,hH⟩ := map_arg_bounds ea eb d
  have hmem (x : A × List B) (i : ℕ) (hi : i < x.2.length) : (x.2.drop i).headD d ∈ x.2 := by
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi,Option.getD_some]
    exact List.getElem_mem hi
  obtain ⟨K,hK⟩ := map_finish ea eb (et:=et) (mapArg ea eb d) d e H (by
    intro x i hi
    have := code_le_of_mem eb (hmem x i hi)
    change (prodCode ea eb (x.1,(x.2.drop i).headD d)).length ≤ _
    simp only [mapEnvCode,prodCode,pairBits_length]
    omega) (fun x i hi => (hH x i hi).1)
  refine ⟨K,?_⟩
  intro f p x L C hL hC
  unfold listMapWith
  rw [cost_congrFun]
  exact hK p x (fun i hi => hL _ (hmem x i hi)) (fun i hi => hC _ (hmem x i hi))

/-- The indexed list-map compiler passes the true binary position and the
corresponding encoded element to its child on each visited position. -/
theorem cost_listMapIdxWith (et : T → List Bool) (d : B) (e : T) :
    ∃ K : ℕ, ∀ {f : A → ℕ → B → T}
      (p : Procedure (prodCode ea (prodCode Nat.bits eb)) et (fun y => f y.1 y.2.1 y.2.2))
      (x : A × List B) {L C : ℕ},
      (∀ i : Fin x.2.length, (et (f x.1 i x.2[i])).length ≤ L) →
      (∀ i : Fin x.2.length, p.cost (x.1,i.val,x.2[i]) ≤ C) →
      (listMapIdxWith d e p).cost x ≤ K*(x.2.length+1)*
        (C+((prodCode ea (listCode eb) x).length+1)^9+
          (tabSpan (prodCode ea (listCode eb)) x.2.length x L)^2+1) := by
  obtain ⟨H,hH⟩ := map_arg_bounds ea eb d
  have hentry (x : A × List B) (i : ℕ) (hi : i < x.2.length) : (x.2.drop i).headD d = x.2[i] := by
    rw [List.headD_eq_head?_getD,List.head?_drop,List.getElem?_eq_getElem hi,Option.getD_some]
  obtain ⟨K,hK⟩ := map_finish ea eb (et:=et) (mapIdxArg ea eb d) d e H (by
    intro x i hi
    have h := code_le_of_mem eb (List.getElem_mem hi)
    have hb : i.bits.length ≤ i := by rw [Nat.size_eq_bits_len]; exact Nat.size_le.mpr Nat.lt_two_pow_self
    have hn := list_length_le_code eb x.2
    change (prodCode ea (prodCode Nat.bits eb) (x.1,i,(x.2.drop i).headD d)).length ≤ _
    rw [hentry x i hi]
    simp only [mapEnvCode,prodCode,pairBits_length]
    omega) (fun x i hi => (hH x i hi).2)
  refine ⟨K,?_⟩
  intro f p x L C hL hC
  unfold listMapIdxWith
  rw [cost_congrFun]
  apply hK p x
  · intro i hi
    change (et (f x.1 i ((x.2.drop i).headD d))).length ≤ L
    rw [hentry x i hi]
    exact hL ⟨i,hi⟩
  · intro i hi
    change p.cost (x.1,i,(x.2.drop i).headD d) ≤ _
    rw [hentry x i hi]
    exact hC ⟨i,hi⟩

end StackProcedure

end BorderVNP
end Computability

namespace ExactQuantumFactoring.BitStackProgram.Procedure

export OAI.Computability.BorderVNP.StackProcedure (
  cost_listMapWith
  cost_listMapIdxWith)

end ExactQuantumFactoring.BitStackProgram.Procedure
end OAI
