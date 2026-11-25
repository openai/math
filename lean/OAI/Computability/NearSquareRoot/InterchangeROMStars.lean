import OAI.Computability.NearSquareRoot.InterchangeROMAddressEffective
import OAI.Computability.NearSquareRoot.InterchangeROMExpose
import OAI.Computability.NearSquareRoot.InterchangeROMRecursionOpen
import OAI.Computability.NearSquareRoot.InterchangeOuterReserves

/-! # Literal full-row reserve program

Both reserve strips use one generated pivot-header forest. At recursive
entry the parent keeps only the remaining headers and one pending return.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROMStars

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Adic IntegerMultiplication.Port
  IntegerMultiplication.Loom CommonRegisters RegisterWitness GeneratorSyntax
  InterchangeAddress InterchangeROMAddress InterchangeROMRecursion InterchangeBatch InterchangeSpace Space

abbrev S (a m : ℕ) := OuterReserves.Slots a m

def ranks (a m : ℕ) : List (ℕ × ℕ) :=
  (List.range a).map (fun t => (t,t)) ++ (List.range a).map (fun t => (a+m+t,a+m+t))

def spec (b a m : ℕ) := numericSpec b (a+m+a) (ranks a m)

noncomputable def core : Cmd := exists_core.choose
noncomputable def command (b a m : ℕ) := InterchangeROMAddress.command core (spec b a m)

theorem registers : ∃ R, ∀ b a m, Within R (command b a m) := by
  obtain ⟨R,_,_,hr,_⟩ := exists_core.choose_spec
  exact ⟨R,fun b a m => hr (spec b a m)⟩

theorem effective {X : Type} [Primcodable X] {b a m : X → ℕ}
    (hb : Computable b) (ha : Computable a) (hm : Computable m) :
    Effective ltr fun x => command (b x) (a x) (m x) := by
  have off := Primrec.nat_add.to_comp.comp ha hm
  have len := Primrec.nat_add.to_comp.comp off ha
  have seq := Primrec.list_range.to_comp.comp ha
  have t : Computable fun v : X × ℕ => a v.1 + m v.1 + v.2 :=
    Primrec.nat_add.to_comp.comp (off.comp .fst) .snd
  exact effective_pivots core hb len (Primrec.list_append.to_comp.comp
    (computable_map seq (Computable.snd.pair Computable.snd)) (computable_map seq (t.pair t)))

theorem metadata_reserves (b a m : ℕ) :
    metadata b (Equiv.refl (S a m)) (OuterReserves.pairs a m) = spec b a m := by
  rw [metadata_eq]
  congr 1
  apply List.ext_getElem
  · simp [ranks,OuterReserves.pairs_length]; omega
  · intro i hi hj
    by_cases lt : i<a
    · simp [OuterReserves.pairs,OuterReserves.ranks,OuterReserves.first,ranks,lt, List.getElem_append_left]
      rfl
    · simp [OuterReserves.pairs,OuterReserves.ranks,OuterReserves.last,ranks,List.getElem_append_right,
        Nat.le_of_not_gt lt]
      rfl

def admin (b a m : ℕ) (h : Header) (K d : ℕ) :=
  headerTime (spec b a m) h K d + 110*(size (plan (spec b a m,h))+1) + 2*a + size h + 4

private theorem chain_counts {b : ℕ} {x y : Tree} {qs : List (Request b)}
    (c : Chain Request.payload (Request.job b).reply x qs y) :
    y.count=x.count ∧ ∀ q∈qs, q.payload.count=x.count := by
  induction c with
  | nil => exact ⟨rfl,by simp⟩
  | @cons q qs z c ih =>
    have same := InterchangeROMExpose.request_reply_count q
    refine ⟨ih.1.trans same,?_⟩
    intro u hu
    rcases List.mem_cons.mp hu with rfl | later
    · rfl
    · exact (ih.2 u later).trans same

/-- Native code for exactly the diagonal reserve pivots, for any spectator
layout. Every emitted payload consists of unchanged original records. -/
theorem run : ∃ K d : ℕ, ∀ {b a m f : ℕ} [NeZero b] (P G B : Tape)
    (l : ℕ) (v : Keys P G B (S a m) (Block b f) → Tree) (good : Tree → Prop) (_ : ∀ k, good (v k)),
    let physical := arrays (Equiv.refl (S a m)) (line b f) P G B
    let h := header f P G B
    let src := stripe physical v
    let dst := stripe physical (v ∘ OuterReserves.swapOuter)
    ∃ qs : List (Request b), qs.length = 2*a ∧
      (∀ q∈qs, (q.width=f ∧ q.rows.count=physical.count ∧ q.recordWidth=l) ∧
        (∀ k, good (q.contents k)) ∧ inherited b P G B q) ∧
      ∀ parent, At parent (command b a m) (Request.job b) [] qs (.fork (send h) src) dst
        (src.count + admin b a m h K d) (headers Request.header qs).count 1 := by
  obtain ⟨_,K,d,_,prep⟩ := exists_core.choose_spec
  refine ⟨K,d,?_⟩
  intro b a m f nz P G B l v good hv
  let ord := Equiv.refl (S a m)
  let physical := arrays ord (line b f) P G B
  let h := header f P G B
  let sp := spec b a m
  let src := stripe physical v
  let dst := stripe physical (v ∘ OuterReserves.swapOuter)
  obtain ⟨all,ct,typed,tag,wire⟩ := InterchangeROMAddress.pivot_schedule ord
    (fun _ : Unit => P) (fun _ => G) (fun _ => B) (fun _ => f) (fun _ => l) (fun _ => good)
    (OuterReserves.pairs a m) (fun _ => v) (fun _ => hv)
  let qs := all ()
  have len : qs.length=2*a := (ct ()).trans (OuterReserves.pairs_length a m)
  have tagEq : send (plan (sp,h)) = headers Request.header qs := by
    simpa only [sp,h,ord,metadata_reserves] using tag ()
  have action : v ∘ (recreation ord P G B f (pivotOps b (OuterReserves.pairs a m))
      (pivotOps_legal _ _ _)).symm = v ∘ OuterReserves.swapOuter :=
    funext fun k => congrArg v (OuterReserves.recreation_outer a m b f P G B k)
  have linked : Chain Request.payload (Request.job b).reply src qs dst := by
    simpa only [layoutRows,action] using wire ()
  have eqs := chain_counts linked
  refine ⟨qs,len,fun q hq => ?_,?_⟩
  · obtain ⟨⟨sizes,r⟩,inheritance⟩ := typed () q hq
    exact ⟨sizes,r,inheritance⟩
  · intro parent env price data depth child deck base hc
    simp only [List.nil_append] at child ⊢
    have ready := InterchangeROMAddress.run core K d prep sp h Request.header Request.payload
      (Request.job b).reply price data depth parent env src.count tagEq linked
      (fun q hq => (eqs.2 q hq).le) eqs.1.le child deck base hc
    let H := (headers Request.header qs).count
    let T := headerTime sp h K d
    have Hsize : size (plan (sp,h)) = H := congrArg Tree.count tagEq
    change BoundedFits _ _ _ _ (T + (((qs.map price).sum+qs.length)+110*(H+1))+2)
      (base+max (size h+src.count+1+T) (dataSpace src.count H (childPeak data qs)))
      (max (T+1) (returnSpace H (childPeak depth qs))) at ready
    let W := src.count+admin b a m h K d
    change BoundedFits _ _ _ _ (W+(qs.map price).sum) (base+max (W+0) (H+childPeak data qs))
      (max (W+0) (1+childPeak depth qs))
    have fee : W = src.count+T+110*(H+1)+2*a+size h+4 := by
      dsimp only [W,admin]
      rw [show size (plan (spec b a m,h)) = H from Hsize]
      dsimp only [T,sp]
      omega
    apply ready.mono
    · omega
    · unfold dataSpace
      omega
    · unfold returnSpace
      omega

end InterchangeROMStars

end NearSquareRoot
end Computability
end OAI
