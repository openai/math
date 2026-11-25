import OAI.Computability.NearSquareRoot.InterchangeROMAddressOpcode

/-! # The actual singleton callback for a numerical pivot -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace OpcodeProgram

open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Strip
  IntegerMultiplication.Strip.Dims IntegerMultiplication.Port IntegerMultiplication.Loom
  IntegerMultiplication.Adic InterchangeROMAddress InterchangeAddress InterchangeBatch
  InterchangeSpace Space

def pivotPrice (K e : ℕ) (spec : Spec) (h : Header) (source answer : Tree) :=
  K*(size (spec,h)+1)^e + source.count + answer.count

private def pivotLocal (K d : ℕ) (p : Spec × Header) :=
  headerTime p.1 p.2 K d + 120*(size (plan p)+1) + size p.2 + 10

private theorem local_dom (K d : ℕ) : Dom size (pivotLocal K d) := by
  let size' := size (X:=Spec × Header)
  have a := Dom.base size'
  have src : Dom size' (fun t => size t.1) := a.mono (fun _ => by simp only [size',size_prod]; omega)
  have hdr : Dom size' (fun t => size t.2) := a.mono (fun _ => by simp only [size',size_prod]; omega)
  have one := Dom.const size' 1
  have comp := (((Dom.const size' 5).mul src).add ((Dom.const size' K).mul ((a.add one).pow d))).add (Dom.const size' 20)
  exact ((comp.add ((Dom.const size' 120).mul (plan_poly.length.add one))).add hdr).add (Dom.const size' 10)

private theorem start {X : Type} {x y : Tree} {payload reply : X → Tree} {qs : List X}
    (len : qs.length = 1) (chain : Chain payload reply x qs y) :
    ∀ q∈qs, payload q = x := by
  obtain ⟨a,rfl⟩ := List.length_eq_one_iff.mp len
  intro q hq
  obtain rfl := List.mem_singleton.mp hq
  cases chain
  rfl

theorem pivot_command : ∃ K e : ℕ, ∀ {n b f : ℕ} [NeZero b] (P G S : Tape)
    (x y : Fin n) (l : ℕ) (v : Keys P G S (Fin n) (Block b f) → Tree)
    (good : Tree → Prop) (_ : ∀ k, good (v k)),
    let ord := Equiv.refl (Fin n)
    let physical := arrays ord (line b f) P G S
    let h := header f P G S
    let sp := metadata b ord [(x,y)]
    let src := stripe physical v
    let dst := stripe physical (v ∘ (reflect ord (.pivot x y) trivial P G S f).symm)
    let cost := pivotPrice K e sp h src dst
    ∃ qs : List (Request b), qs.length = 1 ∧
      (∀ a∈qs, (a.width = f ∧ a.rows.count = physical.count ∧ a.recordWidth = l) ∧
        (∀ z, good (a.contents z)) ∧ inherited b P G S a) ∧
      ∀ parent env (price data depth : Request b → ℕ),
        (∀ a∈qs, ∀ d base, DeckCap base d → BoundedFits (parent::env) parent
          (pile 0 ((Request.job b).issue a) d) (pile 0 ((Request.job b).reply a) d)
          (price a) (base+data a) (depth a)) →
        ∀ deck base, DeckCap base deck →
          BoundedFits (parent::env) (dispatch b n (Opcode.encode (b:=b) (.pivot x y)))
            (pile 0 (.fork (send h) src) deck) (pile 0 dst deck)
            (cost+(qs.map price).sum) (base+cost+childPeak data qs) (cost+childPeak depth qs) := by
  obtain ⟨_,A,d,_,prep⟩ := pivot_core
  obtain ⟨e,K,big⟩ := local_dom A d
  refine ⟨K,e,?_⟩
  intro n b f nz P G S x y l v good hv
  let ord := Equiv.refl (Fin n)
  let physical := arrays ord (line b f) P G S
  let h := header f P G S
  let sp := metadata b ord [(x,y)]
  let src := stripe physical v
  let dst := stripe physical (v ∘ (reflect ord (.pivot x y) trivial P G S f).symm)
  let V := src.count + dst.count
  let amount := pivotPrice K e sp h src dst
  obtain ⟨all,ct,typed,tags,wire⟩ := InterchangeROMAddress.pivot_schedule
    ord (fun _ : Unit => P) (fun _ => G) (fun _ => S) (fun _ => f) (fun _ => l) (fun _ => good)
    [(x,y)] (fun _ => v) (fun _ => hv)
  let qs := all ()
  have card : qs.length = 1 := ct ()
  have lane : Chain Request.payload (Request.job b).reply src qs dst := by
    convert wire () using 1
    simp [dst,physical,layoutRows,pivotOps,recreation]
  refine ⟨qs,card,fun q hq => ?_,?_⟩
  · obtain ⟨⟨sizeEq,payloadGood⟩,shapeGood⟩ := typed () q hq
    exact ⟨sizeEq,payloadGood,shapeGood⟩
  · intro parent env price data depth calls deck base hold
    have hx (q) (hq : q ∈ qs) : (Request.payload q).count ≤ V := by
      rw [start card lane q hq]
      exact Nat.le_add_right ..
    have hy : dst.count ≤ V := Nat.le_add_left ..
    have ready := InterchangeROMAddress.run pivotCore A d prep sp h Request.header Request.payload
      (Request.job b).reply price data depth parent env V (tags ()) lane hx hy calls deck base hold
    let T := headerTime sp h A d
    let H := (headers Request.header qs).count
    have Hsize : size (plan (sp,h)) = H := congrArg Tree.count (tags ())
    have headCharge := big (sp,h)
    change T + 120*(size (plan (sp,h))+1)+size h+10 ≤ K*(size (sp,h)+1)^e at headCharge
    rw [Hsize] at headCharge
    change BoundedFits (parent::env) (InterchangeROMAddress.command pivotCore sp)
      (pile 0 (.fork (send h) src) deck) (pile 0 dst deck)
      (amount+(qs.map price).sum) (base+amount+childPeak data qs) (amount+childPeak depth qs)
    apply ready.mono
    · dsimp only [amount,pivotPrice]
      change T + ((qs.map price).sum+qs.length+110*(H+1))+2 ≤ _
      omega
    · dsimp only [amount,pivotPrice]
      change base + max ((size h + src.count+1) + T)
        (max (V+100*(H+1)) (H+childPeak data qs)) ≤ _
      dsimp only [V]
      omega
    · dsimp only [amount,pivotPrice]
      change max (T+1) (max (100*(H+1)) (childPeak depth qs+1)) ≤ _
      omega

end OpcodeProgram

end NearSquareRoot
end Computability
end OAI
