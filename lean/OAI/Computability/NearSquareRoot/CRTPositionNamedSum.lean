import OAI.Computability.NearSquareRoot.CRTPositionOpcodeCall
import OAI.Computability.NearSquareRoot.CRTControlledEffectiveRectangle

/-! # The named interpreter of a nested opcode sum -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled.PositionProgram
open IntegerMultiplication IntegerMultiplication.Code IntegerMultiplication.Adic IntegerMultiplication.Strip
open IntegerMultiplication.Loom NamedPacked

abbrev OpcodeTemplate {A : Type} (wrap : A → Op) :=
  ∃ t : Effective.Template, ∀ c ρ, 0 ≤ ρ → Effective.rectContract c ρ → OpAt (t.eval c) ρ wrap

private def splitArg {A B : Type} [Codec A] [Codec B] : A ⊕ B → Bool × Tree
  | .inl a => (false,send a)
  | .inr b => (true,send b)

private theorem callRegime_eq {A B X : Type} {p : A → Op} {q : B → Op}
    (l : X → Call p) (r : X → Call q) (k : ∀ x, (l x).k=(r x).k)
    (h : ∀ x, (l x).key = (r x).key) :
    (Call.regime p).pull l = (Call.regime q).pull r := by
  unfold Regime.pull
  congr 1
  · exact funext k
  · exact funext h

theorem opcodeTemplate_sum {A B : Type} [Codec A] [Codec B] (wrap : A ⊕ B → Op)
    (payload : (Call.regime wrap).Has Call.operand)
    (left : OpcodeTemplate (wrap ∘ Sum.inl)) (right : OpcodeTemplate (wrap ∘ Sum.inr)) :
    OpcodeTemplate wrap := by
  let X := Call wrap
  let tag (x : X) := (splitArg x.operand).1
  let L := {x : X // tag x = false}
  let H := {x : X // tag x = true}
  let reg := Call.regime wrap
  have pairCode (t : A ⊕ B) : send (splitArg t) = send t := by cases t <;> rfl
  have both : reg.Has (fun x => splitArg x.operand) := by
    unfold Regime.Has
    simpa only [Function.comp_def,pairCode] using (show reg.Small (send ∘ Call.operand) from payload)
  have know := both.ez Easy.fst
  have st := terminal (p:=2) (r:=reg) (by decide) Call.k Call.widthHas
  have live := cloth_size (fun x : X => line 2 x.k) (fun x => Series.natural x.width) st Call.data
    (l:=Call.width) (fun _ => by simp)
  have get : Rip reg (fun x => (line 2 x.k).count) Call.width Call.input (send ∘ tag) :=
    Drive.small st.1 live know
  obtain ⟨pre,branch⟩ := namedBranch (v:=Call.output) tag (get.twice get.again)
  obtain ⟨l,left⟩ := left
  obtain ⟨r,right⟩ := right
  refine ⟨.branch pre l r,?_⟩
  intro c ρ hr good
  apply branch (Spindle.modes Call.k (τ:=ρ))
  · have has (x : L) : ∃ a, x.val.operand = Sum.inl a := by
      have h := x.property
      cases e : x.val.operand with
      | inl a => exact ⟨a,rfl⟩
      | inr b => simp [tag,e,splitArg] at h
    choose val eq using has
    let pick (x : L) : Call (wrap ∘ Sum.inl) := ⟨x.val.k,val x,by
      change WellFormed _ _ (wrap (Sum.inl (val x)))
      rw [←eq]; exact x.val.legal,x.val.width,x.val.data⟩
    have key (x:L) : (pick x).key = x.val.key := by
      simp only [pick,Call.key,Function.comp_apply,eq]
    have rr := callRegime_eq pick (Subtype.val : L → X) (fun _ => rfl) key
    have run := (left c ρ hr good).on pick
    rw [rr] at run
    convert run using 1 <;> try rfl
    · funext x
      change Tree.fork (Call.key x.val) _ = Tree.fork ((pick x).key) _
      rw [key]
      rfl
    · funext x
      change x.val.packet (x.val.data ∘ nativeOp _ _ (wrap x.val.operand)) =
        x.val.packet (x.val.data ∘ nativeOp _ _ (wrap (.inl (val x))))
      rw [eq]
  · have has (x : H) : ∃ b, x.val.operand = Sum.inr b := by
      have h := x.property
      cases e : x.val.operand with
      | inl a => simp [tag,e,splitArg] at h
      | inr b => exact ⟨b,rfl⟩
    choose val eq using has
    let pick (x : H) : Call (wrap ∘ Sum.inr) := ⟨x.val.k,val x,by
      change WellFormed _ _ (wrap (Sum.inr (val x)))
      rw [←eq]; exact x.val.legal,x.val.width,x.val.data⟩
    have key (x:H) : (pick x).key = x.val.key := by
      simp only [pick,Call.key,Function.comp_apply,eq]
    have rr := callRegime_eq pick (Subtype.val : H → X) (fun _ => rfl) key
    have run := (right c ρ hr good).on pick
    rw [rr] at run
    convert run using 1 <;> try rfl
    · funext x
      change Tree.fork (Call.key x.val) _ = Tree.fork ((pick x).key) _
      rw [key]
      rfl
    · funext x
      change x.val.packet (x.val.data ∘ nativeOp _ _ (wrap x.val.operand)) =
        x.val.packet (x.val.data ∘ nativeOp _ _ (wrap (.inr (val x))))
      rw [eq]

end Controlled.PositionProgram

end NearSquareRoot
end Computability
end OAI
