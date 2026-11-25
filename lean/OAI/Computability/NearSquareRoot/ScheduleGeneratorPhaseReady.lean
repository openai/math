import OAI.Computability.NearSquareRoot.ScheduleGeneratorPhase

/-! # The simulated source transition in the generated alphabet controller -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Generator.Phase
open CommonAlphabet IntegerMultiplication
variable {A Q : ℕ → Type} {I : Type}
variable (a : ∀ x, Numbering (A x)) (q : ∀ x, Numbering (Q x)) (i : Numbering I)
  (ha : Computable fun x => (a x).size)
  (rows : ℕ → ℕ × ℕ → Option (ℕ × ℕ))

/-- Form the source read-tuple rank, consult the source machine and unpack the
simultaneous action tuple for the first writing phase. -/
def execReady (x : ℕ) (r : List ℕ) (v : ℕ × List ℕ) : Option (State × Actions) :=
  (rows x (v.1,Numbering.encodeBase (a x).size v.2)).map fun z =>
    (work z.1 ((actions a i ha).decode x z.2) 0 0,r.map fun s => (s,1))

theorem computable_execReady {X : Type} [Primcodable X]
    (hrws : Computable₂ rows) {j : X → ℕ} {r : X → List ℕ} {v : X → ℕ × List ℕ}
    (hj : Computable j) (hr : Computable r) (hv : Computable v) :
    Computable fun x => execReady a i ha rows (j x) (r x) (v x) := by
  let call := fun x => rows (j x) ((v x).1,Numbering.encodeBase (a (j x)).size (v x).2)
  have get : Computable call := hrws.comp hj ((Computable.fst.comp hv).pair
    (Numbering.primrec_encodeBase.to_comp.comp (ha.comp hj) (Computable.snd.comp hv)))
  apply Computable.option_map get
  have next : Computable (fun z : X × (ℕ × ℕ) => z.2.1) := Computable.fst.comp (Computable.snd (α := X) (β := ℕ × ℕ))
  have op : Computable (fun z : X × (ℕ × ℕ) => (actions a i ha).decode (j z.1) z.2.2) := (actions a i ha).decode_eff.comp (hj.comp Computable.fst) (Computable.snd.comp Computable.snd)
  have state : Computable (fun z : X × (ℕ × ℕ) => work z.2.1 ((actions a i ha).decode (j z.1) z.2.2) 0 0) := Computable.sumInr.comp (Computable.sumInl.comp
    (next.pair (op.pair (Computable.const ((0,0) : ℕ × ℕ)))))
  have holdR : Computable fun x : X => (r x).map (fun s => ((s,1) : ℕ × ℕ)) :=
    computable_map (fallback := fun _ => 0) hr (Computable.snd.pair (Computable.const 1)).to₂
      (Computable.const 0)
  exact (state.pair (holdR.comp Computable.fst)).to₂

theorem observe_ready (blank : ∀ x, A x) (machine : ∀ x, TM.Rule (A x) (Q x) I)
    (h : ∀ x z r, rows x (((q x).equiv z).val, (i.arrow (a x) |>.equiv r).val) =
      (machine x z r).map (fun v => (((q x).equiv v.1).val,
        (i.arrow ((a x).prod Numbering.move) |>.equiv v.2).val)))
    (x : ℕ) (z : Q x) (c : I → A x) (r : I → Option Bool) :
    observe a q i (fun j => (a j).size) x
      (CommonAlphabet.rule (oneHot (a x).equiv (blank x)) (machine x) (.ready z c) r) =
    execReady a i ha rows x (ranks i r)
      (((q x).equiv z).val,i.all.map fun l => ((a x).equiv (c l)).val) := by
  unfold execReady
  rw [Numbering.encodeBase_arrow,h]
  change ((machine x z c).map _).map _ = _
  cases he : machine x z c with
  | none => rfl
  | some u =>
    obtain ⟨y,op⟩ := u
    simp only [Option.map_some,Presentation.decode_rank]
    apply congrArg some
    apply Prod.ext
    · rfl
    · simp only [moves,ranks,List.map_map,CommonAlphabet.hold]
      rfl

end Generator.Phase

end NearSquareRoot
end Computability
end OAI
