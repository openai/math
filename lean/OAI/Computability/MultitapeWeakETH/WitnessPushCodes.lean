import OAI.Computability.MultitapeWeakETH.WitnessForestCodes
import OAI.Computability.VPVNP.PairSimulationVertexJobs

/-! # Exact witness words for pushing site factors through a compression term -/

namespace OAI.Computability.MultitapeWeakETH.WitnessWalk

open IntegerMultiplication Code VPVNP CompressorRecords NetworkKernel PairSimulation LocalHistory
open private push_encode from OAI.Computability.VPVNP.PairSimulationVertexJobs
open scoped Classical
noncomputable section

variable {D : Type} {visit : Visit D} {ctx : D}

private theorem node_reads {H X : Type} {K C : H → Type} (e : X ≃ Σ h, C h × K h)
    (j : Job) (kids : H → List Job) (head : ∀ h, K h → Bits.Word) (emit : ∀ h, K h → List Tally)
    (codes : ∀ h, C h → Bits.Word) (tags : ∀ h, C h → List Tally) (encode : X → Bits.Word)
    (split : ∀ x, encode x = head (e x).1 (e x).2.2 ++ codes (e x).1 (e x).2.1)
    (step : ∀ bits js mid ls, visit ((ctx,j),bits) = some ((js,mid),ls) ↔ ∃ h k,
      js = kids h ∧ bits = head h k ++ mid ∧ ls = emit h k)
    (sub : ∀ h, Reads visit ctx (kids h) (codes h) (tags h)) :
    Reads visit ctx [j] encode (fun x => emit (e x).1 (e x).2.2 ++ tags (e x).1 (e x).2.1) := by
  intro bits tail labels
  rw [accepts_one]
  constructor
  · rintro ⟨js,mid,ls,below,hit,accepted,rfl⟩
    obtain ⟨h,k,rfl,rfl,rfl⟩ := (step _ _ _ _).mp hit
    obtain ⟨c,rfl,rfl⟩ := (sub h _ _ _).mp accepted
    have eqn := e.apply_symm_apply (⟨h,c,k⟩ : Σ h, C h × K h)
    refine ⟨e.symm ⟨h,c,k⟩,?_,?_⟩
    · rw [split,eqn,List.append_assoc]
    · dsimp only; rw [eqn]
  · rintro ⟨x,rfl,rfl⟩
    rw [split,List.append_assoc]
    exact ⟨_,_,_,_,(step _ _ _ _).mpr ⟨_,_,rfl,rfl,rfl⟩,(sub _ _ _ _).mpr ⟨_,rfl,rfl⟩,rfl⟩

variable {R L : Type} [CommRing R] [Fintype L] {f : L → R} {N : Network} {t : Term R N}
  (r : TermParsers f t) (P : SiteParsers f N)
  (before : ∀ v, N.Half v → Job) (parent : ∀ v, t.output.Half v → Job)

def children (v : t.output.Site) (a : Placed t.place N.Half v) :=
  List.ofFn fun j => let u := (r.order.children v).entries j; before u.val (a u.val u.prop)

/-- The old half-wires, chosen kernel, and all child monomials are precisely the
components of the verified VPVNP push equivalence. -/
theorem reads_push (childNames : ∀ u h, (P.witnesses u h).Choice → List Tally)
    (each : ∀ u h, Reads visit ctx [before u h] (P.read u h).encode (childNames u h))
    (v : t.output.Site) (z : t.output.Half v) (emit : ∀ a, (r.witness v a z).Choice → List Tally)
    (step : ∀ bits js mid ls, visit ((ctx,parent v z),bits) = some ((js,mid),ls) ↔ ∃ a k,
      js = children r before v a ∧ bits = r.nodeBits v a z k ++ mid ∧ ls = emit a k) :
    let e := t.pushChoice P.factors P.witnesses r.witness v z
    let o := r.order.children v
    Reads visit ctx [parent v z] ((r.push P).read v z).encode
      (fun x => emit (e x).1 (e x).2.2 ++ (List.ofFn fun j =>
        let u := o.entries j; childNames u.val ((e x).1 u.val u.prop) ((e x).2.1 u)).flatten) := by
  intro e o
  apply node_reads e (parent v z) (children r before v) (fun a k => r.nodeBits v a z k) emit
    (fun a x => (List.ofFn fun j => let u := o.entries j; (P.read u.val (a u.val u.prop)).encode (x u)).flatten)
    (fun a x => (List.ofFn fun j => let u := o.entries j; childNames u.val (a u.val u.prop) (x u)).flatten)
    _ (push_encode r P v z) step
  intro a bits tail labels
  let fam (u : t.Preimage v) := (P.witnesses u.val (a u.val u.prop)).Choice
  have forest := reads_forest o.length (fun j => fam (o.entries j))
    (fun j => let u := o.entries j; before u.val (a u.val u.prop))
    (fun j => let u := o.entries j; (P.read u.val (a u.val u.prop)).encode)
    (fun j => let u := o.entries j; childNames u.val (a u.val u.prop))
    (fun j => each _ _) bits tail labels
  refine forest.trans ?_
  constructor
  · rintro ⟨x,hc,he⟩
    let y := Equiv.piCongrLeft fam o.entries x
    have same j : y (o.entries j) = x j := Equiv.piCongrLeft_apply_apply ..
    exact ⟨y,by simpa only [same] using hc,by simpa only [same] using he⟩
  · rintro ⟨x,hc,he⟩
    exact ⟨fun j => x (o.entries j),hc,he⟩

end
end OAI.Computability.MultitapeWeakETH.WitnessWalk
