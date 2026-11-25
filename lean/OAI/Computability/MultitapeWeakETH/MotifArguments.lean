import OAI.Computability.MultitapeWeakETH.MotifCopies

/-! # Reconstructing both finite coordinates of a motif lookup -/

namespace OAI.Computability.MultitapeWeakETH.MotifFields

open IntegerMultiplication Code VPVNP StackInterpreter MotifSelector
open scoped Classical
noncomputable section

variable {D J : Type} (src dst : D → J) (j : J)
abbrev Ends := {e // j=src e} ⊕ {e // j=dst e}
def wire : Ends src dst j → D := Sum.elim Subtype.val Subtype.val

def assemble {A : D → Type} (z : ∀ p : Ends src dst j, A (wire src dst j p)) :
    ((e : D) → j=src e → A e) × ((e : D) → j=dst e → A e) :=
  (fun e h => z (.inl ⟨e,h⟩), fun e h => z (.inr ⟨e,h⟩))

variable [Fintype D] [DecidableEq J]
theorem assemble_poly {A : D → Type} [∀ e, Fintype (A e)] [∀ e, Nonempty (A e)] {X : Type} [Codec X]
    (z : ∀ p : Ends src dst j, X → A (wire src dst j p)) (p : ∀ e, Poly (fun x => Label.mk (z e x))) :
    Poly (fun x => Label.mk (assemble src dst j (fun e => z e x))) := by
  apply index_poly
  intro ref
  let r (e : Ends src dst j) : A (wire src dst j e) := match e with
    | .inl e => ref.1 e.val e.prop
    | .inr e => ref.2 e.val e.prop
  have test (e : Ends src dst j) := (p e).compose (Easy.finite (fun t : Label (A (wire src dst j e)) => decide (t.val = r e))).poly
  convert all_poly _ test using 1
  funext x
  apply Bool.eq_iff_iff.mpr
  simp only [decide_eq_true_eq]
  constructor
  · intro eq e
    cases e with
    | inl e => exact congrArg (fun h => h.1 e.val e.prop) eq
    | inr e => exact congrArg (fun h => h.2 e.val e.prop) eq
  · intro eq
    exact Prod.ext (funext fun e => funext fun h => eq (.inl ⟨e,h⟩))
      (funext fun e => funext fun h => eq (.inr ⟨e,h⟩))

def demandInput {u : ℕ} {b : D → ℕ} (d : MotifEntry.DemandBits src dst b j) (i : Fin u) :=
  (bank (fun p : Ends src dst j => match p with
    | .inl e => List.ofFn (d.1 e.val e.prop)
    | .inr e => List.ofFn (d.2 e.val e.prop)),tally i.val)

def demand (a : D → ℕ) (q : List Bits.Word × Tally) : Label (MotifDemandPadding.HalfBits src dst a j) :=
  ⟨assemble src dst j (fun p => (copy (a (wire src dst j p)) ((fetch [] p q.1,[]),q.2)).val)⟩

theorem demand_poly (a : D → ℕ) : Poly (demand src dst j a) := by
  apply assemble_poly
  intro p
  have get := (Easy.fst (X:=List Bits.Word) (Y:=Tally)).poly.compose (fetch_poly ([] : Bits.Word) p)
  exact ((get.pair (Code.Poly.const ([] : Tally))).pair Easy.snd.poly).compose (copy_poly _)

theorem demand_eq {u : ℕ} {b : D → ℕ} (a : D → ℕ) (d : MotifEntry.DemandBits src dst b j) (i : Fin u) :
    (demand src dst j a (demandInput src dst j d i)).val = MotifEntry.demandFields src dst a i j d := by
  apply Prod.ext <;> funext e he <;>
    simp only [demand,assemble,demandInput,fetch_bank,wire,Sum.elim_inl,Sum.elim_inr,copy,tally_length,List.length_nil,
      Nat.zero_add,read_eq,MotifEntry.demandFields]

variable {E S : Type} [Fintype E] [Fintype S] (G : Supply J E) (w : S → E → ℕ)
abbrev Argument := (SupplyInput × List (Label S)) × Tally

def supply (s : S) (q : Argument (S:=S)) : Label (Half G (fun e => Word (w s e)) j) :=
  ⟨assemble G.src G.dst j (fun p =>
    let field := fetch ([],[]) p q.1.1.1
    let payload := (cutLists field.swap).1
    (read (w s (edge G j p)) (payload,start w (edge G j p) (q.1.2,q.2))).val)⟩

theorem supply_poly (s : S) : Poly (supply j G w s) := by
  apply assemble_poly
  intro p
  have bank : Poly (fun q : Argument (S:=S) => q.1.1.1) := by fun_prop
  have field := bank.compose (fetch_poly (([] : Bits.Word),([] : Tally)) p)
  have payload := field.compose ((easy_cut Easy.exchange).fstCompose.poly)
  have pos := ((show Poly (fun q : Argument (S:=S) => q.1.2) by fun_prop).pair Easy.snd.poly).compose (start_poly w (edge G j p))
  exact (payload.pair pos).compose (read_poly _)

private theorem truncate {u bits v : ℕ} (x : Fin (v+u*bits) → Bool) :
    (List.ofFn x).take v = List.ofFn (MotifEntry.payloadBits x) := by
  rw [← Fin.ofFn_take_eq_take_ofFn (Nat.le_add_right v (u*bits))]
  rfl

omit [Fintype S] in
theorem supply_eq {u bits : ℕ} (seq : Fin u → S) (v : E → ℕ) (x : Half G (fun e => Fin (v e+u*bits) → Bool) j)
    (i : Fin u) (s : S) :
    (supply j G w s ((supplyInput G j v x,List.ofFn fun l => Label.mk (seq l)),tally i.val)).val =
      mapHalf G (fun e y => MotifEntry.fieldIndex (MotifEntry.payloadBits y) (MotifEntry.offset (fun l => w (seq l) e) i) (w s e)) x := by
  apply Prod.ext <;> funext e he <;>
    simp only [supply,assemble,supplyInput,fetch_bank,endpoint,edge,Sum.elim_inl,Sum.elim_inr,cutLists,
      Prod.swap,tally_length,truncate,start_eq,read_eq,mapHalf]

end
end OAI.Computability.MultitapeWeakETH.MotifFields
