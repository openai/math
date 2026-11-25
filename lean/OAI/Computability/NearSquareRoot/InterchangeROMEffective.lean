import OAI.Computability.NearSquareRoot.InterchangeROMEffectiveSeries

/-! # Effective finite movement lists -/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace InterchangeROM
open IntegerMultiplication IntegerMultiplication.Code LoomRegisters GeneratorSyntax

variable {X M : Type} [Primcodable X] [Primcodable M]

/-- One numeric generation algorithm handles all finite movement lists even
when both the selected ranks and the move implementations vary. -/
theorem effective_route {entries : X → List (ℕ × M)} {op : X → M → Cmd}
    (he : Computable entries) (ho : Effective ltr (fun v : X × M => op v.1 v.2)) :
    Effective ltr (fun x => routeCommand (op x) (entries x)) := by
  apply effective_series (p:=fun x a => routePart (op x) a)
    (l:=fun x => none :: (entries x).map some)
  · let A := X × Option (ℕ × M)
    have hm : Computable (fun v : A × (ℕ × M) => (v.1.1,v.2.2)) :=
      (Computable.fst.comp Computable.fst).pair (Computable.snd.comp Computable.snd)
    change Computable (fun v : X × M => file ltr (op v.1 v.2)) at ho
    have hd : Effective ltr (fun v : A × (ℕ × M) => op v.1.1 v.2.2) :=
      Computable.comp (f:=fun v : X × M => file ltr (op v.1 v.2))
        (g:=fun v : A × (ℕ × M) => (v.1.1,v.2.2)) ho hm
    have hc : Effective ltr (fun v : A × (ℕ × M) => underHeader (cellCommand v.2.1)) :=
      effective_underHeader (effective_cell (Computable.fst.comp Computable.snd))
    have options := Computable.option_casesOn (Computable.snd (α:=X) (β:=Option (ℕ × M)))
      (Computable.const (file ltr (cellCommand 0))) (hc.join hd).to₂
    exact options.of_eq (by rintro ⟨x,_ | ⟨a,m⟩⟩ <;> rfl)
  · exact Computable.list_cons.comp (Computable.const none)
      ((Primrec.list_map Primrec.id (Primrec.option_some.comp Primrec.snd).to₂).to_comp.comp he)

end InterchangeROM

end NearSquareRoot
end Computability
end OAI
