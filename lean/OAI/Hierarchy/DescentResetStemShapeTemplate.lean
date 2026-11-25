import OAI.Hierarchy.DescentResetStemDecoder
import OAI.Hierarchy.DescentInstalledPublicHeader

namespace OAI
/-! # Fixed local endpoint shapes for both signed stem tickets -/
namespace Hierarchy.DescentResetStemDecoder
open DescentContacts DescentCommonHost DescentDenseHostOrder DescentSixParty
open scoped Classical
noncomputable section

variable {n h : ℕ} (board : NonlinearExpanders.Graph n h)

def localOrdinal (r height : ℕ) (sh : Node Unit (Unit×Endpoint (2^n)) (DescentCommonPalette.rotor board).Site) (nonempty : 0<(roster board r height).card) : Fin (roster board r height).card :=
  if hh : sh ∈ roster board r height then localRank board r height ⟨sh,hh⟩ else ⟨0,nonempty⟩

/-- These operands depend on the fixed board, depth and signed short ticket. The
previous vertex is only used later to form an absolute native name. -/
def localTemplate (r height : ℕ) (s : Bool) (j : ℕ) : Option (Fin (roster board r height).card×Fin (roster board r height).card) :=
  if hh : 0<(roster board r height).card then
    (nodes board s () (DescentFallbackShapeTable.decode r (2^n) (j/2),decide (j%2=1))).map
      (fun z=>(localOrdinal board r height z.1 hh,localOrdinal board r height z.2 hh))
  else none

private theorem nodes_shape {V : Type} (v : V) (s : Bool) (ticket : Endpoint (2^n)×Bool) :
    (nodes board s v ticket).map (fun z=>(shape board z.1,shape board z.2))=nodes board s () ticket := by
  rcases ticket with ⟨⟨which,port⟩,mode⟩
  cases mode <;> cases port <;> rfl

private theorem nodes_position {V : Type} (v : V) (s : Bool) (ticket : Endpoint (2^n)×Bool)
    {ends} (got : nodes board s v ticket=some ends) :
    position board ends.1=v ∧ position board ends.2=v := by
  rcases ticket with ⟨⟨which,port⟩,mode⟩
  cases mode <;> cases port <;> simp [nodes] at got <;> subst ends <;> exact ⟨rfl,rfl⟩

variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits}
  {q ε : ℝ} {g C depth : ℕ} (Z : ResetInput W q ε g C depth) (T : ResetInput.Terminals Z)
local notation "r" => Z.k-T.commonDepth
local notation "pool" => roster Z.graph r depth

theorem localTemplate_read {H : ℕ} (vertex : Z.V↪Fin H) (v : Z.V) (s : Bool) (j : ℕ)
    (nonempty : 0< (pool).card) :
    (localTemplate Z.graph r depth s j).map (fun z=>
      (z.1.val+(pool).card*(vertex v).val,z.2.val+(pool).card*(vertex v).val))=
    (nodes Z.graph s v (DescentFallbackShapeTable.decode r (2^Z.n) (j/2),decide (j%2=1))).map
      (fun z=>(Z.codeHost T vertex z.1,Z.codeHost T vertex z.2)) := by
  let ticket:= (DescentFallbackShapeTable.decode r (2^Z.n) (j/2),decide (j%2=1))
  have shapes:=nodes_shape Z.graph v s ticket
  unfold localTemplate
  rw [dite_eq_left nonempty,←shapes]
  cases got : nodes Z.graph s v ticket with
  | none=>rfl
  | some ends=>
    obtain ⟨left,right⟩:=nodes_position Z.graph v s ticket got
    change some ((localOrdinal Z.graph r depth (shape Z.graph ends.1) nonempty).val+(pool).card*(vertex v).val,
      (localOrdinal Z.graph r depth (shape Z.graph ends.2) nonempty).val+(pool).card*(vertex v).val)=some (Z.codeHost T vertex ends.1,Z.codeHost T vertex ends.2)
    apply congrArg some
    by_cases l : shape Z.graph ends.1∈pool <;> by_cases rgt : shape Z.graph ends.2∈pool <;> simp [ResetInput.codeHost,left,right,localOrdinal,l,rgt]

end
end Hierarchy.DescentResetStemDecoder

end OAI
