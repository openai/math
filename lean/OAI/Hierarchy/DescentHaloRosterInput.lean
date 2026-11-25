import OAI.Hierarchy.DescentHaloCompilation
import OAI.Hierarchy.DescentColonyDynamicSplit

namespace OAI
/-! # Mount the same native dynamic roster used by stage geometry -/
namespace Hierarchy.DescentHaloCompilation
open DescentHaloWalkRAM DescentColonies Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open Classical
open scoped Fin.CommRing
noncomputable section
variable {V : Type} [DecidableEq V] {ℓ D L w : ℕ}
local notation "H" => 2^ℓ

/-- The dependency on represented geometry resides in the single rectangular
adjacency table. Root/path digits and base addresses are public arithmetic. -/
theorem roster_reads (B : DescentHaloWalkRAM.Banks) (rs : DynamicSplit.Roster ℓ D) (m : Memory w)
    (stored : DynamicSplit.Stored B.adjacency.base rs m)
    (root : ∀(v:Fin H)(p:Fin (breadth D)),m (B.root.base+(row v p).val)=(v.val:Word w))
    (choice : ∀(v:Fin H)(p:Fin (breadth D))(j:Fin 4),m ((B.choice j).base+(row v p).val)=((path p j).val:Word w)) : Reads B rs m :=
  ⟨stored,root,choice⟩

omit [DecidableEq V] in
theorem roster_member (name : V≃Fin L) (padded : L≤H) (near : V→Finset V) (symm : ∀ v u,u∈near v ↔ v∈near u)
    (rs : DynamicSplit.Roster ℓ D)
    (members : ∀i j,j∈DynamicSplit.incoming rs i ↔ ∃ v u : V,i=(name v).castLE padded ∧ j=(name u).castLE padded ∧ v∈near u)
    (v u : V) (edge : u∈near v) : ∃s,rs ((name v).castLE padded) s=some ((name u).castLE padded) :=by
  have here:=(members ((name v).castLE padded) ((name u).castLE padded)).2 ⟨v,u,rfl,rfl,(symm v u).1 edge⟩
  obtain ⟨a,ins,hit⟩:=List.mem_filterMap.mp here
  obtain ⟨s,val⟩:=List.mem_ofFn.mp ins
  exact ⟨s,val.trans hit⟩

/-- Costs depend only on the shared host count and degree. There is no factor
for the number of represented groups, old sites, or cable occurrences. -/
theorem public_cost (B : DescentHaloWalkRAM.Banks) (T : Ranks.Columns) (h D : ℕ) :
    (4+h*breadth D*(2*(body B h D 4).work+4))+(4+h*breadth D*(2*(Ranks.body T (breadth D)).work+4)) ≤
      8+128*h*(D+10)^8 :=by
  let N:=(D+10)^4
  have small : breadth D≤N:=Nat.pow_le_pow_left (by omega) _
  have one : 1≤N := pow_pos (by omega : 0 < D+10) 4
  have a:=body_work B h D 4;have b:=Ranks.body_work T (breadth D)
  have walks : 2*(body B h D 4).work+4≤40*N:=by change _≤40*(D+10)^4;omega
  have ranks : 2*(Ranks.body T (breadth D)).work+4≤70*N:=by omega
  have left:=Nat.mul_le_mul (Nat.mul_le_mul_left h small) walks
  have right:=Nat.mul_le_mul (Nat.mul_le_mul_left h small) ranks
  have square : (D+10)^8=N*N := by dsimp only [N]; rw [←pow_add]
  rw [square];nlinarith

end
end Hierarchy.DescentHaloCompilation

end OAI
