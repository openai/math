import OAI.Hierarchy.DescentHaloRebaseRAM
import OAI.Hierarchy.DescentHaloRosterInput

namespace OAI
/-! # Mount a genuine common board for reciprocal donor rank lookups -/
namespace Hierarchy.DescentHaloCompilation
open DescentHaloWalkRAM DescentColonies DescentHostDirectory Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure ProtocolRAM
open scoped Classical Fin.CommRing
noncomputable section
variable {w H D : ℕ} (R : Fin H→Fin D→Option (Fin H))
local notation "P" => breadth D

theorem reciprocal_roster {V : Type} [DecidableEq V] {L ℓ : ℕ} (name : V≃Fin L) (padded : L≤2^ℓ)
    (near : V→Finset V) (symm : ∀v u,u∈near v↔v∈near u) (rs : DynamicSplit.Roster ℓ D)
    (members : ∀i j,j∈DynamicSplit.incoming rs i ↔ ∃v u : V,i=(name v).castLE padded ∧ j=(name u).castLE padded ∧ v∈near u)
    (v u : Fin (2^ℓ)) (j : Fin D) (edge : rs v j=some u) : ∃k,rs u k=some v :=by
  have fresh : u∈DynamicSplit.incoming rs v:=List.mem_filterMap.mpr ⟨rs v j,List.mem_ofFn.mpr ⟨j,rfl⟩,edge⟩
  obtain ⟨a,b,va,ub,back⟩:=(members v u).1 fresh
  rw [va,ub];exact roster_member name padded near symm rs members b a back

private def rebaseResult (first last : Procedure w) (m result : Memory w)
    (firstCost lastCost : ℕ) (values : Prop) : Prop :=
  (first.seq last).Exec m result (firstCost+lastCost) ∧ values ∧ CheapCode (first.seq last)

private theorem join_rebase {first last : Procedure w} {m mid result : Memory w} {a b : ℕ}
    {ranks values : Prop} (one : first.Exec m mid a ∧ ranks ∧ CheapCode first)
    (two : ranks → last.Exec mid result b ∧ values ∧ CheapCode last) :
    rebaseResult first last m result a b values := by
  obtain ⟨runOne,ranked,cheapOne⟩ := one
  obtain ⟨runTwo,read,cheapTwo⟩ := two ranked
  exact ⟨@Procedure.Exec.then w first last m mid result a b (@runOne) (@runTwo),read,
    @ProtocolRAM.cheap_seq w first last (@cheapOne) (@cheapTwo)⟩

set_option maxHeartbeats 600000 in
/-- The common compiler's full run on actual stage adjacency and static
arithmetic ROMs. Select `.rank` for a new source’s donor ticket and `.path`
for the short directed reciprocal route. Neither output includes a rack ID. -/
theorem rebase_run (W : DescentHaloWalkRAM.Banks) (T : Ranks.Columns) (B : Rebase.Banks) (mode : Rebase.Output) (out : ℕ)
    (room1 : Fits W T.endpoints.base H D w) (room2 : Ranks.Fits T B.ranks.base H P w) (room3 : Rebase.Fits B out H D w)
    (endsBank : B.endpoints=T.endpoints) (input : Memory w) (old : Reads W R input)
    (start : ∀(v:Fin H)(p:Fin P),input (T.start.base+(Ranks.id v p).val)=((v.val*P:ℕ):Word w))
    (roots : ∀(v:Fin H)(p:Fin P),input (B.roots.base+(row v p).val)=(v.val:Word w))
    (offsets : ∀v : Fin H,input (B.offsets.base+v.val)=((v.val*P:ℕ):Word w))
    (hStart : T.start.base+T.start.size≤T.endpoints.base)
    (hRoots : B.roots.base+B.roots.size≤T.endpoints.base) (hOff : B.offsets.base+B.offsets.size≤T.endpoints.base) :
    let n:=H*P
    let f:=body W H D 4
    let g:=Ranks.body T P
    let h:=Rebase.body B mode H D
    let m₁:=image T.endpoints.base n f input
    let m₂:=image B.ranks.base n g m₁
    let result:=image out n h m₂
    rebaseResult ((scan w T.endpoints.base n f).seq (scan w B.ranks.base n g)) (scan w out n h)
      input result ((4+n*(2*f.work+4))+(4+n*(2*g.work+4))) (4+n*(2*h.work+4))
      (∀(v:Fin H)(p:Fin P),result (out+(row v p).val)=(Rebase.value R mode v p:Word w)) := by
  intro n f g h m₁ m₂ result
  refine @join_rebase w ((scan w T.endpoints.base n f).seq (scan w B.ranks.base n g))
    (scan w out n h) input m₂ result ((4+n*(2*f.work+4))+(4+n*(2*g.work+4))) (4+n*(2*h.work+4))
    (∀ (v : Fin H) (p : Fin P),m₂ (B.ranks.base+(row v p).val)=(Rebase.slot R .rank v p : Word w))
    (∀ (v : Fin H) (p : Fin P),result (out+(row v p).val)=(Rebase.value R mode v p : Word w))
    (execute R W T B.ranks.base room1 room2 input old start hStart) ?_
  intro ranked
  have gap : T.endpoints.base+n ≤ B.ranks.base :=
    (Nat.add_le_add_left room2.sizeEnd T.endpoints.base).trans room2.endpoints.2.2
  have initial (a : ℕ) (prev : a<T.endpoints.base) : m₂ a=input a :=
    (ProtocolRAMGeneratedWrite.frame_image B.ranks.base n g m₁ a
      (Or.inl (prev.trans_le ((Nat.le_add_right _ n).trans gap)))).trans
      (ProtocolRAMGeneratedWrite.frame_image T.endpoints.base n f input a (Or.inl prev))
  refine Rebase.run R B mode out room3 m₂ ⟨?_,ranked,?_,?_⟩
  · intro v p
    rw [endsBank]
    have beforeRanks : T.endpoints.base+(row v p).val < B.ranks.base :=
      (Nat.add_lt_add_left (row v p).isLt T.endpoints.base).trans_le gap
    exact (ProtocolRAMGeneratedWrite.frame_image B.ranks.base n g m₁ _ (Or.inl beforeRanks)).trans
      ((ProtocolRAMGeneratedWrite.read_image T.endpoints.base n f input (row v p)).trans
        (DescentHaloWalkRAM.body_at W T.endpoints.base room1 R input old v p 4))
  · intro v p
    have beforeEnds := (Nat.add_lt_add_left ((row v p).isLt.trans_le room3.rootCount) B.roots.base).trans_le hRoots
    exact (initial _ beforeEnds).trans (roots v p)
  · intro v
    have beforeEnds := (Nat.add_lt_add_left (v.isLt.trans_le room3.offsetCount) B.offsets.base).trans_le hOff
    exact (initial _ beforeEnds).trans (offsets v)

end
end Hierarchy.DescentHaloCompilation

end OAI
