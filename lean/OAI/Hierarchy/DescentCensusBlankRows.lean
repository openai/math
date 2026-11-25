import OAI.Hierarchy.DescentCensusCapacity
import OAI.Hierarchy.DescentNormalize

namespace OAI
/-! # Zero-width physical tethers through an ordinary stage -/

namespace Hierarchy.DescentSixParty.MarkedWorld
open Computability.BorderVNP.Crossing GadgetNetwork
open scoped Classical BigOperators
noncomputable section
variable {F P : Type} [Field F] {d : ℕ} {bits : P→ℕ} (W : MarkedWorld F d P bits)

omit [Field F] in
@[simp] theorem mem_blank (e : W.graph.Edge) : e∈W.blank ↔ e∉W.core ∧ W.graph.width e=0 := by
  simp [blank]

omit [Field F] in
theorem blank_pieces (q : ℕ) (m : W.graph.Edge→ℕ) (cut : ∀e∈W.core,W.graph.width e=m e*q) :
    (W.pieces q m cut).blank.card≤W.blank.card := by
  let Q:=W.pieces q m cut
  let first (e : Q.blank) : W.blank := by
    rcases e with ⟨old | fresh, mem⟩
    · exact ⟨old.val, (W.mem_blank old.val).2 ⟨old.property, ((Q.mem_blank _).mp mem).2⟩⟩
    · exact (((Q.mem_blank _).mp mem).1 (Finset.mem_map.mpr ⟨fresh, Finset.mem_univ _, rfl⟩)).elim
  apply Finset.card_le_card_of_injective (f:=first)
  rintro ⟨e|⟨e,id⟩,he⟩ ⟨f|⟨f,j⟩,hf⟩ eqn
  · have oldEq : e.val = f.val := congrArg (fun x : W.blank => x.val) eqn
    exact Subtype.ext (congrArg Sum.inl (show e = f from Subtype.ext oldEq))
  all_goals first
    | exact ((Q.mem_blank _).1 he).1 (Finset.mem_map.mpr ⟨_,Finset.mem_univ _,rfl⟩) |>.elim
    | exact ((Q.mem_blank _).1 hf).1 (Finset.mem_map.mpr ⟨_,Finset.mem_univ _,rfl⟩) |>.elim

theorem blank_selected {I C : Type} [Fintype I] (G : PoweredGadget F)
    (pick : I×Fin 2↪W.graph.Edge) (z : I→ℕ) (hz : ∀i,0<z i)
    (fit : ∀i s,W.graph.width (pick (i,s))=z i*G.b) (pack : W.graph.Site→C) (p : I→Profile G.C) :
    (W.selected G pick z hz fit pack p).blank.card≤W.blank.card := by
  let Q:=W.selected G pick z hz fit pack p
  let sw:=branchWidth G z p
  let pos:=fun _ : Merged W.graph pick (bestLayout sw) pack=>(0 : EuclideanSpace ℝ (Fin d))
  let ball:=fun u=>(by simp [pos] : ‖pos u‖≤1)
  let em : Q.graph.Edge↪GadgetNetwork.Edge (I:=I) W.graph := Function.Embedding.subtype _
  have incl : Q.blank.map em⊆W.blank.map Function.Embedding.inl := by
    intro t ht
    obtain ⟨e,mem,rfl⟩:=Finset.mem_map.mp ht
    obtain ⟨no,zero⟩:=(Q.mem_blank _).mp mem
    have old := mt (GadgetNetwork.mem_nextCore W.graph pick sw (bestLayout sw) pack pos ball W.core e).mpr no
    rcases e with ⟨oldEdge|gadget,remaining⟩
    · exact Finset.mem_map.mpr ⟨oldEdge,(W.mem_blank _).mpr ⟨old,zero⟩,rfl⟩
    · exact (old trivial).elim
  simpa using Finset.card_le_card incl

theorem blank_normalize (n : Normalize W) : n.result.blank.card≤W.blank.card := by
  induction n with
  | done _=>exact le_rfl
  | split A q m cut tail ih=>exact ih.trans (A.blank_pieces q m cut)
  | merge A V key hub k g tail ih=>
    apply ih.trans
    let Q:=A.coalesced key hub k g
    have coreOf (x : Q.graph.Edge) (marked : x.val ∈ A.core) : x ∈ Q.core := by
      apply Finset.mem_filter.mpr
      refine ⟨?_, marked⟩
      first
        | apply @Finset.mem_univ
        | exact @Finset.mem_univ _ (Subtype.fintype fun e : A.graph.Edge =>
            A.address key hub k g (A.graph.src e) ≠ A.address key hub k g (A.graph.dst e)) x
    apply Finset.card_le_card_of_injective (f:=fun e : Q.blank=>⟨e.val.val,
      (A.mem_blank _).mpr ⟨fun marked=>((Q.mem_blank _).mp e.property).1
        (coreOf e.val marked),((Q.mem_blank _).mp e.property).2⟩⟩)
    exact fun _ _ eqn=>Subtype.ext (Subtype.ext (congrArg (fun a : A.blank => a.val) eqn))
  | named A s e tail ih=>
    apply ih.trans
    let Q:=PhysicalRename.world A s e
    apply Finset.card_le_card_of_injective (f:=fun x : Q.blank=>⟨e.symm x.val,
      (A.mem_blank _).mpr ⟨fun old=>((Q.mem_blank _).mp x.property).1
        (by
          have mapped := (PhysicalRename.core_mem A s e (e.symm x.val)).2 old
          have same := congrArg (fun a : A.graph.Edge => a ∈ Q.core) (e.apply_symm_apply x.val)
          exact same.mp mapped),
        ((Q.mem_blank _).mp x.property).2⟩⟩)
    exact fun _ _ eqn=>Subtype.ext (e.symm.injective (congrArg (fun a : A.blank => a.val) eqn))

end
end Hierarchy.DescentSixParty.MarkedWorld

end OAI
