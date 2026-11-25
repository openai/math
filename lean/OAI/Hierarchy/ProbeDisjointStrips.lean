import OAI.Hierarchy.ProbeChainPlacement

namespace OAI
/-! # The purchased strips of one activation use disjoint physical columns -/

namespace Hierarchy.ProbeStage
open AdaptiveProbe ChainStrip
open scoped Classical
noncomputable section

variable {h d k : ℕ} (S : PurchaseSampler) (π : Equiv.Perm (Fin (2^h))) (depth : ℕ)
    (marked : StageAt h d → (Fin k × Bool) → Finset (Fin (2^h)))

/-- Dropping sign labels from the disjoint live commodities still leaves distinct
stage/record rows, because actual mask decoding puts each record in a unique sign. -/
def plainRows (unique : ∀ s c c' r, r∈marked s c → r∈marked s c' → c=c') :
    LiveChains S π depth marked × Fin (depth+1) ↪ StageAt h d × Fin (2^h) where
  toFun p := (p.1.1,liveRow S π depth marked p.1 p.2)
  inj' := by
    rintro ⟨⟨s,c,i⟩,j⟩ ⟨⟨s',c',i'⟩,j'⟩ eq
    have ss := congrArg Prod.fst eq
    dsimp at ss; subst s'
    let a : LiveChains S π depth marked := ⟨s,c,i⟩
    let b : LiveChains S π depth marked := ⟨s,c',i'⟩
    have same : liveRow S π depth marked a j=liveRow S π depth marked b j' := congrArg Prod.snd eq
    have one := liveSlot_marked S π depth marked a j
    have two := liveSlot_marked S π depth marked b j'
    change liveRow S π depth marked a j∈marked s c at one
    change liveRow S π depth marked b j'∈marked s c' at two
    have member : liveRow S π depth marked a j∈marked s c' := by rw [same]; exact two
    have color := unique s c c' _ one member
    subst c'
    have pair : (i,j)=(i',j') := (liveDigit S π depth marked s c).injective same
    exact congrArg (fun v => ((⟨s,c,v.1⟩ : LiveChains S π depth marked),v.2)) pair

/-- The stage's matching puts records at distinct actual sockets on each side.
This uses full `(group,position)` addresses, including group padding. -/
def physicalPorts : (StageAt h d × Fin (2^h)) × Bool ↪ StageColumns h d where
  toFun p := let tile := advisedStage h d π p.1.1
             ⟨p.1.1,tile.group p.1.2,if p.2 then .inr (tile.output p.1.2) else .inl (tile.input p.1.2)⟩
  inj' := by
    rintro ⟨⟨s,r⟩,side⟩ ⟨⟨s',r'⟩,side'⟩ eq
    have sc := congrArg Sigma.fst eq
    dsimp at sc; subst s'
    have slots := eq_of_heq (Sigma.mk.inj_iff.mp eq).2
    have groups := congrArg Prod.fst slots
    have ports := congrArg Prod.snd slots
    cases side <;> cases side'
    · have same : r=r' := (advisedStage h d π s).input_inj (Prod.ext groups (by simpa using ports))
      subst r'; rfl
    · simp at ports
    · simp at ports
    · have same : r=r' := (advisedStage h d π s).output_inj (Prod.ext groups (by simpa using ports))
      subst r'; rfl

/-- A single combined injective site map certifies parallel ball replacements
have genuinely disjoint writable local sites, for all accepted paths in all groups. -/
def allStripColumns (unique : ∀ s c c' r, r∈marked s c → r∈marked s c' → c=c') :
    LiveChains S π depth marked × Columns depth ↪ StageColumns h d := by
  let divide (q : Columns depth) : Fin (depth+1) := ⟨q.val.val/2,by have bound := q.val.isLt; dsimp [edgeCount] at bound; omega⟩
  let split : (LiveChains S π depth marked × Columns depth) ↪ (LiveChains S π depth marked × Fin (depth+1)) × Bool := {
    toFun := fun x => ((x.1,divide x.2),decide (x.2.val.val%2=1))
    inj' := by
      rintro ⟨x,t⟩ ⟨x',t'⟩ eq
      have a := congrArg (fun p => p.1.1) eq
      have b := congrArg (fun p => (p.1.2:Fin (depth+1)).val) eq
      have par := congrArg Prod.snd eq
      dsimp at a b par; subst x'
      apply congrArg (fun q : Columns depth => (x,q)); apply Subtype.ext; apply Fin.ext
      change t.val.val/2=t'.val.val/2 at b
      by_cases z : t.val.val%2=1 <;> by_cases z' : t'.val.val%2=1 <;> simp [z,z'] at par <;> omega }
  exact (split.trans ((plainRows S π depth marked unique).prodMap (Function.Embedding.refl _))).trans (physicalPorts π)

theorem allStripColumns_single (unique : ∀ s c c' r, r∈marked s c → r∈marked s c' → c=c') (x : LiveChains S π depth marked) (q : Columns depth) :
    allStripColumns S π depth marked unique (x,q)=stripPlace S π depth marked x q := by
  let t : Fin (depth+1) := ⟨q.val.val/2,by have bound := q.val.isLt; dsimp [edgeCount] at bound; omega⟩
  let tile := advisedStage h d π x.1
  let row := liveRow S π depth marked x
  have group : tile.group (row t)=tile.group (row 0) := (live_in_ball S π depth marked x t).1
  change (⟨x.1,tile.group (row t),if decide (q.val.val%2=1) then Sum.inr (tile.output (row t)) else Sum.inl (tile.input (row t))⟩ : StageColumns h d) =
    ⟨x.1,tile.group (row 0),if q.val.val%2=0 then Sum.inl (tile.input (row t)) else Sum.inr (tile.output (row t))⟩
  by_cases side : q.val.val%2=0
  · have other : q.val.val%2≠1 := by omega
    simp [side,group]
  · have other : q.val.val%2=1 := by omega
    simp [other,group]

end
end Hierarchy.ProbeStage

end OAI
