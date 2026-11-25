import OAI.Hierarchy.DescentStarKeys
import OAI.Hierarchy.DescentHostDirectory
import OAI.Hierarchy.DescentMergedCableCost

namespace OAI
/-! # Eight directory hops for each actual surviving motif cable -/

namespace Hierarchy.DescentSixParty.StarKeys
open Computability.BorderVNP.Crossing DescentHostDirectory GadgetNetwork
open scoped Classical
noncomputable section

variable {V : Type} [DecidableEq V] (near : V→Finset V) (D slots : ℕ)

def Linked (x y : Key V) : Prop := y∈next near D slots x ∧ x∈next near D slots y

protected theorem Linked.symm {x y : Key V} (h : Linked near D slots x y) :
    Linked near D slots y x := ⟨h.2,h.1⟩

private inductive Walk : ℕ→Key V→Key V→Prop
  | stay (a) : Walk 0 a a
  | hop {a b} (edge : Linked near D slots a b) : Walk 1 a b
  | append {a b c m n} (left : Walk m a b) (right : Walk n b c) : Walk (m+n) a c

private theorem Walk.back {a b : Key V} {n : ℕ} (h : Walk near D slots n a b) :
    Walk near D slots n b a := by
  induction h with
  | stay _ => exact .stay _
  | hop h => exact .hop ⟨h.2,h.1⟩
  | append _ _ ih jh => simpa only [Nat.add_comm] using Walk.append jh ih

private theorem Walk.follow {a b c : Key V} {n k : ℕ} (h : Walk near D slots n a b)
    (initialPath : a∈directory near D slots k c) : b∈directory near D slots (k+n) c := by
  induction h generalizing k with
  | stay _ => simpa using initialPath
  | hop h => exact extend initialPath h.1
  | append _ _ ih jh => simpa only [Nat.add_assoc] using jh (ih initialPath)

private theorem Walk.result {a b : Key V} {n : ℕ} (h : Walk near D slots n a b) :
    b∈directory near D slots n a := by
  simpa using Walk.follow near D slots h (k:=0) (c:=a) (by simp [directory])

variable {n : ℕ} {P : Type*} {bits : P→ℕ} {I C S : Type} [Fintype I]
variable (N : Network n P bits) (pick : I×Fin 2 ↪ N.Edge) (l : Bool)
    (pack : N.Site→C⊕S) (slot : I→S) (center : I→C)
    (sourceAt : ∀i,pack (N.src (pick (i,1)))=.inr (slot i))
    (centerAt : ∀i,pack (thickCenter N pick l i)=.inl (center i))
    (coherent : ∀i j,slot i=slot j→center i=center j)
    (physical : C⊕S ↪ Key V) (room : ∀p,(physical p).2.2<slots)
    (cable : ∀e, Linked near D slots (physical (pack (N.src e))) (physical (pack (N.dst e))))
    (together : ∀i, Linked near D slots (physical (pack (N.src (pick (i,0)))))
      (physical (pack (N.src (pick (i,1))))))

include room in
private theorem waitHop (p : C⊕S) : Walk near D slots 1 (physical p) (physical p) :=
  .hop ⟨pad _ (room p),pad _ (room p)⟩

include sourceAt centerAt cable together room in
/-- An attached thin slot is within two physical links of its center. -/
private theorem resolve_walk (u : N.Site) : Walk near D slots 2
    (physical (resolve slot center (pack u))) (physical (pack u)) := by
  have idle (p : C⊕S) := waitHop near D slots physical room p
  cases h : pack u with
  | inl c => exact (idle (.inl c)).append (idle _)
  | inr s =>
    by_cases active : ∃i,slot i=s
    · let i := active.choose
      have thin : pack (N.src (pick (i,1)))=.inr s := by rw [sourceAt,active.choose_spec]
      have cent : resolve slot center (.inr s)=pack (thickCenter N pick l i) := by
        rw [centerAt];simp [resolve,active,i]
      rw [cent,←thin]
      cases l with
      | false => exact (idle _).append (.hop (together i))
      | true => exact (Walk.hop (cable (pick (i,0))).symm).append (.hop (together i))
    · rw [resolve,dite_eq_right active]
      exact (idle _).append (idle _)

include room cable together in
omit [Fintype I] in
/-- Every gadget party is within two links of the original thick source. -/
private theorem anchor_walk (i : I) (j : Fin 6) : Walk near D slots 2
    (physical (pack (anchor N pick l (.inr (i,j))))) (physical (pack (N.src (pick (i,0))))) := by
  have idle (p : C⊕S) := waitHop near D slots physical room p
  change Walk _ _ _ _ (physical (pack (endpoint N pick i (cluster l j)))) _
  generalize cluster l j=a
  fin_cases a
  · exact (idle _).append (idle _)
  · exact (Walk.hop (cable (pick (i,0))).symm).append (idle _)
  · exact (Walk.hop (cable (pick (i,1))).symm).append (.hop (together i).symm)

/-- Every newly supplied cable is named from the thick cable of its actual
matched pair. Old cables retain their old source donor. -/
def donorEdge : GadgetNetwork.Edge (I:=I) N → N.Edge
  | .inl e=>e
  | .inr (.inl (i,_))=>pick (i,0)
  | .inr (.inr (i,_))=>pick (i,0)

include cable together room in
/-- A retained local tensor has its own old site in the same bounded donor
directory, including a vertex without any incident edge. -/
theorem old_donor_mem (u : N.Site) :
    physical (pack u)∈directory near D slots 4
      (physical (key N pick l pack slot center sourceAt centerAt coherent
        (newSite N pick l pack (.inl u)))) := by
  let wait:=waitHop near D slots physical room (pack u)
  exact Walk.result near D slots ((resolve_walk near D slots N pick l pack slot center sourceAt centerAt
    physical room cable together u).append (wait.append wait))

include cable together room in
theorem born_donor_mem (i : I) (j : Fin 6) :
    physical (pack (N.src (pick (i,0))))∈directory near D slots 4
      (physical (key N pick l pack slot center sourceAt centerAt coherent
        (newSite N pick l pack (.inr (i,j))))) := by
  let before:=resolve_walk near D slots N pick l pack slot center sourceAt centerAt
    physical room cable together (anchor N pick l (.inr (i,j)))
  exact Walk.result near D slots (before.append (anchor_walk near D slots N pick l pack physical room cable together i j))

include cable together room in
theorem donor_mem (e : GadgetNetwork.Edge (I:=I) N) :
    physical (pack (N.src (donorEdge N pick e)))∈directory near D slots 4
      (physical (key N pick l pack slot center sourceAt centerAt coherent
        (newSite N pick l pack (GadgetNetwork.source N e)))) := by
  let s:=GadgetNetwork.source N e
  let u:=anchor N pick l s
  have resolved:=resolve_walk near D slots N pick l pack slot center sourceAt centerAt physical room cable together u
  have leg : Walk near D slots 2 (physical (pack u)) (physical (pack (N.src (donorEdge N pick e)))) := by
    rcases e with e|⟨i,j⟩|⟨i,j⟩
    · exact (waitHop near D slots physical room _).append (waitHop near D slots physical room _)
    · exact anchor_walk near D slots N pick l pack physical room cable together i (demandDst j)
    · exact anchor_walk near D slots N pick l pack physical room cable together i (supplySrc j)
  exact Walk.result near D slots (resolved.append leg)

include cable together room in
/-- The injection gives one physical position for each true quotient site.
Every true external cable, with its exact two quotient sites, is present in
the eighth power of the finite directory. -/
theorem merged_cables_both (sw : I→Fin 8→ℕ) {d : ℕ}
    (pos : Merged N pick l pack→EuclideanSpace ℝ (Fin d)) (hpos : ∀q,‖pos q‖≤1) :
    let addr := (⟨key N pick l pack slot center sourceAt centerAt coherent,
      key_injective N pick l pack slot center sourceAt centerAt coherent⟩ :
      Merged N pick l pack ↪ C⊕S).trans physical
    let M := merged N pick sw l pack pos hpos
    ∀e : M.Edge, addr (M.dst e)∈directory near D slots 8 (addr (M.src e)) ∧
      addr (M.src e)∈directory near D slots 8 (addr (M.dst e)) := by
  dsimp only
  intro e
  let start := GadgetNetwork.source N e.val
  let stop := GadgetNetwork.target N pick e.val
  let name := fun s=>physical (resolve slot center (pack (anchor N pick l s)))
  change name stop∈directory near D slots 8 (name start) ∧ name start∈directory near D slots 8 (name stop)
  have resolveAt (s) : Walk near D slots 2 (name s) (physical (pack (anchor N pick l s))) :=
    resolve_walk near D slots N pick l pack slot center sourceAt centerAt physical room cable together _
  have anchorAt := anchor_walk near D slots N pick l pack physical room cable together
  have idle (p : C⊕S) := waitHop near D slots physical room p
  have middle : Walk near D slots 4 (physical (pack (anchor N pick l start)))
      (physical (pack (anchor N pick l stop))) := by
    obtain ⟨edge,crosses⟩ := e
    rcases edge with wire|⟨i,s⟩|⟨i,j⟩
    · cases h : selected N pick wire with
      | none =>
        change Walk _ _ _ _ (physical (pack (N.src wire)))
          (physical (pack (anchor N pick l (GadgetNetwork.target N pick (.inl wire)))))
        rw [GadgetNetwork.target,h]
        exact (((Walk.hop (cable wire)).append (idle _)).append (idle _)).append (idle _)
      | some q =>
        exfalso
        apply crosses
        change newSite N pick l pack (.inl (N.src wire))=
          newSite N pick l pack (GadgetNetwork.target N pick (.inl wire))
        rw [GadgetNetwork.target,h,←selected_spec N pick h]
        exact source_merge N pick l pack q.1 q.2
    · exact False.elim (crosses (target_merge N pick l pack i s).symm)
    · exact (anchorAt i (supplySrc j)).append (Walk.back near D slots (anchorAt i (supplyDst j)))
  have walk := ((resolveAt start).append middle).append (Walk.back near D slots (resolveAt stop))
  exact ⟨Walk.result near D slots walk,Walk.result near D slots (Walk.back near D slots walk)⟩

include room cable together in
theorem merged_cables (sw : I→Fin 8→ℕ) {d : ℕ}
    (pos : Merged N pick l pack→EuclideanSpace ℝ (Fin d)) (hpos : ∀q,‖pos q‖≤1) :
    let addr := (⟨key N pick l pack slot center sourceAt centerAt coherent,
      key_injective N pick l pack slot center sourceAt centerAt coherent⟩ :
      Merged N pick l pack ↪ C⊕S).trans physical
    let M := merged N pick sw l pack pos hpos
    ∀e : M.Edge, addr (M.dst e)∈directory near D slots 8 (addr (M.src e)) := by
  dsimp only
  intro e
  exact (merged_cables_both near D slots N pick l pack slot center sourceAt centerAt coherent physical room cable together sw pos hpos e).1

end
end Hierarchy.DescentSixParty.StarKeys

end OAI
