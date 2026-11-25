import OAI.Hierarchy.DescentPackedOwnerWord
import OAI.Hierarchy.DescentPackedReverseMatch
import OAI.Hierarchy.DescentStarKeys

namespace OAI
/-! # Recovering the actual redirect of a previous thin pack from its issued rows -/

namespace Hierarchy.DescentPacking.PackedMatch
open DescentSIMDLookup PackedLocalMatch DescentSixParty.StarKeys
open scoped Classical
noncomputable section
variable {s : Shape}

theorem interval_unique {n : ℕ} (wt : Fin n→ℕ) {u v : Fin n} {j : ℕ}
    (lu : ProtocolRAMPortRanks.«prefix» wt Fin.val u≤j) (ru : j<ProtocolRAMPortRanks.«prefix» wt Fin.val u+wt u)
    (lv : ProtocolRAMPortRanks.«prefix» wt Fin.val v≤j) (rv : j<ProtocolRAMPortRanks.«prefix» wt Fin.val v+wt v) : u=v := by
  apply Fin.ext
  rcases Nat.lt_trichotomy u.val v.val with h|h|h
  · have h':=ProtocolRAMPortRanks.prefix_disjoint wt Fin.val h;omega
  · exact h
  · have h':=ProtocolRAMPortRanks.prefix_disjoint wt Fin.val h;omega

def unitPack (x : Inputs s) (e : MatchedUnit x) : Fin s.packs := index (need x) (cap x) e.2.1.val
private theorem own (x : Inputs s) (e : MatchedUnit x) :
    interval (s:=s) (need x) (unitPack x e) (fields (need x) (cap x) e).thin := by
  let t:=unitPack x e
  change ProtocolRAMPortRanks.«prefix» (need x) Fin.val t ≤ _ ∧
    ProtocolRAMPortRanks.«prefix» (need x) Fin.val t+e.2.2.val<ProtocolRAMPortRanks.«prefix» (need x) Fin.val t+need x t
  have room : e.2.2.val<need x t :=
    e.2.2.isLt.trans_le (amount_at (need x) (cap x) e.2.1.val).le
  exact ⟨Nat.le_add_right _ _,Nat.add_lt_add_left room _⟩

local notation "out" => fun x=>decodeOutput s (lookupCell s (encodeInput x))
def unitRow (x : Inputs s) (h : Bounded x) (e : MatchedUnit x) : Fin s.pairs :=
  ⟨(fields (need x) (cap x) e).accepted,unit_index x h e⟩

theorem belongs (x : Inputs s) (h : Bounded x) (wide : 0<s.digit) (u : Fin s.packs) (e : MatchedUnit x) :
    redirects x (out x) u (unitRow x h e)=true ↔ unitPack x e=u := by
  have small:=(bounds (need x) (cap x) e).2.2.1.trans_le h.thin
  have live : ((out x).row (unitRow x h e) 0).val=1 := by
    unfold unitRow
    rw [unit_row x h e]
    exact short_val (Nat.one_lt_two_pow wide.ne')
  have thin : ((out x).row (unitRow x h e) 3).val=(fields (need x) (cap x) e).thin := by
    unfold unitRow
    rw [unit_row x h e]
    exact short_val (small.trans h.entries)
  unfold redirects
  constructor
  · intro yes
    have inside := (of_decide_eq_true yes).2
    rw [thin] at inside
    have own':=own x e
    exact interval_unique _ own'.1 own'.2 inside.1 inside.2
  · rintro rfl
    apply decide_eq_true
    refine ⟨live,?_⟩
    rw [thin]
    exact own x e

theorem head_real (x : Inputs s) (h : Bounded x) (wide : 0<s.digit) (u : Fin s.packs) {j : Fin s.pairs}
    (found : headRow x (out x) u=some j) : ∃e : MatchedUnit x,unitRow x h e=j ∧ unitPack x e=u := by
  have yes:=List.find?_some found
  change redirects x (out x) u j=true at yes
  have actual : j.val<amount x:=by
    by_contra! late
    simp only [redirects,empty_row x h j late,Fin.val_zero,Nat.zero_ne_one,false_and,decide_false] at yes
    cases yes
  let rank:=pairNumber id (packing (need x) (cap x)).decisions
  let e : MatchedUnit x:=rank.symm ⟨j.val,actual⟩
  have eqn : unitRow x h e=j:=Fin.ext (congrArg (fun i : Fin (amount x)=>i.val)
    (rank.apply_symm_apply ⟨j.val,actual⟩))
  exact ⟨e,eqn,(belongs x h wide u e).mp (eqn.symm ▸ yes)⟩

theorem head_none (x : Inputs s) (h : Bounded x) (wide : 0<s.digit) (u : Fin s.packs) :
    headRow x (out x) u=none ↔ ¬∃e : MatchedUnit x,unitPack x e=u := by
  constructor
  · rintro empty ⟨e,hit⟩
    have yes : (headRow x (out x) u).isSome :=
      List.find?_isSome.mpr ⟨unitRow x h e,List.mem_finRange _,(belongs x h wide u e).mpr hit⟩
    simp [empty] at yes
  · intro miss
    cases found:headRow x (out x) u with
    | none=>rfl
    | some j=>
      obtain ⟨e,_,hit⟩:=head_real x h wide u found
      exact False.elim (miss ⟨e,hit⟩)



def centerOf (l : Bool) (x : Inputs s) (h : Bounded x) (e : MatchedUnit x) : Cell s.digit :=
  let room:=((bounds (need x) (cap x) e).2.2.2).trans_le h.thick
  x.thick ⟨(fields (need x) (cap x) e).thick,room⟩ (if l then 2 else 1)

theorem center_read (l : Bool) (x : Inputs s) (h : Bounded x) (e : MatchedUnit x) :
    centerAt l (out x) (unitRow x h e)=centerOf l x h e := by
  unfold centerAt unitRow
  rw [unit_row x h e]
  cases l <;> rfl

/-- Translating the returned thick handle to its actual host/colony gives
the same collapsed name as the quotient resolver, independently of which
of a pack's matching units occurs first. -/
theorem resolve_report {C : Type} (read : Cell s.digit→C) (l : Bool) (x : Inputs s) (h : Bounded x)
    (wide : 0<s.digit) (u : Fin s.packs)
    (coherent : ∀e e',unitPack x e=unitPack x e'→ read (centerOf l x h e)=read (centerOf l x h e')) :
    (match headRow x (out x) u with
     | none=>Sum.inr u
     | some j=>Sum.inl (read (centerAt l (out x) j))) =
        resolve (unitPack x) (fun e=>read (centerOf l x h e)) (.inr u) := by
  cases found:headRow x (out x) u with
  | none=>simp [resolve,(head_none x h wide u).mp found]
  | some j=>
    obtain ⟨e,eqn,atU⟩:=head_real x h wide u found
    change Sum.inl (read (centerAt l (out x) j))=resolve (unitPack x) (fun e=>read (centerOf l x h e)) (.inr u)
    rw [←eqn,←atU,center_read l x h e,resolve_active _ _ coherent e]

end
end Hierarchy.DescentPacking.PackedMatch

end OAI
