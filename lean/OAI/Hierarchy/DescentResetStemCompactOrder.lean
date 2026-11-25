import OAI.Hierarchy.DescentResetStemRoster
import OAI.Hierarchy.DescentPackedTicketChronology
import OAI.Hierarchy.DescentCableDonorNames

namespace OAI
/-! # Comparing actual old stem grains with bounded local coordinates -/
namespace Hierarchy.DescentResetStemCompactOrder
open DescentSixParty DescentSixParty.GroupStage DescentIssuedFallbackPanel DescentSharedCableNames.Stage
open DescentCompiler DescentGL DescentColonies DescentHostDirectory DescentPackedTicketChronology DescentPacking
open scoped Classical BigOperators
noncomputable section
set_option quotPrecheck false

/-- This rank is computed by comparisons on the genuinely reachable local digits. -/
def compress (domain : Finset ℕ) (x : ℕ) := (domain.filter (·<x)).card

theorem compress_bound (domain : Finset ℕ) (x : ℕ) : compress domain x≤domain.card :=
  Finset.card_le_card (Finset.filter_subset _ _)

theorem compress_lt (domain : Finset ℕ) {x y : ℕ} (hx : x∈domain) (hy : y∈domain) :
    compress domain x<compress domain y ↔ x<y := by
  have step {a b : ℕ} (ha : a∈domain) (ab : a<b) : compress domain a<compress domain b := by
    apply Finset.card_lt_card
    have part : domain.filter (·<a)⊆domain.filter (·<b):=by
      intro i hi;rcases Finset.mem_filter.mp hi with ⟨inside,less⟩
      exact Finset.mem_filter.mpr ⟨inside,less.trans ab⟩
    exact (Finset.ssubset_iff_of_subset part).mpr ⟨a,Finset.mem_filter.mpr ⟨ha,ab⟩,by simp⟩
  constructor
  · intro strict
    rcases lt_trichotomy x y with yes|same|no
    · exact yes
    · subst y;exact (lt_irrefl _ strict).elim
    · exact (strict.not_gt (step hy no)).elim
  · exact step hx

theorem compress_eq (domain : Finset ℕ) {x y : ℕ} (hx : x∈domain) (hy : y∈domain) :
    compress domain x=compress domain y ↔ x=y := by
  constructor
  · intro same;apply le_antisymm <;> apply le_of_not_gt <;> intro less
    · exact (same.symm.not_lt ((compress_lt domain hy hx).mpr less))
    · exact same.not_lt ((compress_lt domain hx hy).mpr less)
  · rintro rfl;rfl

variable {F P V : Type} [Field F] [Fintype V] [DecidableEq V]
    {groups d k m c i : ℕ} {bits : P→ℕ} {W : MarkedWorld F d P bits} {G : PoweredGadget F}
    {q ε : ℝ} (A : GroupStage W G q ε (Fin groups) V k) (S : AtomSchedule) (ready : A.StateBounds S i)
variable (digits : Block m≃Fin groups×Block k) (basis : Layout m) (fits : c≤ m)
variable (vertex : V↪Fin (Fintype.card V)) (v : V) (hi : Block c)
local notation "L" => 2^(m-c)
local notation "E" => Grain A
local notation "oldsrc" => fun e : Grain A=>W.graph.src e.1
local notation "oldhome" => home A
local notation "oldgroup" => fun e : Grain A=>(A.pos (oldsrc e)).1.val
local notation "oldhost" => fun e : Grain A=>(vertex (A.pos (oldsrc e)).2).val
local notation "oldblock" => fun e : Grain A=>(A.block (oldsrc e)).val

/-- The group digits come from the previous physical donors in precisely the
one remixed subcell being read. An old edge preserves group and fine block. -/
def groupDomain := Finset.univ.image (fun low : Fin L=>(donor digits basis fits v hi low).1.1.val)

def hostDomain {K : Type} [Fintype K] [DecidableEq K] (A : GroupStage W G q ε K V k)
    (vertex : V↪Fin (Fintype.card V)) (v : V) : Finset ℕ := (insert v (A.near v)).image (fun u=>(vertex u).val)

def Located (s : Bool) (e : E) : Prop :=
  (A.pos (endSite A s e)).2=v ∧ group c (rearrange basis (oldBlock digits (oldhome (endSite A s e))))=hi.val

theorem in_scope (s : Bool) (e : E) (located : Located A digits basis v hi s e) :
    oldgroup e∈groupDomain digits basis fits v hi ∧ oldhost e∈hostDomain A vertex v := by
  let p:=endSite A s e
  obtain ⟨hgroup,hnear⟩ : (A.pos (oldsrc e)).1=(A.pos p).1 ∧ (A.pos (oldsrc e)).2∈insert v (A.near v):=by
    cases s with
    | false=>exact ⟨rfl,Finset.mem_insert.mpr (.inl located.1)⟩
    | true=>
      obtain ⟨u,near,atSrc⟩:=Finset.mem_map.mp (A.peers e.1).2
      have hgroup : (A.pos (oldsrc e)).1=(A.pos (W.graph.dst e.1)).1:=(congrArg Prod.fst atSrc).symm
      have srcHost : u=(A.pos (oldsrc e)).2:=congrArg Prod.snd atSrc
      rw [srcHost] at near
      have center : (A.pos (W.graph.dst e.1)).2=v:=located.1
      rw [center] at near
      exact ⟨hgroup,Finset.mem_insert.mpr (.inr near)⟩
  constructor
  · refine Finset.mem_image.mpr ⟨subcell digits basis (c:=c) (oldhome p),Finset.mem_univ _,?_⟩
    have atDonor:=donor_locates digits basis fits (oldhome p) v hi located.1 located.2
    exact (congrArg (fun z=>(z.1.1 : Fin groups).val) atDonor).trans (congrArg Fin.val hgroup.symm)
  · exact Finset.mem_image.mpr ⟨_,hnear,rfl⟩

omit [Fintype V] [DecidableEq V] in
theorem group_bound : (groupDomain digits basis fits v hi).card≤L := by
  simpa [groupDomain] using (Finset.card_image_le (s:=Finset.univ) (f:=fun low : Fin L=>(donor digits basis fits v hi low).1.1.val))

theorem host_bound : (hostDomain A vertex v).card≤A.degree+1 := by
  exact Finset.card_image_le.trans ((Finset.card_insert_le _ _).trans (Nat.add_le_add_right (A.degreeBound v) 1))

/-- The entire old source coordinate is represented locally by one donor
group ordinal, one neighbor-host ordinal and the genuine original block. -/
def sourceDigit (e : E) :=
  (compress (groupDomain digits basis fits v hi) (oldgroup e)*(A.degree+2)+compress (hostDomain A vertex v) (oldhost e))*2^k+oldblock e

theorem source_room (e : E) :
    sourceDigit A digits basis fits vertex v hi e < (L+1)*(A.degree+2)*2^k := by
  have groupLt:=lt_of_le_of_lt ((compress_bound _ (oldgroup e)).trans (group_bound digits basis fits v hi)) (Nat.lt_succ_self _)
  have hostLt:=lt_of_le_of_lt ((compress_bound _ (oldhost e)).trans (host_bound A vertex v)) (Nat.lt_succ_self _)
  let g:=compress (groupDomain digits basis fits v hi) (oldgroup e)
  let t:=compress (hostDomain A vertex v) (oldhost e)
  have pairLt : g*(A.degree+2)+t<(L+1)*(A.degree+2):=calc
    _<g*(A.degree+2)+(A.degree+2):=Nat.add_lt_add_left hostLt _
    _=(g+1)*(A.degree+2):=(Nat.succ_mul ..).symm
    _≤(L+1)*(A.degree+2):=Nat.mul_le_mul_right _ groupLt
  calc
    _<(g*(A.degree+2)+t)*2^k+2^k:=Nat.add_lt_add_left (A.block (oldsrc e)).isLt _
    _=(g*(A.degree+2)+t+1)*2^k:=(Nat.succ_mul ..).symm
    _≤_:=Nat.mul_le_mul_right _ pairLt

variable (coord : Function.Injective (fun u=>(A.pos u,A.block u)))
variable (indexed : ∀u,originalId W.graph.Site u=(A.site vertex coord u).val)

include coord indexed

theorem source_original (s : Bool) (x y : E) (atX : Located A digits basis v hi s x)
    (atY : Located A digits basis v hi s y) :
    sourceDigit A digits basis fits vertex v hi x < sourceDigit A digits basis fits vertex v hi y ↔
      originalId W.graph.Site (oldsrc x)<originalId W.graph.Site (oldsrc y) := by
  let gd:=groupDomain digits basis fits v hi
  let hd:=hostDomain A vertex v
  obtain ⟨gx,hx⟩:=in_scope A digits basis fits vertex v hi s x atX
  obtain ⟨gy,hy⟩:=in_scope A digits basis fits vertex v hi s y atY
  let mid (e : E):=compress gd (oldgroup e)*(A.degree+2)+compress hd (oldhost e)
  let raw (e : E):=oldgroup e*Fintype.card V+oldhost e
  have hostRoom (e : E) : compress hd (oldhost e)<A.degree+2:=
    lt_of_le_of_lt ((compress_bound ..).trans (host_bound A vertex v)) (Nat.lt_succ_self _)
  have midLess (a b : E) (ga : oldgroup a∈gd) (gb : oldgroup b∈gd)
      (ha : oldhost a∈hd) (hb : oldhost b∈hd) : mid a< mid b ↔ raw a<raw b := by
    rw [show mid a< mid b ↔ _ from DescentCableDonorNames.digit_lt (hostRoom a) (hostRoom b),
      show raw a<raw b ↔ _ from DescentCableDonorNames.digit_lt
        (vertex (A.pos (oldsrc a)).2).isLt (vertex (A.pos (oldsrc b)).2).isLt,
      compress_lt gd ga gb,compress_eq gd ga gb,compress_lt hd ha hb]
  have midEq : mid x=mid y ↔ raw x=raw y := by
    constructor <;> intro eqn <;> apply le_antisymm <;> apply le_of_not_gt <;> intro bad
    · exact ((midLess y x gy gx hy hx).mpr bad).ne eqn.symm
    · exact ((midLess x y gx gy hx hy).mpr bad).ne eqn
    · exact ((midLess y x gy gx hy hx).mp bad).ne eqn.symm
    · exact ((midLess x y gx gy hx hy).mp bad).ne eqn
  rw [indexed,indexed]
  change _ ↔ DescentPhysicalOrder.physical (DescentSiteTape.rank (A.siteSlot vertex coord)) (oldsrc x)<
    DescentPhysicalOrder.physical (DescentSiteTape.rank (A.siteSlot vertex coord)) (oldsrc y)
  rw [DescentPhysicalOrder.physical_lt_iff]
  change _ ↔ (A.siteSlot vertex coord (oldsrc x)).val<(A.siteSlot vertex coord (oldsrc y)).val
  rw [A.siteSlot_val,A.siteSlot_val]
  change mid x*2^k+oldblock x< mid y*2^k+oldblock y ↔ raw x*2^k+oldblock x<raw y*2^k+oldblock y
  simp only [DescentCableDonorNames.digit_lt (A.block (oldsrc x)).isLt (A.block (oldsrc y)).isLt,midLess x y gx gy hx hy,midEq]

/-- Honest short comparison at either endpoint of a stem. All operand
bounds are independent of the number of prior hosts and groups. -/
theorem scope_before (order : W.graph.Edge↪Fin (Fintype.card W.graph.Edge)) (sorted : SourceSorted W order)
    (s : Bool) (x y : E) (atX : Located A digits basis v hi s x) (atY : Located A digits basis v hi s y) :
    (DescentOrderedReset.grains W A.grainCount order x)<(DescentOrderedReset.grains W A.grainCount order y) ↔
      before (sourceDigit A digits basis fits vertex v hi x) (outgoingSlot A S ready order x).val x.2.val
        (sourceDigit A digits basis fits vertex v hi y) (outgoingSlot A S ready order y).val y.2.val := by
  have xy:=source_original A digits basis fits vertex v hi coord indexed s x y atX atY
  have yx:=source_original A digits basis fits vertex v hi coord indexed s y x atY atX
  have eqn : sourceDigit A digits basis fits vertex v hi x=sourceDigit A digits basis fits vertex v hi y ↔
      originalId W.graph.Site (oldsrc x)=originalId W.graph.Site (oldsrc y) := by
    constructor <;> intro h <;> apply le_antisymm <;> apply le_of_not_gt <;> intro bad
    · exact (yx.mpr bad).ne h.symm
    · exact (xy.mpr bad).ne h
    · exact (yx.mp bad).ne h.symm
    · exact (xy.mp bad).ne h
  rw [actual_before A S ready order sorted]
  simp only [before,xy,eqn]

end
end Hierarchy.DescentResetStemCompactOrder

end OAI
