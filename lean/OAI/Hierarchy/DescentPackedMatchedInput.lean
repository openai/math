import OAI.Hierarchy.DescentMarkedNeighborToken
import OAI.Hierarchy.DescentMatcherRateNumbers
import OAI.Hierarchy.DescentPackedMatchingCell
import OAI.Hierarchy.DescentThinPacks

namespace OAI
/-! # Source-local whole-pack and original-edge inputs from marked physical ports -/

namespace Hierarchy.DescentPacking.PackedMatch.Local
open DescentSIMDLookup
open scoped Classical BigOperators
noncomputable section
variable {r D p digit : ℕ}

/-- Live site tickets carry the actual winning code (one plus twice the local
leaf ordinal plus the paint). Marked source ports carry one plus the immutable
neighbor ordinal. Zero fills the corresponding inactive source or port slot. -/
structure Panel (r D p digit : ℕ) where
  winner : Fin r→Cell digit
  neighbor : Fin r→Fin p→Cell digit
  peerWinner : Fin D→Fin r→Cell digit

def encodePanel (u : Panel r D p digit) : Cell (digit*fields r D p) :=
  encode digit (fields r D p) (Fin.addCases u.winner (Fin.addCases
    (fun i : Fin (r*p)=>u.neighbor (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)
    (fun i : Fin (D*r)=>u.peerWinner (finProdFinEquiv.symm i).1 (finProdFinEquiv.symm i).2)))

def decodePanel (s : Cell (digit*fields r D p)) : Panel r D p digit :=
  let get := (encode digit (fields r D p)).symm s
  ⟨fun i=>get (Fin.castAdd (r*p+D*r) i),
   fun x i=>get (Fin.natAdd r (Fin.castAdd (D*r) (finProdFinEquiv (x,i)))),
   fun v x=>get (Fin.natAdd r (Fin.natAdd (r*p) (finProdFinEquiv (v,x))))⟩

@[simp] theorem decode_encode_panel (u : Panel r D p digit) : decodePanel (encodePanel u)=u := by
  cases u
  unfold decodePanel encodePanel fields
  simp only [Equiv.symm_apply_apply,Fin.addCases_left,Fin.addCases_right]

def leaf (v : ℕ) := (v-1)/2
def thick (v : ℕ) := (v-1)%2=1

def sites (u : Panel r D p digit) (key : ℕ) (paint : Bool) :=
  (List.finRange r).filter fun x=>u.winner x≠0 ∧ leaf (u.winner x).val=key ∧ decide (thick (u.winner x).val)=paint

def peer (u : Panel r D p digit) (x : Fin r) (s : Fin p) : Option (Fin D) :=
  let word := (u.neighbor x s).val
  if h : 0<word ∧ word≤D then some ⟨word-1,by omega⟩ else none

/-- The first present original block fixes the numerical order of an occupied
colony inside a neighbor host. Host ordinals already occur in original physical order. -/
def earlier (u : Panel r D p digit) (v : Fin D) (x : Fin r) (n : ℕ) : Prop :=
  ∃y : Fin r,y.val=n ∧ u.peerWinner v y≠0 ∧ leaf (u.peerWinner v y).val=leaf (u.peerWinner v x).val

def first (u : Panel r D p digit) (v : Fin D) (x : Fin r) : ℕ :=
  if h : ∃n,earlier u v x n then Nat.find h else r

theorem first_live (u : Panel r D p digit) (v : Fin D) (x : Fin r) (alive : u.peerWinner v x≠0) :
    earlier u v x (first u v x) ∧ first u v x≤x.val := by
  have here : earlier u v x x.val := ⟨x,rfl,alive,rfl⟩
  have h : ∃n,earlier u v x n := ⟨_,here⟩
  rw [first,dite_eq_left h]
  exact ⟨Nat.find_spec h,Nat.find_min' h here⟩

theorem first_same (u : Panel r D p digit) (v : Fin D) (x y : Fin r)
    (same : leaf (u.peerWinner v x).val=leaf (u.peerWinner v y).val) : first u v x=first u v y := by
  have equal : earlier u v x=earlier u v y := by funext n;simp only [earlier,same]
  simp only [first,equal]

/-- Slot zero is available to the zero-demand sentinel. All positive capacities
lie at actual old-neighbor / first-block coordinates. -/
def bin (u : Panel r D p digit) (v : Fin D) (x : Fin r) := 1+(v.val*r+first u v x)

abbrev Port (r p : ℕ) := Fin r×Fin p

def atBin (u : Panel r D p digit) (x : Fin r) (b : ℕ) : List (Port r p) :=
  ((List.finRange p).filter fun i=>(peer u x i).any fun v=>decide (bin u v x=b)).map (fun i=>(x,i))

def inBlock (u : Panel r D p digit) (bins : ℕ) (x : Fin r) := (List.finRange bins).flatMap fun b=>atBin u x b.val

def countAt (u : Panel r D p digit) (bins : ℕ) (x : Fin r) := (inBlock u bins x).length

def details (u : Panel r D p digit) (i : Port r p) : Fin 3→ℕ :=
  ![i.1.val*p+i.2.val,i.1.val,((peer u i.1 i.2).map (fun v=>v.val*r+i.1.val)).getD 0]

def thinStream (u : Panel r D p digit) (bins key : ℕ) :=
  (sites u key false).flatMap (inBlock u bins)

def thickBins (u : Panel r D p digit) (key b : ℕ) := (sites u key true).flatMap fun x=>atBin u x b

def thickStream (u : Panel r D p digit) (bins key : ℕ) := (List.finRange bins).flatMap fun b=>thickBins u key b.val

def packs (u : Panel r D p digit) (bins B key : ℕ) := thinPacks (countAt u bins) B (sites u key false)

def triple (u : Panel r D p digit) (stream : List (Port r p)) (i : ℕ) (j : Fin 3) :=
  ((stream[i]?).map fun v=>details u v j).getD 0

/-- The profile-free phase computes the actual pair census before any globally
compacted selector is routed. The same input fields admit a subsequent profile pass. -/
def inputs (s : Shape) (B key : ℕ) (u : Panel r D p digit) (profile : Fin s.pairs→Cell s.digit) : Inputs s where
  need i := word s.digit ((((packs u s.bins B key)[i.val]?).map (amount (countAt u s.bins))).getD 0)
  cap b := word s.digit (thickBins u key b.val).length
  thin i j := word s.digit (triple u (thinStream u s.bins key) i.val j)
  thick i j := word s.digit (triple u (thickStream u s.bins key) i.val j)
  profile := profile

def descriptor (s : Shape) (B key : ℕ) (z : Cell (digit*fields r D p)) : Cell s.inputBits :=
  encodeInput (inputs s B key (decodePanel z) (fun _=>0))

@[simp] theorem descriptor_fields (s : Shape) (B key : ℕ) (u : Panel r D p digit) :
    decodeInput s (descriptor s B key (encodePanel u))=inputs s B key u (fun _=>0) := by
  simp only [descriptor,decode_encode_panel,decode_encode]

theorem thin_flatten (u : Panel r D p digit) (bins B key : ℕ) :
    ((packs u bins B key).flatMap fun part=>part.flatMap (inBlock u bins))=thinStream u bins key := by
  have eqn := List.flatMap_assoc (l:=packs u bins B key) (f:=id) (g:=inBlock u bins)
  simpa only [List.flatMap_id,id_eq,packs,thinPacks_flatten,thinStream] using eqn.symm

theorem local_amount (u : Panel r D p digit) (bins : ℕ) (xs : List (Fin r)) :
    amount (countAt u bins) xs=(xs.flatMap (inBlock u bins)).length := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    rw [List.flatMap_cons,List.length_append]
    change (inBlock u bins x).length + amount (countAt u bins) xs = _
    rw [ih]

theorem triple_at (u : Panel r D p digit) (xs : List (Port r p)) (i : Fin xs.length) (j : Fin 3) :
    triple u xs i.val j=details u (xs.get i) j := by simp [triple]

theorem at_bin_mem (u : Panel r D p digit) (x : Fin r) (i : Fin p) (b : ℕ) :
    (x,i)∈atBin u x b ↔ ∃v,peer u x i=some v ∧ bin u v x=b := by
  cases h : peer u x i <;> simp [atBin,h]

theorem slots_ordered (u : Panel r D p digit) (x : Fin r) (b : ℕ) :
    (atBin u x b).Pairwise (fun a c=>a.2<c.2) := by
  rw [atBin,List.pairwise_map]
  apply List.Pairwise.filter
  rw [List.finRange]
  exact List.pairwise_ofFn.mpr (fun _ _ h=>h)

theorem sites_empty (u : Panel r D p digit) (key : ℕ) (off : ∀x,u.winner x≠0→leaf (u.winner x).val≠key) (shade : Bool) :
    sites u key shade=[] := by
  apply List.eq_nil_iff_forall_not_mem.mpr
  intro x hx
  have hit := List.mem_filter.mp hx
  have live : u.winner x≠0 ∧ leaf (u.winner x).val=key ∧ decide (thick (u.winner x).val)=shade := of_decide_eq_true hit.2
  exact off x live.1 live.2.1

theorem vacant (s : Shape) (B key : ℕ) (u : Panel r D p digit)
    (off : ∀x,u.winner x≠0→leaf (u.winner x).val≠key) :
    inputs s B key u (fun _=>0)=⟨fun _=>0,fun _=>0,fun _ _=>0,fun _ _=>0,fun _=>0⟩ := by
  have empty := sites_empty u key off
  simp [inputs,packs,thickBins,thinStream,thickStream,empty,thinPacks,word,triple]

end
end Hierarchy.DescentPacking.PackedMatch.Local

end OAI
