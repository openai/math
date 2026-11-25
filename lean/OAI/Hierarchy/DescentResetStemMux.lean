import OAI.Hierarchy.DescentPackedPorts
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Packed actor descriptor selection from a row of public endpoint keys -/

namespace Hierarchy.DescentResetStemMux
open DescentSIMDLookup DescentPackedZip DescentPackedColony Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {K a b H G M w out : ℕ}

def gate (j : Fin K) (x : Cell a) (v : Cell b) : Cell b := if x.val=j.val+1 then v else 0

def join (x y : Cell b) : Cell b := if x=0 then y else x

/-- Public ordinal zero and out-of-range ordinals both select the zero descriptor. -/
def pick (x : Cell a) (heads : Fin K→Cell b) : Cell b :=
  if valid : 0<x.val ∧ x.val≤K then heads ⟨x.val-1,by omega⟩ else 0

theorem pick_actor (x : Cell a) (heads : Fin K→Cell b) (j : Fin K) (key : x.val=j.val+1) :
    pick x heads=heads j := by
  have range : 0<x.val ∧ x.val≤K := ⟨by omega,by have := j.isLt;omega⟩
  unfold pick
  rw [dite_eq_left range]
  exact congrArg heads (Fin.ext (by dsimp;omega))

theorem pick_absent (heads : Fin K→Cell b) : pick (0:Cell a) heads=0 := by
  simp [pick]

private def value (x : Cell a) (heads : Fin K→Cell b) : List (Fin K)→Cell b
  | [] => 0
  | j::js => join (gate j x (heads j)) (value x heads js)

private theorem value_at (x : Cell a) (v : Fin K→Cell b) (i : Fin K) (encoded : x.val=i.val+1)
    (is : List (Fin K)) : value x v is=if i∈is then v i else 0 := by
  induction is with
  | nil => simp [value]
  | cons j js ih =>
    by_cases equal : i=j
    · subst j
      by_cases empty : v i=0 <;> simp [value,gate,join,encoded,ih,empty]
    · have diff : x.val≠j.val+1 := by
        intro h
        exact equal (Fin.ext (by omega))
      simp [value,gate,join,diff,ih,equal]

private theorem value_none (x : Cell a) (v : Fin K→Cell b) (missing : ∀i : Fin K,x.val≠i.val+1)
    (is : List (Fin K)) : value x v is=0 := by
  induction is with
  | nil => rfl
  | cons j js ih => simp [value,gate,missing,join,ih]

private theorem value_all (x : Cell a) (v : Fin K→Cell b) : value x v (List.finRange K)=pick x v := by
  unfold pick
  split
  next ok =>
    let i : Fin K:=⟨x.val-1,by omega⟩
    exact (value_at x v i (by dsimp [i];omega) _).trans (ite_eq_left (List.mem_finRange i))
  next bad =>
    exact value_none x v (fun i eq=>bad ⟨by omega,by have := i.isLt;omega⟩) _

def combine (tables : Fin K→Tables) (merge : Tables) (key : Expr) (heads : Fin K→Expr) :
    List (Fin K)→Expr
  | [] => .lit 0
  | j::js => merge.read ((tables j).read key (heads j)) (combine tables merge key heads js)

def assemble (tables : Fin K→Tables) (merge : Tables) (key : Expr) (heads : Fin K→Expr) :=
  combine tables merge key heads (List.finRange K)

structure Fits (tables : Fin K→Tables) (merge : Tables) (key : Expr) (heads : Fin K→Expr)
    (a b M w out : ℕ) : Prop where
  selectors : ∀i,WordRoom (tables i) a b M w out
  combine : WordRoom merge b b M w out
  key : key.Fits w out
  heads : ∀i,(heads i).Fits w out

variable (tables : Fin K→Tables) (merge : Tables) (key : Expr) (heads : Fin K→Expr)
local notation "term" => assemble tables merge key heads
local notation "bounds" => Fits tables merge key heads a b M w out

private theorem combine_fits (fit : bounds) (is : List (Fin K)) :
    (combine tables merge key heads is).Fits w out := by
  induction is with
  | nil => trivial
  | cons i is ih => exact fit.combine.safe _ _ ((fit.selectors i).safe _ _ fit.key (fit.heads i)) ih

theorem assemble_fits (fit : bounds) : (term).Fits w out :=
  combine_fits tables merge key heads fit _

structure Loaded (tables : Fin K→Tables) (merge : Tables) (key : Expr) (heads : Fin K→Expr)
    (x : Fin H→Fin G→Cell a) (v : Fin K→Fin H→Cell b) (M : ℕ) (m : Memory w) : Prop where
  selectors : ∀i,Static (tables i) (gate (a:=a) (b:=b) i) M m
  combine : Static merge (join (b:=b)) M m
  key : Source key x M m
  heads : ∀i,Source (heads i) (fun h (_ : Fin G)=>v i h) M m

private theorem read_lanes_list (fit : bounds) (x : Fin H→Fin G→Cell a) (v : Fin K→Fin H→Fin G→Cell b)
    (m : Memory w) (selectors : ∀i,Static (tables i) (gate (a:=a) (b:=b) i) M m)
    (mergeRead : Static merge (join (b:=b)) M m) (keyRead : Source key x M m)
    (headsRead : ∀i,Source (heads i) (v i) M m) (is : List (Fin K)) :
    Source (combine tables merge key heads is) (fun h g=>value (x h g) (fun i=>v i h g) is) M m := by
  induction is with
  | nil =>
    intro p
    change 0=(((finFunctionFinEquiv (fun i : Fin M=>if _ : p.2.val*M+i.val<G then (0:Cell b) else 0)).val:ℕ):Word w)
    simp []
  | cons i is ih =>
    have mask := read_data (tables i) key (heads i) out ((fit.selectors i).issue _ _ fit.key (fit.heads i))
      (gate (a:=a) (b:=b) i) (by simp [gate]) m (selectors i) _ _ keyRead (headsRead i)
    exact read_data merge _ _ out (fit.combine.issue _ _
      ((fit.selectors i).safe _ _ fit.key (fit.heads i)) (combine_fits tables merge key heads fit is))
      join (by simp [join]) m mergeRead _ _ mask ih

/-- Each group on a physical row may hold a different value at the same
candidate; the public selector and merge tables apply independently to each lane. -/
theorem read_lanes (fit : bounds) (x : Fin H→Fin G→Cell a) (v : Fin K→Fin H→Fin G→Cell b)
    (m : Memory w) (selectors : ∀i,Static (tables i) (gate (a:=a) (b:=b) i) M m)
    (mergeRead : Static merge (join (b:=b)) M m) (keyRead : Source key x M m)
    (headsRead : ∀i,Source (heads i) (v i) M m) :
    Source term (fun h g=>pick (x h g) (fun i=>v i h g)) M m := by
  simpa only [assemble,value_all] using
    read_lanes_list tables merge key heads fit x v m selectors mergeRead keyRead headsRead (List.finRange K)

theorem read (fit : bounds) (x : Fin H→Fin G→Cell a) (v : Fin K→Fin H→Cell b)
    (m : Memory w) (loaded : Loaded tables merge key heads x v M m) :
    Source term (fun h g=>pick (x h g) (fun i=>v i h)) M m :=
  read_lanes tables merge key heads fit x (fun i h _=>v i h) m loaded.selectors loaded.combine loaded.key loaded.heads

theorem combine_work (is : List (Fin K)) : (combine tables merge key heads is).work=
    1+(is.map (fun j=>key.work+(heads j).work+22)).sum := by
  induction is with
  | nil => rfl
  | cons j js ih =>
    simp only [combine,DescentPackedZip.work,ih,List.map_cons,List.sum_cons]
    omega

theorem work : (term).work=1+((List.finRange K).map (fun j=>key.work+(heads j).work+22)).sum :=
  combine_work tables merge key heads _

theorem work_le (U : ℕ) (cheap : ∀i,(heads i).work≤U) : (term).work≤1+K*(key.work+U+22) := by
  have bound (slots : List (Fin K)) :
      (slots.map (fun j=>key.work+(heads j).work+22)).sum ≤ slots.length*(key.work+U+22) := by
    induction slots with
    | nil => simp
    | cons j js ih =>
      simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.succ_mul]
      have h:=cheap j
      omega
  rw [work]
  exact Nat.add_le_add_left (by simpa using bound (List.finRange K)) 1

def program (w H G M out : ℕ) := scan w out (H*chunks G M) term
def ticks (H G M : ℕ) := 4+(H*chunks G M)*(2*(term).work+4)

theorem run (fit : bounds) (x : Fin H→Fin G→Cell a) (v : Fin K→Fin H→Cell b)
    (m : Memory w) (loaded : Loaded tables merge key heads x v M m) (room : out+H*chunks G M<2^w) :
    let last:=image out (H*chunks G M) term m
    (program tables merge key heads w H G M out).Exec m last (ticks tables merge key heads H G M) ∧
      (∀p : Row H G M,last (out+(row H G M p).val)=
        ((data (fun h g=>pick (x h g) (fun j=>v j h)) p).val:Word w)) ∧
      (∀u,u<out ∨ out+H*chunks G M≤u→last u=m u) ∧
      CheapCode (program tables merge key heads w H G M out) := by
  intro last
  refine ⟨scan_exec _ _ _ _ (assemble_fits tables merge key heads fit) room,?_,
    fun u hu=>ProtocolRAMGeneratedWrite.frame_image out (H*chunks G M) term m u hu,
    @scan_cheap w out (H*chunks G M) term⟩
  intro p
  exact (ProtocolRAMGeneratedWrite.read_image out (H*chunks G M) term m (row H G M p)).trans
    (read tables merge key heads fit x v m loaded p)

theorem published (dst : Bank) (fit : Fits tables merge key heads a b M w dst.base)
    (x : Fin H→Fin G→Cell a) (v : Fin K→Fin H→Cell b) (m : Memory w)
    (loaded : Loaded tables merge key heads x v M m) (space : H*chunks G M≤dst.size)
    (room : dst.base+dst.size<2^w) :
    Source (.lookup dst .row) (fun h g=>pick (x h g) (fun i=>v i h)) M
      (image dst.base (H*chunks G M) term m) := by
  have receipt:=run tables merge key heads fit x v m loaded ((Nat.add_le_add_left space _).trans_lt room)
  exact source_column dst (dst.base+dst.size) ⟨Nat.two_pow_pos _,by omega,le_rfl⟩ _ _ space receipt.2.1


end
end Hierarchy.DescentResetStemMux

end OAI
