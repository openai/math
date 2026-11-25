import OAI.Hierarchy.DescentColonyScanLeaves
import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.ProtocolRAMSchedule

namespace OAI
/-! # Emitting the winning colony's masked outgoing slabs in original block order -/

namespace Hierarchy.DescentColonies.WinningSlabs
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped BigOperators Fin.CommRing Classical
variable {k H w : ℕ}

/-- Complete public directory, ordered first by depth and then interval number. -/
def keys : ℕ → List (ℕ × ℕ)
  | 0 => [(0,0)]
  | k+1 => keys k ++ (List.range (2^(k+1))).map (fun q => (k+1,q))

theorem mem_keys (k d q : ℕ) : (d,q)∈keys k ↔ d≤k ∧ q<2^d := by
  induction k with
  | zero =>
    constructor
    · intro h
      have e : (d,q)=(0,0) := List.mem_singleton.mp h
      have a : d=0 := congrArg Prod.fst e
      have b : q=0 := congrArg Prod.snd e
      simp [a,b]
    · rintro ⟨lo,hi⟩
      have a : d=0 := by omega
      subst d
      have b : q=0 := by simpa using hi
      simp [keys,b]
  | succ k ih =>
    simp only [keys,List.mem_append,List.mem_map,List.mem_range,Prod.mk.injEq,ih]
    constructor
    · rintro (old | ⟨j,h,rfl,rfl⟩)
      · exact ⟨old.1.trans (Nat.le_succ _),old.2⟩
      · exact ⟨le_rfl,h⟩
    · rintro ⟨lo,hi⟩
      by_cases last : d=k+1
      · subst d;exact Or.inr ⟨q,hi,rfl,rfl⟩
      · exact Or.inl ⟨by omega,hi⟩

theorem keys_nodup (k : ℕ) : (keys k).Nodup := by
  induction k with
  | zero => simp [keys]
  | succ k ih =>
    apply List.nodup_append'.mpr
    refine ⟨ih,(List.nodup_range).map (fun _ _ e => congrArg Prod.snd e),?_⟩
    apply List.disjoint_left.mpr
    rintro ⟨d,q⟩ old new
    obtain ⟨j,h,e⟩ := List.mem_map.mp new
    have eqn : k+1=d := congrArg Prod.fst e
    have earlier := ((mem_keys k d q).mp old).1
    omega

theorem keys_count (k : ℕ) : (keys k).length+1=2*2^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp only [keys,List.length_append,List.length_map,List.length_range,pow_succ];omega

def keyName (k i : ℕ) : ℕ × ℕ := if h : i<(keys k).length then (keys k)[i] else (0,0)

theorem name_valid (i : Fin (keys k).length) : (keyName k i.val).1≤k ∧ (keyName k i.val).2<2^(keyName k i.val).1 := by
  have h : keyName k i.val∈keys k := by simp [keyName,i.isLt]
  exact (mem_keys ..).mp h

theorem name_injective : Function.Injective (fun i : Fin (keys k).length => keyName k i.val) := by
  intro i j e
  apply List.nodup_iff_injective_get.mp (keys_nodup k)
  simpa only [List.get_eq_getElem,keyName,dite_eq_left i.isLt,dite_eq_left j.isLt] using e

/-- The current block index is the native scan's row register. Every visited
level loads that index from its own previously published flag bank. -/
private def walk (flag : Fin k → ℕ) (wanted : ℕ) : ℕ → ℕ → Expr
  | 0,z => .lit (decide (z=wanted)).toNat
  | n+1,z => if h : z<k then .branch .eq (.lookup ⟨flag ⟨z,h⟩,k⟩ .row) (.lit 0)
      (.lit (decide (z=wanted)).toNat) (walk flag wanted n (z+1)) else .lit 0

private theorem eval_walk (flag : Fin k→ℕ) (wanted : ℕ) (get : ℕ→Bool) (m : Memory w) (x : Block k)
    (widthRoom : 2^k<2^w) (read : ∀ z : Fin k,m (flag z+x.val)=((get z.val).toNat:Word w))
    (n z : ℕ) (hz : z+n≤k) :
    (walk flag wanted n z).eval m (x.val : Word w) = ((decide ((Scan.seek get n z).1=wanted)).toNat : Word w) := by
  have wide : 1<2^w := (show 1≤2^k from Nat.two_pow_pos k).trans_lt widthRoom
  have one : (1:Word w)≠0 := by
    intro eqn
    have e := congrArg Fin.val eqn
    simp [Nat.mod_eq_of_lt wide] at e
  induction n generalizing z with
  | zero => rfl
  | succ n ih =>
    have live : z<k := by omega
    have r := read ⟨z,live⟩
    have next := ih (z+1) (by omega)
    cases h : get z <;> simp [walk,live,Expr.eval,Comparison.test,Bank.read,Bank.size,
      Fin.val_cast_of_lt (x.isLt.trans widthRoom),Nat.mod_eq_of_lt x.isLt,r,h,one,Scan.seek,next]

private theorem fits_walk (flag : Fin k→ℕ) (wanted n z w out : ℕ)
    (fits : ∀ j : Fin k,(Bank.mk (flag j) k).Fits w out) : (walk flag wanted n z).Fits w out := by
  induction n generalizing z with
  | zero => trivial
  | succ n ih =>
    unfold walk
    split
    · exact ⟨⟨fits _,trivial⟩,trivial,trivial,ih _⟩
    · trivial

private theorem work_walk (flag : Fin k→ℕ) (wanted n z : ℕ) : (walk flag wanted n z).work≤1+n*10 := by
  induction n generalizing z with
  | zero => simp [walk,Expr.work]
  | succ n ih =>
    have next := ih (z+1)
    unfold walk
    split <;> simp only [Expr.work,Nat.succ_mul] <;> omega

/-- Unsigned comparisons restrict the numeric row to the half-open dyadic
interval. No layout-dependent grouped addresses are instruction literals. -/
def mask (flag : Fin k→ℕ) (d q : ℕ) : Expr :=
  .branch .lt .row (.lit (q*width k d)) (.lit 0)
    (.branch .lt .row (.lit ((q+1)*width k d)) (walk flag d k 0) (.lit 0))

def slab (flag : Fin k→ℕ) (amount d q : ℕ) : Expr :=
  .branch .eq (mask flag d q) (.lit 0) (.lit 0) (.lookup ⟨amount,k⟩ .row)

def member (rows : Scan.Buffer (Fin H) k) (v : Fin H) (d q : ℕ) (x : Block k) :=
  Scan.leafDepth rows v x=d ∧ group d x=q

noncomputable def filtered (rows : Scan.Buffer (Fin H) k) (v : Fin H) (outgoing : Block k→ℕ)
    (name : ℕ×ℕ) (x : Block k) : ℕ := by
  classical
  exact if member rows v name.1 name.2 x then outgoing x else 0

private theorem interval_spec (x : Block k) (d q : ℕ) :
    group d x=q ↔ q*width k d≤x.val ∧ x.val<(q+1)*width k d := by
  have pos : 0<width k d := Nat.two_pow_pos _
  rw [←Nat.le_div_iff_mul_le pos,←Nat.div_lt_iff_lt_mul pos]
  unfold group
  omega

theorem mask_eval (flag : Fin k→ℕ) (rows : Scan.Buffer (Fin H) k) (v : Fin H) (m : Memory w)
    (widthRoom : 2^k<2^w)
    (read : ∀ z : Fin k, ∀ x : Block k, m (flag z+x.val)=((Scan.lookup rows z.val v x).toNat:Word w))
    (d q : ℕ) (hd : d≤k) (hq : q<2^d) (x : Block k) :
    (mask flag d q).eval m (x.val : Word w)=if member rows v d q x then 1 else 0 := by
  classical
  have endBound : (q+1)*width k d≤2^k := calc
    _ ≤ 2^d*2^(k-d) := Nat.mul_le_mul_right _ hq
    _ = _ := by rw [←pow_add,show d+(k-d)=k by omega]
  have upper := endBound.trans_lt widthRoom
  have lower : q*width k d<2^w := (Nat.mul_le_mul_right _ (Nat.le_succ q)).trans_lt upper
  have depth := eval_walk flag d (fun z => Scan.lookup rows z v x) m x widthRoom (fun z=>read z x) k 0 (by omega)
  change (walk flag d k 0).eval m (x.val : Word w) = ((decide (Scan.leafDepth rows v x=d)).toNat : Word w) at depth
  simp only [mask,Expr.eval,Comparison.test,decide_eq_true_eq,Fin.lt_def,Fin.val_cast_of_lt (x.isLt.trans widthRoom),
    Fin.val_cast_of_lt lower,Fin.val_cast_of_lt upper,depth,member,interval_spec]
  by_cases lo : x.val<q*width k d
  · simp [lo,Nat.not_le_of_gt lo]
  · have lowerBound : q*width k d≤x.val := Nat.le_of_not_gt lo
    by_cases chosen : Scan.leafDepth rows v x=d <;> by_cases hi : x.val<(q+1)*width k d <;>
      simp [chosen,lo,lowerBound,hi]

theorem slab_eval (flag : Fin k→ℕ) (amount : ℕ) (rows : Scan.Buffer (Fin H) k) (v : Fin H)
    (outgoing : Block k→ℕ) (m : Memory w) (widthRoom : 2^k<2^w)
    (read : ∀ z : Fin k, ∀ x : Block k, m (flag z+x.val)=((Scan.lookup rows z.val v x).toNat:Word w))
    (load : ∀ x : Block k,m (amount+x.val)=(outgoing x:Word w)) (d q : ℕ) (hd : d≤k) (hq : q<2^d) (x : Block k) :
    (slab flag amount d q).eval m (x.val : Word w)=(filtered rows v outgoing (d,q) x:Word w) := by
  classical
  have wide : 1<2^w := (show 1≤2^k from Nat.two_pow_pos k).trans_lt widthRoom
  have one : (1:Word w)≠0 := by
    intro h
    have e := congrArg Fin.val h
    simp [Nat.mod_eq_of_lt wide] at e
  by_cases test : member rows v d q x <;>
    simp [slab,Expr.eval,Comparison.test,mask_eval flag rows v m widthRoom read d q hd hq x,test,
      Bank.read,Bank.size,Fin.val_cast_of_lt (x.isLt.trans widthRoom),Nat.mod_eq_of_lt x.isLt,
      filtered,load,one]

theorem slab_fits (flag : Fin k→ℕ) (amount d q w out : ℕ)
    (fs : ∀z,(Bank.mk (flag z) k).Fits w out) (a : (Bank.mk amount k).Fits w out) :
    (slab flag amount d q).Fits w out :=
  ⟨⟨trivial,trivial,trivial,⟨trivial,trivial,fits_walk _ _ _ _ _ _ fs,trivial⟩⟩,
    trivial,trivial,⟨a,trivial⟩⟩

theorem slab_work (flag : Fin k→ℕ) (amount d q : ℕ) : (slab flag amount d q).work≤21+10*k := by
  have h := work_walk flag d k 0
  dsimp only [slab,mask,Expr.work]
  omega

def ptr (k base i : ℕ) := base+i*2^k

def finish (k base : ℕ) := ptr k base (keys k).length

def table {C : ℕ} (k base : ℕ) (f : Fin C→Expr) : (n : ℕ) → n≤C → List Pass
  | 0,_ => []
  | n+1,h => table k base f n (by omega) ++ [⟨ptr k base n,2^k,f ⟨n,by omega⟩⟩]

theorem table_mem {C : ℕ} (base : ℕ) (f : Fin C→Expr) (n : ℕ) (h : n≤C) {p : Pass}
    (hp : p∈table k base f n h) : ∃ j : Fin C,j.val<n ∧ p=⟨ptr k base j.val,2^k,f j⟩ := by
  induction n with
  | zero => simp [table] at hp
  | succ n ih =>
    simp only [table,List.mem_append,List.mem_singleton] at hp
    rcases hp with hp|hp
    · obtain ⟨j,hj,e⟩ := ih (by omega) hp
      exact ⟨j,by omega,e⟩
    · exact ⟨⟨n,by omega⟩,Nat.lt_succ_self _,hp⟩

theorem table_length {C : ℕ} (k base : ℕ) (f : Fin C→Expr) (n : ℕ) (h : n≤C) :
    (table k base f n h).length=n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [table,ih]

private theorem ptr_end {base a b : ℕ} (h : a<b) : ptr k base a+2^k≤ptr k base b := by
  simpa only [ptr,Nat.succ_mul,Nat.add_assoc] using Nat.add_le_add_left (Nat.mul_le_mul_right (2^k) h) base

theorem table_below {C : ℕ} (k base : ℕ) (f : Fin C→Expr) (n : ℕ) (h : n≤C)
    (m : Memory w) {a : ℕ} (early : a<base) : result (table k base f n h) m a=m a := by
  apply result_below
  intro p hp
  obtain ⟨j,_,rfl⟩ := table_mem base f n h hp
  exact early.trans_le (Nat.le_add_right _ _)

theorem table_run {C : ℕ} (k base : ℕ) (f : Fin C→Expr) (m : Memory w)
    (fits : ∀ j,(f j).Fits w base) (room : ptr k base C<2^w) :
    (ProtocolRAM.program w (table k base f C le_rfl)).Exec m
      (result (table k base f C le_rfl) m) (clock (table k base f C le_rfl)) := by
  apply program_exec
  intro p hp
  obtain ⟨j,_,rfl⟩ := table_mem base f C le_rfl hp
  exact ⟨ProtocolRAMGeneratedWrite.fits_mono _ (Nat.le_add_right _ _) (fits j),(ptr_end j.isLt).trans_lt room⟩

theorem table_read {C : ℕ} (k base : ℕ) (f : Fin C→Expr) (m : Memory w)
    (fits : ∀ j,(f j).Fits w base) (n : ℕ) (h : n≤C) (j : Fin C) (hj : j.val<n) (x : Block k) :
    result (table k base f n h) m (ptr k base j.val+x.val)=(f j).eval m (x.val:Word w) := by
  induction n with
  | zero => omega
  | succ n ih =>
    let t : Fin C := ⟨n,by omega⟩
    let old := result (table k base f n (by omega)) m
    rw [table,result_append]
    change image (ptr k base n) (2^k) (f t) old (ptr k base j.val+x.val)=_
    by_cases last : j.val=n
    · have eqn : j=t := Fin.ext last
      calc
        _ = image (ptr k base n) (2^k) (f t) old (ptr k base n+x.val) :=
          congrArg (fun z => image (ptr k base n) (2^k) (f t) old (ptr k base z+x.val)) last
        _ = (f t).eval old (x.val:Word w) := ProtocolRAMGeneratedWrite.read_image _ _ _ _ x
        _ = (f t).eval m (x.val:Word w) :=
          eval_below (f t) _ m old (fits t) (fun a ha=>table_below k base f n _ m ha)
        _ = _ := congrArg (fun idx => (f idx).eval m (x.val:Word w)) eqn.symm
    · have early : j.val<n := by omega
      have below : ptr k base j.val+x.val<ptr k base n :=
        (Nat.add_lt_add_left x.isLt _).trans_le (ptr_end early)
      rw [ProtocolRAMGeneratedWrite.frame_image _ _ _ _ _ (Or.inl below)]
      exact ih (by omega) early

private def term (flag : Fin k→ℕ) (amount : ℕ) (i : Fin (keys k).length) : Expr :=
  slab flag amount (keyName k i.val).1 (keyName k i.val).2

def passes (k base : ℕ) (flag : Fin k→ℕ) (amount : ℕ) :=
  table k base (term flag amount) (keys k).length le_rfl

theorem run (k base : ℕ) (flag : Fin k→ℕ) (amount : ℕ) (m : Memory w)
    (fs : ∀z,(Bank.mk (flag z) k).Fits w base) (a : (Bank.mk amount k).Fits w base)
    (room : finish k base<2^w) :
    (ProtocolRAM.program w (passes k base flag amount)).Exec m (result (passes k base flag amount) m) (clock (passes k base flag amount)) :=
  table_run k base _ _ (fun _ => slab_fits _ _ _ _ _ _ fs a) room

theorem published (k base : ℕ) (flag : Fin k→ℕ) (amount : ℕ) (rows : Scan.Buffer (Fin H) k) (v : Fin H)
    (outgoing : Block k→ℕ) (m : Memory w)
    (fs : ∀z,(Bank.mk (flag z) k).Fits w base) (a : (Bank.mk amount k).Fits w base)
    (read : ∀ z : Fin k, ∀ x : Block k, m (flag z+x.val)=((Scan.lookup rows z.val v x).toNat:Word w))
    (load : ∀ x : Block k,m (amount+x.val)=(outgoing x:Word w)) (j : Fin (keys k).length) (x : Block k) :
    result (passes k base flag amount) m (ptr k base j.val+x.val)=(filtered rows v outgoing (keyName k j.val) x:Word w) :=
  (table_read k base (term flag amount) m (fun _ => slab_fits _ _ _ _ _ _ fs a) _ le_rfl j j.isLt x).trans
    (slab_eval flag amount rows v outgoing m a.2.1 read load _ _ (name_valid j).1 (name_valid j).2 x)

/-- Enumerate selected original block groups, sites, and public interval names on
one tape. -/
def directory (G H k : ℕ) : ((Fin G × Fin H) × Fin (keys k).length) ≃ Fin ((G*H)*(keys k).length) :=
  (Equiv.prodCongr finProdFinEquiv (Equiv.refl _)).trans finProdFinEquiv

variable {G : ℕ}

abbrev Slot (G H k : ℕ) := Fin ((G*H)*(keys k).length)

def worldTerm (flag : Fin G→Fin H→Fin k→ℕ) (amount : Fin G→Fin H→ℕ) (i : Slot G H k) : Expr :=
  let j := (directory G H k).symm i
  term (flag j.1.1 j.1.2) (amount j.1.1 j.1.2) j.2

def worldPasses (k base : ℕ) (flag : Fin G→Fin H→Fin k→ℕ) (amount : Fin G→Fin H→ℕ) :=
  table k base (worldTerm flag amount) ((G*H)*(keys k).length) le_rfl

def worldEnd (G H k base : ℕ) := ptr k base ((G*H)*(keys k).length)

theorem slot_end (base : ℕ) (i : Slot G H k) : ptr k base i.val+2^k≤worldEnd G H k base :=
  ptr_end i.isLt

noncomputable def worldValue (rows : Fin G→Scan.Buffer (Fin H) k) (outgoing : Fin G→Fin H→Block k→ℕ)
    (i : Slot G H k) (x : Block k) :=
  let j := (directory G H k).symm i
  filtered (rows j.1.1) j.1.2 (outgoing j.1.1 j.1.2) (keyName k j.2.val) x

theorem world_run (k base : ℕ) (flag : Fin G→Fin H→Fin k→ℕ) (amount : Fin G→Fin H→ℕ) (m : Memory w)
    (fs : ∀g v z,(Bank.mk (flag g v z) k).Fits w base) (as_ : ∀g v,(Bank.mk (amount g v) k).Fits w base)
    (room : worldEnd G H k base<2^w) :
    (ProtocolRAM.program w (worldPasses k base flag amount)).Exec m (result (worldPasses k base flag amount) m)
      (clock (worldPasses k base flag amount)) :=
  table_run k base _ m (fun _ => slab_fits _ _ _ _ _ _ (fs _ _) (as_ _ _)) room

theorem world_read (k base : ℕ) (flag : Fin G→Fin H→Fin k→ℕ) (amount : Fin G→Fin H→ℕ)
    (rows : Fin G→Scan.Buffer (Fin H) k) (outgoing : Fin G→Fin H→Block k→ℕ) (m : Memory w)
    (fs : ∀g v z,(Bank.mk (flag g v z) k).Fits w base) (as_ : ∀g v,(Bank.mk (amount g v) k).Fits w base)
    (read : ∀ g v (z : Fin k) (x : Block k), m (flag g v z+x.val)=((Scan.lookup (rows g) z.val v x).toNat:Word w))
    (load : ∀ g v (x : Block k),m (amount g v+x.val)=(outgoing g v x:Word w)) (i : Slot G H k) (x : Block k) :
    result (worldPasses k base flag amount) m (ptr k base i.val+x.val)=(worldValue rows outgoing i x:Word w) := by
  let j := (directory G H k).symm i
  apply (table_read k base (worldTerm flag amount) m (fun _=>slab_fits _ _ _ _ _ _ (fs _ _) (as_ _ _))
    _ le_rfl i i.isLt x).trans
  exact slab_eval _ _ _ _ _ _ (as_ j.1.1 j.1.2).2.1 (read _ _) (load _ _) _ _ (name_valid j.2).1 (name_valid j.2).2 x

theorem world_below (k base : ℕ) (flag : Fin G→Fin H→Fin k→ℕ) (amount : Fin G→Fin H→ℕ)
    (m : Memory w) {a : ℕ} (lo : a<base) : result (worldPasses k base flag amount) m a=m a :=
  table_below k base _ _ le_rfl m lo

theorem world_length (k base : ℕ) (flag : Fin G→Fin H→Fin k→ℕ) (amount : Fin G→Fin H→ℕ) :
    (worldPasses k base flag amount).length=(G*H)*(keys k).length := table_length ..

theorem world_pass (k base : ℕ) (flag : Fin G→Fin H→Fin k→ℕ) (amount : Fin G→Fin H→ℕ)
    {p : Pass} (hp : p∈worldPasses k base flag amount) : p.rows=2^k ∧ p.term.work≤21+10*k := by
  obtain ⟨j,_,rfl⟩ := table_mem base (worldTerm flag amount) _ le_rfl hp
  exact ⟨rfl,slab_work ..⟩

theorem world_clock (k base : ℕ) (flag : Fin G→Fin H→Fin k→ℕ) (amount : Fin G→Fin H→ℕ) :
    clock (worldPasses k base flag amount) ≤ 4+(G*H)*(keys k).length*(4+2^k*(2*(21+10*k)+4)) := by
  rw [←world_length k base flag amount]
  apply clock_le
  exact fun p hp => ⟨(world_pass k base flag amount hp).1.le,(world_pass k base flag amount hp).2⟩

noncomputable def positive (rows : Fin G→Scan.Buffer (Fin H) k) (outgoing : Fin G→Fin H→Block k→ℕ) :
    Finset (Slot G H k) := by
  classical
  exact Finset.univ.filter (fun i => ∃x,0<worldValue rows outgoing i x)

theorem off (rows : Fin G→Scan.Buffer (Fin H) k) (outgoing : Fin G→Fin H→Block k→ℕ)
    (i : Slot G H k) (absent : i∉positive rows outgoing) (x : Block k) : worldValue rows outgoing i x=0 := by
  classical
  by_contra nz
  exact absent (Finset.mem_filter.mpr ⟨Finset.mem_univ _,x,Nat.pos_of_ne_zero nz⟩)

/-- Charge each positive physical row to its reached leaf, at its own group and
site. Unoccupied directory rows carry no charge. -/
theorem world_support (rows : Fin G→Scan.Buffer (Fin H) k) (outgoing : Fin G→Fin H→Block k→ℕ) :
    (positive rows outgoing).card ≤ ∑g,∑v,(Scan.siteKeys (rows g) v).card := by
  classical
  let A := positive rows outgoing
  let W := Σ g : Fin G, Σ v : Fin H, ↥(Scan.siteKeys (rows g) v)
  let tag := fun i : A => (directory G H k).symm i.val
  have visited (i : A) : keyName k (tag i).2.val∈Scan.siteKeys (rows (tag i).1.1) (tag i).1.2 := by
    have inside : i.val∈positive rows outgoing := i.property
    obtain ⟨x,hx⟩ := (Finset.mem_filter.mp inside).2
    let d := (keyName k (tag i).2.val).1
    let q := (keyName k (tag i).2.val).2
    have hit : member (rows (tag i).1.1) (tag i).1.2 d q x := by
      by_contra fail
      change 0 < (if member (rows (tag i).1.1) (tag i).1.2 d q x then
        outgoing (tag i).1.1 (tag i).1.2 x else 0) at hx
      simp only [ite_eq_right fail,Nat.lt_irrefl] at hx
    apply Finset.mem_image.mpr
    refine ⟨x,Finset.mem_univ _,Prod.ext hit.1 ?_⟩
    exact (congrArg (fun z=>group z x) hit.1).trans hit.2
  let bill : A→W := fun i=>⟨(tag i).1.1,(tag i).1.2,⟨_,visited i⟩⟩
  have inj : Function.Injective bill := by
    intro a b e
    have sameSite : (tag a).1 = (tag b).1 := congrArg (fun s : W => (s.1,s.2.1)) e
    have sameKey : keyName k (tag a).2.val = keyName k (tag b).2.val :=
      congrArg (fun s : W => s.2.2.val) e
    apply Subtype.ext
    apply (directory G H k).symm.injective
    exact Prod.ext sameSite (name_injective sameKey)
  simpa only [A,W,Fintype.card_coe,Fintype.card_sigma] using Fintype.card_le_of_injective bill inj

theorem score_support (incoming : Fin H→List (Fin H)) (load outgoing : Fin G→Fin H→Block k→ℕ) (D cap : ℕ) :
    (positive (fun g=>Scan.build incoming (load g) D cap k) outgoing).card ≤ ∑ g,Scan.leafScore incoming (load g) D cap := by
  simpa only [Scan.leafScore_siteKeys] using world_support (fun g=>Scan.build incoming (load g) D cap k) outgoing

end Hierarchy.DescentColonies.WinningSlabs

end OAI
