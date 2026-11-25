import OAI.Hierarchy.DescentColonySplitRAM
import OAI.Hierarchy.ProtocolRAMSchedule

namespace OAI
/-! # Executing all descending colony layers in disjoint word banks -/

namespace Hierarchy.DescentColonies.LayerRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Fin.CommRing

variable {H w : ℕ}

/-- The layer for depth `k-1` comes first. Each site owns one whole row. -/
def address (k base d : ℕ) (v : Fin H) := base + ((k-1-d)*H+v.val)*2^k

structure Layout (H : ℕ) where
  k : ℕ
  base : ℕ
  incoming : Fin H → List (Fin H)
  loadBase : Fin H → ℕ
  D : ℕ
  cap : ℕ

namespace Layout
variable (c : Layout H)

def fence (s : ℕ) := c.base + s*H*2^c.k

def bank (s : ℕ) (v : Fin H) := c.base + (s*H+v.val)*2^c.k

def previous (s z : ℕ) (u : Fin H) : Option ℕ :=
  if z<c.k ∧ c.k-1-z<s then some (address c.k c.base z u) else none

def pass (s : ℕ) (v : Fin H) : Pass :=
  ⟨c.bank s v, 2^c.k, SplitRAM.expr c.k c.incoming c.loadBase (c.previous s) c.D c.cap (c.k-1-s) v⟩

/-- First `i` sites of the current depth, in physical address order. -/
def sites (c : Layout H) (s : ℕ) : (i : ℕ) → i ≤ H → List Pass
  | 0, _ => []
  | i+1, hi => sites c s i (by omega) ++ [c.pass s ⟨i,by omega⟩]

def stages (c : Layout H) : ℕ → List Pass
  | 0 => []
  | s+1 => stages c s ++ c.sites s H le_rfl

private theorem fence_mono {s t : ℕ} (h : s≤t) : c.fence s ≤ c.fence t := by
  unfold fence
  gcongr

private theorem fence_bank (s : ℕ) (v : Fin H) : c.fence s ≤ c.bank s v := by
  unfold fence bank
  gcongr; omega

private theorem bank_end (s : ℕ) (v : Fin H) : c.bank s v+2^c.k ≤ c.fence (s+1) := by
  have ordinal : s*H+v.val+1 ≤ (s+1)*H := by rw [Nat.succ_mul]; omega
  have step := Nat.mul_le_mul_right (2^c.k) ordinal
  calc
    c.bank s v+2^c.k = c.base+(s*H+v.val+1)*2^c.k := by rw [bank,Nat.succ_mul,Nat.add_assoc]
    _ ≤ c.fence (s+1) := Nat.add_le_add_left step c.base

private theorem bank_before (s : ℕ) {v u : Fin H} (lt : v.val<u.val) :
    c.bank s v + 2^c.k ≤ c.bank s u := by
  have h := Nat.mul_le_mul_right (2^c.k) (show s*H+v.val+1 ≤ s*H+u.val by omega)
  calc
    c.bank s v+2^c.k = c.base+(s*H+v.val+1)*2^c.k := by rw [bank,Nat.succ_mul,Nat.add_assoc]
    _ ≤ c.bank s u := Nat.add_le_add_left h c.base

private theorem previous_end {s z : ℕ} {u : Fin H} {b : ℕ} (hit : c.previous s z u = some b) :
    b + 2^c.k ≤ c.fence s := by
  unfold previous at hit
  split at hit
  next good =>
    have eq := Option.some.inj hit
    subst b
    exact (c.bank_end (c.k-1-z) u).trans (c.fence_mono good.2)
  next => contradiction

private theorem sites_mem {s i : ℕ} {hi : i≤H} {p : Pass} (hp : p ∈ c.sites s i hi) :
    ∃ v : Fin H, p = c.pass s v := by
  induction i with
  | zero => simp [sites] at hp
  | succ i ih =>
    simp only [sites,List.mem_append,List.mem_singleton] at hp
    rcases hp with h | h
    · exact ih h
    · exact ⟨_,h⟩

private theorem stages_mem {s : ℕ} {p : Pass} (hp : p ∈ c.stages s) :
    ∃ t < s, ∃ v : Fin H, p = c.pass t v := by
  induction s with
  | zero => simp [stages] at hp
  | succ s ih =>
    rw [stages,List.mem_append] at hp
    rcases hp with h | h
    · obtain ⟨t,lt,v,e⟩ := ih h
      exact ⟨t,by omega,v,e⟩
    · exact ⟨s,by omega,c.sites_mem h⟩

private theorem sites_below {s i : ℕ} (hi : i≤H) (m : Memory w) {a : ℕ} (lo : a<c.fence s) :
    result (c.sites s i hi) m a = m a := by
  apply result_below
  intro p hp
  obtain ⟨v,rfl⟩ := c.sites_mem hp
  exact lo.trans_le (c.fence_bank s v)

private theorem stages_below {s : ℕ} (m : Memory w) {a : ℕ} (lo : a<c.base) :
    result (c.stages s) m a = m a := by
  apply result_below
  intro p hp
  obtain ⟨t,_,v,rfl⟩ := c.stages_mem hp
  exact lo.trans_le (Nat.le_add_right _ _)

private theorem pass_fits {s : ℕ} (hs : s<c.k) (v : Fin H)
    (old : ∀ u, c.loadBase u+2^c.k ≤ c.base) (room : c.fence c.k < 2^w) : (c.pass s v).Fits w := by
  have endRoom := ((c.bank_end s v).trans (c.fence_mono hs)).trans_lt room
  have front := c.fence_bank s v
  have baseLo : c.base ≤ c.fence s := Nat.le_add_right _ _
  have wide : 2^c.k < 2^w := by omega
  exact ⟨SplitRAM.fits v ⟨Nat.two_pow_pos _,wide,(old v).trans (baseLo.trans front)⟩
    (fun _ _ _ h=>⟨Nat.two_pow_pos _,wide,(c.previous_end h).trans front⟩),endRoom⟩

private theorem sites_length (s i : ℕ) (hi : i≤H) : (c.sites s i hi).length=i := by
  induction i with
  | zero => rfl
  | succ i ih => simp [sites,ih]

private theorem stages_length (s : ℕ) : (c.stages s).length=s*H := by
  induction s with
  | zero => simp [stages]
  | succ s ih => simp [stages,ih,sites_length,Nat.succ_mul]

/-- Every active read address is below the current layer's first word. -/
private theorem previous_frame {m m' : Memory w} {s : ℕ}
    (keep : ∀ a<c.fence s,m' a=m a) (z : ℕ) (v : Fin H) (x : Block c.k) :
    SplitRAM.flagWord (c.previous s z v) m' x = SplitRAM.flagWord (c.previous s z v) m x := by
  cases eqn : c.previous s z v with
  | none => rfl
  | some b =>
    change m' (b+x.val) = m (b+x.val)
    exact keep _ ((Nat.add_lt_add_left x.isLt b).trans_le (c.previous_end eqn))

private theorem sites_read (s : ℕ) (hs : s<c.k) (m : Memory w)
    (load : Fin H → Block c.k → ℕ) (get : ℕ → Fin H → Block c.k → Bool)
    (old : ∀ u, c.loadBase u+2^c.k ≤ c.base) (room : c.fence c.k < 2^w) (capRoom : c.cap<2^w)
    (weights : ∀ v (x : Block c.k), m (c.loadBase v+x.val) = (load v x : Word w))
    (flags : ∀ z v x, SplitRAM.flagWord (c.previous s z v) m x = ((get z v x).toNat : Word w))
    (sumRoom : ∀ v x, (Scan.readWeights load (c.k-1-s) v x).sum < 2^w)
    (i : ℕ) (hi : i≤H) (v : Fin H) (hv : v.val < i) (x : Block c.k) :
    result (c.sites s i hi) m (c.bank s v+x.val) =
      ((Scan.rowValue c.incoming load get c.D c.cap (c.k-1-s) v x).toNat : Word w) := by
  induction i with
  | zero => omega
  | succ i ih =>
    let u : Fin H := ⟨i,by omega⟩
    let mem := result (c.sites s i (by omega)) m
    have keep (a : ℕ) (lo : a<c.fence s) : mem a=m a := c.sites_below (by omega) m lo
    rw [sites,result_append]
    change (c.pass s u).apply mem (c.bank s v+x.val) = _
    by_cases last : v.val=i
    · have same : v=u := Fin.ext last
      calc
        _ = (c.pass s u).apply mem (c.bank s u+x.val) :=
          congrArg (fun t => (c.pass s u).apply mem (c.bank s t+x.val)) same
        _ = ((Scan.rowValue c.incoming load get c.D c.cap (c.k-1-s) u x).toNat : Word w) := by
          refine SplitRAM.published u mem load get (((c.bank_end s u).trans (c.fence_mono hs)).trans_lt room)
            capRoom ?_ ?_ x (sumRoom u x)
          · intro y
            exact (keep _ (((Nat.add_lt_add_left y.isLt _).trans_le (old u)).trans_le (Nat.le_add_right _ _))).trans
              (weights u y)
          · intro z t y
            exact (c.previous_frame keep z t y).trans (flags z t y)
        _ = _ := congrArg (fun t => ((Scan.rowValue c.incoming load get c.D c.cap (c.k-1-s) t x).toNat : Word w)) same.symm
    · have prior : v.val < i := by omega
      have early : c.bank s v+x.val < c.bank s u :=
        (Nat.add_lt_add_left x.isLt _).trans_le (c.bank_before s (u:=u) prior)
      simpa [Pass.apply,pass,image,fillSegment,not_le.mpr early,mem] using ih (by omega) prior

/-- Each stage interprets all active flag rows in the actual result tape, and
absent rows as zero, exactly as the descending table constructor does. -/
private theorem stage_read (load : Fin H → Block c.k → ℕ) (m : Memory w)
    (old : ∀ v, c.loadBase v+2^c.k ≤ c.base) (room : c.fence c.k < 2^w) (capRoom : c.cap<2^w)
    (weights : ∀ v (x : Block c.k), m (c.loadBase v+x.val)=(load v x : Word w))
    (sumRoom : ∀ d<c.k, ∀ v x, (Scan.readWeights load d v x).sum < 2^w)
    (s : ℕ) (hs : s≤c.k) (z : ℕ) (v : Fin H) (x : Block c.k) :
    SplitRAM.flagWord (c.previous s z v) (result (c.stages s) m) x =
      ((Scan.lookup (Scan.build c.incoming load c.D c.cap s) z v x).toNat : Word w) := by
  induction s generalizing z v x with
  | zero => simp [previous,SplitRAM.flagWord,Scan.build,Scan.lookup]
  | succ s ih =>
    have lt : s<c.k := by omega
    let start := result (c.stages s) m
    rw [stages,result_append,Scan.lookup_build_succ]
    by_cases current : z=c.k-(s+1)
    · subst z
      have active : c.k-(s+1)<c.k ∧ c.k-1-(c.k-(s+1))<s+1 := by omega
      have index : c.k-1-(c.k-(s+1))=s := by omega
      have hit : c.previous (s+1) (c.k-(s+1)) v = some (c.bank s v) := by
        rw [previous,ite_eq_left active]
        simp only [address,bank,index]
      rw [hit,ite_eq_left (rfl : c.k-(s+1)=c.k-(s+1))]
      change result (c.sites s H le_rfl) start (c.bank s v+x.val) = _
      have atSite (u : Fin H) (y : Block c.k) : start (c.loadBase u+y.val)=(load u y : Word w) :=
        (c.stages_below m ((Nat.add_lt_add_left y.isLt _).trans_le (old u))).trans (weights u y)
      have depth : c.k-1-s=c.k-(s+1) := by omega
      simpa only [depth] using c.sites_read s lt start load (Scan.lookup (Scan.build c.incoming load c.D c.cap s))
        old room capRoom atSite (fun a u y => ih (by omega) a u y)
        (sumRoom _ (by omega)) H le_rfl v v.isLt x
    · have eqn : c.previous (s+1) z v = c.previous s z v := by
        have test : (z<c.k ∧ c.k-1-z<s+1) ↔ (z<c.k ∧ c.k-1-z<s) := by omega
        simp only [previous,test]
      rw [ite_eq_right current,eqn]
      exact (c.previous_frame (fun a lo=>c.sites_below le_rfl start lo) z v x).trans
        (ih (by omega) z v x)

end Layout

/-- All `k*H` passes, starting at `base`, in the order in which they execute. -/
def passes (k base : ℕ) (incoming : Fin H → List (Fin H)) (loadBase : Fin H → ℕ) (D cap : ℕ) : List Pass :=
  (Layout.mk k base incoming loadBase D cap).stages k

variable {k base D cap : ℕ} {incoming : Fin H → List (Fin H)} {loadBase : Fin H → ℕ}

theorem run (m : Memory w) (old : ∀ v, loadBase v+2^k≤base) (room : base+k*H*2^k<2^w) :
    (ProtocolRAM.program w (passes k base incoming loadBase D cap)).Exec m
      (result (passes k base incoming loadBase D cap) m) (clock (passes k base incoming loadBase D cap)) := by
  let c := Layout.mk k base incoming loadBase D cap
  apply program_exec
  intro p hp
  obtain ⟨t,lt,v,rfl⟩ := c.stages_mem hp
  exact c.pass_fits lt v old room

theorem published (m : Memory w) (load : Fin H → Block k → ℕ)
    (old : ∀ v, loadBase v+2^k≤base) (room : base+k*H*2^k<2^w) (capRoom : cap<2^w)
    (weights : ∀ v (x : Block k), m (loadBase v+x.val)=(load v x : Word w))
    (sumRoom : ∀ d<k, ∀ v x, (Scan.readWeights load d v x).sum < 2^w)
    (d : ℕ) (hd : d<k) (v : Fin H) (x : Block k) :
    result (passes k base incoming loadBase D cap) m (address k base d v+x.val) =
      ((Scan.lookup (Scan.build incoming load D cap k) d v x).toNat : Word w) := by
  let c := Layout.mk k base incoming loadBase D cap
  have active : d<k ∧ k-1-d<k := by omega
  simpa only [c,Layout.previous,ite_eq_left active,SplitRAM.flagWord,passes] using
    c.stage_read load m old room capRoom weights sumRoom k le_rfl d v x

/-- The stored word recognizes exactly the inductive propagated split predicate. -/
theorem published_split (m : Memory w) (load : Fin H → Block k → ℕ) (adj : Fin H → Fin H → Prop)
    (neighbors : ∀ u v, u∈incoming v ↔ adj u v) (positive : 0<D) (limit : ∀ v x,load v x≤cap)
    (old : ∀ v, loadBase v+2^k≤base) (room : base+k*H*2^k<2^w) (capRoom : cap<2^w)
    (weights : ∀ v (x : Block k), m (loadBase v+x.val)=(load v x : Word w))
    (sumRoom : ∀ d<k, ∀ v x, (Scan.readWeights load d v x).sum < 2^w)
    (d : ℕ) (hd : d<k) (v : Fin H) (x : Block k) :
    (result (passes k base incoming loadBase D cap) m (address k base d v+x.val)).val=1 ↔
      Split load adj D cap v d x := by
  rw [published m load old room capRoom weights sumRoom d hd v x,
    ← Scan.lookup_split incoming adj neighbors load positive limit d v x]
  have oneRoom : 1 < 2^w := by
    have lo := old v
    have pos := Nat.two_pow_pos k
    omega
  cases bit : Scan.lookup (Scan.build incoming load D cap k) d v x <;>
    simp [Nat.mod_eq_of_lt oneRoom]

theorem below (m : Memory w) {a : ℕ} (ha : a<base) :
    result (passes k base incoming loadBase D cap) m a=m a :=
  (Layout.mk k base incoming loadBase D cap).stages_below m ha

theorem length : (passes k base incoming loadBase D cap).length=k*H :=
  (Layout.mk k base incoming loadBase D cap).stages_length k

theorem pass_rows {p : Pass} (hp : p∈passes k base incoming loadBase D cap) : p.rows=2^k := by
  let c := Layout.mk k base incoming loadBase D cap
  obtain ⟨s,_,v,rfl⟩ := c.stages_mem hp
  rfl

theorem pass_work (deg : ℕ) (degree : ∀ v,(incoming v).length≤deg)
    {p : Pass} (hp : p∈passes k base incoming loadBase D cap) : p.term.work ≤ SplitRAM.workBound k deg := by
  let c := Layout.mk k base incoming loadBase D cap
  obtain ⟨s,_,v,rfl⟩ := c.stages_mem hp
  refine (SplitRAM.work k incoming loadBase (c.previous s) D cap (k-1-s) v).trans ?_
  let n := 2^k
  have neighbors := Nat.add_le_add_left (Nat.mul_le_mul_right (1+n*9+3) (Nat.succ_le_succ (degree v))) 1
  have row := Nat.add_le_add_left neighbors (1+n*7)
  exact Nat.add_le_add_left (Nat.mul_le_mul_left n (Nat.add_le_add_right (Nat.add_le_add_right row 3) 4)) 1

theorem clock_bound (deg : ℕ) (degree : ∀ v,(incoming v).length≤deg) :
    clock (passes k base incoming loadBase D cap) ≤ 4+k*H*(4+2^k*(2*SplitRAM.workBound k deg+4)) := by
  rw [← length (base:=base) (incoming:=incoming) (loadBase:=loadBase) (D:=D) (cap:=cap)]
  apply clock_le
  exact fun p hp => ⟨(pass_rows hp).le,pass_work deg degree hp⟩

end Hierarchy.DescentColonies.LayerRAM

end OAI
