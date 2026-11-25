import OAI.Hierarchy.TraceReceiverOwnerRead
import OAI.Hierarchy.GridPinReceiverPrefix
import OAI.Hierarchy.GridPinArenaRoom

namespace OAI
/-! # Physical frames of the receiver's interval and chronological owner scans -/
namespace Hierarchy.TraceReceiverEntryFrame
open ThreeFlat Diagonal.TickWorkspace Computability.VPVNP.BurstRAM PrivateRAM
open GridPinPublisher
open scoped Fin.CommRing

/-- Low shifted PIN words, all resident source, library and S43/S44 banks, and
the high T archive and decoder dictionaries. -/
def Kept (w u a : ℕ) : Prop :=
  a < base u 1 ∨ (base u 12 ≤ a ∧ a < base u 45) ∨ 16*GridDescription.sector w ≤ a

set_option quotPrecheck false
variable {w u k n q pins pars sel text compact rails bits N stages full K f roots : ℕ}
local notation "span" => (2*2^(w/2))
local notation "P" => canonical w k n q pins pars sel text compact rails bits N stages full span
local notation "J" => GridDescription.sector w
local notation "g" => GridPinArena.slab w
local notation "S" => stride u
local notation "owners" => (GridReceiverTickDirectory.banks w u).owners
local notation "target" => ((GridReceiverTickDirectory.banks w u).scratch+1)

theorem lane_span (wide : 2 ≤ w) (bitsFit : bits ≤ g) (lower : 4*w ≤ u^10) :
    4*(P).lanes ≤ S := by
  let quarter := 2^(16*w-2)
  have square : g=4*quarter := by
    change 2^(16*w)=2^2*2^(16*w-2)
    rw [←pow_add,show 2+(16*w-2)=16*w by omega]
  have two : 2 ≤ 2^(w/2):=Nat.pow_le_pow_right (by decide : 0<2) (show 1 ≤ w/2 by omega)
  have four : 4 ≤ span:=by omega
  have roof : bits ≤ quarter*span:=by
    have h:=Nat.mul_le_mul_left quarter four
    rw [square,Nat.mul_comm 4 quarter] at bitsFit
    omega
  have quota : (P).lanes ≤ quarter := by
    apply Nat.le_of_lt_succ
    change (bits+span-1)/span < quarter+1
    apply (Nat.div_lt_iff_lt_mul (by omega)).mpr
    rw [Nat.add_mul,Nat.one_mul];omega
  have slot : g ≤ S:=by
    change 2^(16*w)≤(2^(u^10))^4
    rw [←pow_mul];exact Nat.pow_le_pow_right (by decide) (by omega)
  exact (Nat.mul_le_mul_left 4 quota).trans (square ▸ slot)

/-- The exact canonical seed/factor/bucket passes update only their three
consecutive allocator slices. The fourth pass additionally writes column 3 of
the four-word interval rows in S5. -/
theorem interval (R : GridPinArena.Scalars (64*w) P bits full K g)
    (wide : 2 ≤ w) (lower : 4*w ≤ u^10) (upper : u^10 ≤ 5*w) (bitsFit : bits ≤ g)
    (m : Memory (64*w)) (live : PrefixOwners P m) (a : ℕ)
    (range : (a < base u 5 ∨ base u 6 ≤ a) ∧ (a < 15*J+8*g ∨ 15*J+11*g ≤ a)) :
    (P).intervalMemory (base u 5) m a=m a := by
  have pos : 0 < w:=by omega
  have scales:=GridPinArena.scales w pos
  have sep:=TraceReceiverOwnerMount.sector pos upper
  have slots:=lane_span (k:=k) (n:=n) (q:=q) (pins:=pins) (pars:=pars) (sel:=sel) (text:=text)
    (compact:=compact) (rails:=rails) (bits:=bits) (N:=N) (stages:=stages) (full:=full) wide bitsFit lower
  have gp : 0 < g:=Nat.two_pow_pos _
  have ticksGap:=R.bank.disjoint .ticks .factors (by decide)
  change 15*J+8*g+(P).ticks ≤ 15*J+9*g ∨ 15*J+9*g+N ≤ 15*J+8*g at ticksGap
  have factorsGap:=R.bank.disjoint .factors .blocks (by decide)
  change 15*J+9*g+N ≤ 15*J+10*g ∨ 15*J+10*g+(P).lanes ≤ 15*J+9*g at factorsGap
  have blocksGap:=R.bank.disjoint .blocks .rails (by decide)
  change 15*J+10*g+(P).lanes ≤ 15*J+11*g ∨ 15*J+11*g+(P).endpoints/2 ≤ 15*J+10*g at blocksGap
  have blocksFit:=R.window.fit .blocks
  change 15*J+10*g+g < 2^(64*w) at blocksFit
  let G : PrefixGeometry (64*w) P full := ⟨R.factorsFit.le,R.itemsFit,fun h=>Nat.pos_of_mul_pos_left h,R.within,rfl⟩
  obtain ⟨s₅,banks⟩:=range
  refine interval_frame P R.bank G m live (base u 5) R.lanesFit
    (by change 15*J+10*g+(P).lanes ≤ 2^(64*w);omega) (by change 6*S+4*(P).lanes ≤ 2^(64*w);omega)
    R.pinsFit ?_ a ?_ ?_ ?_ ?_
  · intro b hb i hi
    change 15*J+10*g+b≠6*S+4*i+3
    omega
  · intro i hi
    change a < 6*S ∨ 7*S ≤ a at s₅
    change a≠6*S+4*i+3
    omega
  · change a < 15*J+8*g ∨ 15*J+8*g+(P).ticks ≤ a;omega
  · change a < 15*J+9*g ∨ 15*J+9*g+N ≤ a;omega
  · change a < 15*J+10*g ∨ 15*J+10*g+(P).lanes ≤ a;omega

/-- All the memory needed at entry to the owner scan, including the decoded
target, is retained by the literal canonical interval program. -/
theorem interval_inputs (R : GridPinArena.Scalars (64*w) P bits full K g)
    (wide : 2 ≤ w) (lower : 4*w ≤ u^10) (upper : u^10 ≤ 5*w) (bitsFit : bits ≤ g)
    (old : 8*(f+roots) ≤ S) (rootFit : roots ≤ g) (m : Memory (64*w)) (live : PrefixOwners P m)
    (a : ℕ) (rd : TraceReceiverOwnerMount.Reads u f roots owners target a) :
    (P).intervalMemory (base u 5) m a=m a := by
  have scales:=GridPinArena.scales w (by omega)
  have sep:=TraceReceiverOwnerMount.sector (by omega : 0 < w) upper
  apply interval R wide lower upper bitsFit m live a
  rcases TraceReceiverOwnerMount.read_bands old rootFit rd with h|h|h
  · change 45*S ≤ a ∧ a < 46*S at h
    change (a < 6*S ∨ 7*S ≤ a) ∧ _;omega
  · change (a < 6*S ∨ 7*S ≤ a) ∧ _;omega
  · change (a < 6*S ∨ 7*S ≤ a) ∧ _;omega

theorem interval_kept (R : GridPinArena.Scalars (64*w) P bits full K g)
    (wide : 2 ≤ w) (lower : 4*w ≤ u^10) (upper : u^10 ≤ 5*w) (bitsFit : bits ≤ g)
    (m : Memory (64*w)) (live : PrefixOwners P m) (a : ℕ) (h : Kept w u a) :
    (P).intervalMemory (base u 5) m a=m a := by
  have scales:=GridPinArena.scales w (by omega)
  have sep:=TraceReceiverOwnerMount.sector (by omega : 0 < w) upper
  apply interval R wide lower upper bitsFit m live a
  change a < 2*S ∨ (13*S ≤ a ∧ a < 46*S) ∨ 16*J ≤ a at h
  change (a < 6*S ∨ 7*S ≤ a) ∧ _
  omega

theorem owner_keeps_s5 (r : TraceReceiverOwnerMount.Room (64*w) u f roots owners target)
    (m : Memory (64*w)) (a : ℕ) (lo : base u 5 ≤ a) (hi : a < base u 6) :
    TraceReceiverOwnerMount.output u f roots owners target m a=m a := by
  apply TraceReceiverOwnerMount.output_frame r m a
  have s:=r.fixed;have nodes:=r.nodes
  change 6*S ≤ a at lo
  change a < 7*S at hi
  change ¬((a=12*S+3*(S/4) ∨ a=12*S+3*(S/4)+1 ∨ a=7*S+1 ∨ a=2*S ∨ a=2*S+3) ∨
    (12*S+1*(S/4) ≤ a ∧ a < 12*S+1*(S/4)+2*roots) ∨ (46*S ≤ a ∧ a < 46*S+(f+roots)))
  omega

theorem owner_slot (r : TraceReceiverOwnerMount.Room (64*w) u f roots owners target)
    (wide : 2 ≤ w) (lower : 4*w ≤ u^10) (bitsFit : bits ≤ g) (m : Memory (64*w)) (j : Fin (P).lanes) :
    TraceReceiverOwnerMount.output u f roots owners target m (base u 5+4*j.val+3)=m (base u 5+4*j.val+3) := by
  have slots:=lane_span (k:=k) (n:=n) (q:=q) (pins:=pins) (pars:=pars) (sel:=sel) (text:=text)
    (compact:=compact) (rails:=rails) (bits:=bits) (N:=N) (stages:=stages) (full:=full) wide bitsFit lower
  have index:=j.isLt
  exact owner_keeps_s5 (u:=u) r m (base u 5+4*j.val+3) (by omega) (by change 6*S+4*j.val+3 < 7*S;omega)

theorem after (R : GridPinArena.Scalars (64*w) P bits full K g)
    (r : TraceReceiverOwnerMount.Room (64*w) u f roots owners target)
    (wide : 2 ≤ w) (lower : 4*w ≤ u^10) (upper : u^10 ≤ 5*w) (bitsFit : bits ≤ g)
    (m : Memory (64*w)) (live : PrefixOwners P m) (a : ℕ) (h : Kept w u a) :
    TraceReceiverOwnerMount.output u f roots owners target ((P).intervalMemory (base u 5) m) a=m a := by
  refine Eq.trans (TraceReceiverOwnerMount.output_frame r _ a ?_) (interval_kept R wide lower upper bitsFit m live a h)
  apply TraceReceiverOwnerMount.untouched_of_bands r.fixed r.nodes
  have sep:=TraceReceiverOwnerMount.sector (by omega : 0 < w) upper
  rcases h with lo|middle|high
  · exact .inl lo
  · exact .inr (.inl middle)
  · right;right;change 47*S ≤ a;omega

/-- The classifier rows on either side of the three prefix accumulators
survive both S5 allocation and the S45 reverse traversal. -/
theorem after_bank (R : GridPinArena.Scalars (64*w) P bits full K g)
    (r : TraceReceiverOwnerMount.Room (64*w) u f roots owners target)
    (large : 2 ≤ w) (lower : 4*w ≤ u^10) (upper : u^10 ≤ 5*w) (bitsFit : bits ≤ g)
    (m : Memory (64*w)) (live : PrefixOwners P m) (a : ℕ) (lo : 14*J ≤ a)
    (outside : a < 15*J+8*g ∨ 15*J+11*g ≤ a) :
    TraceReceiverOwnerMount.output u f roots owners target ((P).intervalMemory (base u 5) m) a=m a := by
  have sep:=TraceReceiverOwnerMount.sector (by omega : 0 < w) upper
  refine (TraceReceiverOwnerMount.output_frame r _ a
    (TraceReceiverOwnerMount.untouched_of_bands r.fixed r.nodes (.inr (.inr (by change 47*S ≤ a;omega))))).trans ?_
  exact interval R large lower upper bitsFit m live a ⟨.inr (by change 7*S ≤ a;omega),outside⟩

/-- Rereading the original factor key, elected ordinal and decoded target reproduces
the S17 roster after traversal. The resource counts and all original high journal
words, including the last true destination rows, also survive. -/
theorem after_classifier (R : GridPinArena.Scalars (64*w) P bits full K g)
    (r : TraceReceiverOwnerMount.Room (64*w) u f roots owners target)
    (large : 2 ≤ w) (lower : 4*w ≤ u^10) (upper : u^10 ≤ 5*w) (bitsFit : bits ≤ g)
    (m : Memory (64*w)) (live : PrefixOwners P m) :
    let out:=TraceReceiverOwnerMount.output u f roots owners target ((P).intervalMemory (base u 5) m)
    (∀ v < g,out (15*J+g+v)=m (15*J+g+v)) ∧
    (∀ v < g,out (15*J+3*g+v)=m (15*J+3*g+v)) ∧
    out (15*J+20*g+1)=m (15*J+20*g+1) ∧
    (∀ v < g,out (14*J+v)=m (14*J+v)) ∧
    ∀ a,16*J ≤ a → out a=m a := by
  intro out
  have scales:=GridPinArena.scales w (by omega)
  have go:=after_bank R r large lower upper bitsFit m live
  refine ⟨?_,?_,go (15*J+20*g+1) (by omega) (.inr (by omega)),?_,?_⟩
  · intro v inside;exact go (15*J+g+v) (by omega) (.inl (by omega))
  · intro v inside;exact go (15*J+3*g+v) (by omega) (.inl (by omega))
  · intro v inside;exact go (14*J+v) (by omega) (.inl (by omega))
  · intro a hi;exact go a (by omega) (.inr (by omega))

end Hierarchy.TraceReceiverEntryFrame

end OAI
