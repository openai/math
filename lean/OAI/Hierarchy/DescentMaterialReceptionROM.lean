import OAI.Hierarchy.DescentOrdinaryMaterialSocket
import OAI.Hierarchy.DescentStaticTablePages
import OAI.Hierarchy.DescentPrivateNativePhase

namespace OAI
/-! Shared block projection, compact-host addresses, and receiving path numbers. -/
namespace Hierarchy.DescentRawCablePanel.DepotRAM.Material.Route.Projection
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentHaloWalkRAM DescentOrdinaryAtomFieldRAM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open DescentSixParty.Chronology
open scoped Classical Fin.CommRing
noncomputable section
def pageId {r : ℕ} (gate : Bool) (i : Fin r) (side : Fin 2) : Fin ((2*r)*2) :=
  finProdFinEquiv (finProdFinEquiv (⟨gate.toNat,by cases gate<;>decide⟩,i),side)
def pages (a r M : ℕ) (j : Fin ((2*r)*2)) : ROM.Page :=
  let at₀ : Fin (2*r)×Fin 2:=finProdFinEquiv.symm j
  let z : Fin 2×Fin r:=finProdFinEquiv.symm at₀.1
  ROM.binary (choose (a:=a) (decide (z.1.val=1)) z.2) M at₀.2
def width (a r M : ℕ) :=(a*r+a)*M
def table (a r M base : ℕ) (f : Port) (i : Fin r) : Tables :=
  ROM.joined (pages a r M) (width a r M) base (pageId (gated f) i)
theorem page_read {a r M : ℕ} (gate : Bool) (i : Fin r) (j : Fin 2) :
    pages a r M (pageId gate i j)=ROM.binary (choose (a:=a) gate i) M j :=by
  cases gate <;> simp [pages,pageId]
theorem pageFit (a r M : ℕ) (j : Fin ((2*r)*2)) :
    (pages a r M j).bits≤width a r M :=by
  obtain ⟨⟨q,t⟩,rfl⟩:=finProdFinEquiv.surjective j
  obtain ⟨⟨g,i⟩,rfl⟩:=finProdFinEquiv.surjective q
  simp only [pages,Equiv.symm_apply_apply]
  fin_cases t
  · change a*r*M≤(a*r+a)*M;exact Nat.mul_le_mul_right _ (Nat.le_add_right ..)
  · exact le_rfl
/-- The small launch coordinates are consumed in the radix of the source-return query. -/
def launchSites (r pitch : ℕ) := (2*r)*(pitch/(2*r-1))
def launchWidth (P r pitch : ℕ) (low : Bool) :=
  DescentSharedCableNames.Packed.bits (if low then launchSites r pitch else P)
def narrow {a r : ℕ} (q : ℕ) (i : Fin r) (x : Cell (a*r)) : Cell q :=
  ((choose false i x (0:Cell a)).val:ℕ)
def launchValue (P a r M pitch : ℕ) (low : Bool) (i : Fin r) (x : Cell ((a*r)*M)) :=
  DescentSIMDLookup.table (narrow (a:=a) (launchWidth P r pitch low) i) x
def jump (a r M : ℕ) := if 0<a*M then 2^(a*r*M) else 0
def launchBank (a r M base : ℕ) (low : Bool) (i : Fin r) : Bank :=
  ⟨(ROM.bank (pages a r M) (width a r M) base (pageId low i 0)).base+jump a r M,a*r*M⟩

/-- The upper half of each shift page was already initialized by the shared table scan.
It now contains the block projection re-encoded in the launch radix. -/
def combined (P a r M pitch : ℕ) (j : Fin ((2*r)*2)) : ROM.Page :=
  let q:=finProdFinEquiv.symm j
  let z:Fin 2×Fin r:=finProdFinEquiv.symm q.1
  ⟨width a r M,fun n=>
    if q.2.val=0 ∧ 2^(a*r*M)≤n.val then
      (launchValue P a r M pitch (decide (z.1.val=1)) z.2 ((n.val-2^(a*r*M):ℕ):Cell ((a*r)*M))).val
    else ROM.point (pages a r M j) n.val⟩
private theorem combine_regular (P a r M pitch base w : ℕ) (m : Memory w)
    (flag : Bool) (i : Fin r) (side : Fin 2) (k : Cell (pages a r M (pageId flag i side)).bits) :
    ROM.after (combined P a r M pitch) (width a r M) base m
      ((ROM.bank (pages a r M) (width a r M) base (pageId flag i side)).base+k.val)=
    ROM.after (pages a r M) (width a r M) base m
      ((ROM.bank (pages a r M) (width a r M) base (pageId flag i side)).base+k.val) :=by
  let j:=pageId flag i side
  let wide:Cell (width a r M):=⟨k.val,k.isLt.trans_le (Nat.pow_le_pow_right (by decide) (pageFit a r M j))⟩
  have heard:=ROM.read (combined P a r M pitch) (width a r M) base m j le_rfl wide
  rw [ROM.read _ _ _ _ _ (pageFit ..) k]
  refine heard.trans ?_
  have harmless : ¬(side.val=0 ∧ 2^(a*r*M)≤k.val) :=by
    rintro ⟨h,hk⟩
    have iszero : side=0:=Fin.ext h
    subst side
    have bound := congrArg (fun q : ROM.Page => 2^q.bits) (page_read (a:=a) (M:=M) flag i 0)
    exact (Nat.not_le_of_lt (k.isLt.trans_eq bound)) hk
  simp only [combined,j,pageId,Equiv.symm_apply_apply,wide]
  rw [ite_eq_right harmless]
  change ((ROM.point (pages a r M j) k.val : ℕ) : Word w) = _
  rw [ROM.point, dite_eq_left k.isLt]
  rfl
theorem launch_extent (a r M : ℕ) : jump a r M+2^(a*r*M)≤2^width a r M :=by
  rw [width,Nat.add_mul,pow_add]
  by_cases pos : 0<a*M
  · have two : 2≤2^(a*M):=Nat.le_self_pow (by omega: a*M≠0) 2
    simpa [jump,pos,Nat.mul_two] using Nat.mul_le_mul_left (2^(a*r*M)) two
  · simp [jump,show a*M=0 by omega]
theorem launch_before (a r M base : ℕ) (low : Bool) (i : Fin r) :
    (launchBank a r M base low i).base+(launchBank a r M base low i).size≤
    base+((2*r)*2)*2^width a r M :=by
  let j:=pageId low i 0
  have h:=Nat.add_le_add_left (launch_extent a r M) (base+j.val*2^width a r M)
  calc _ ≤ base+j.val*2^width a r M+2^width a r M :=by simpa [launchBank,ROM.bank,Bank.size,j,Nat.add_assoc] using h
       _ ≤ _ :=by rw [Nat.add_assoc,←Nat.succ_mul];exact Nat.add_le_add_left (Nat.mul_le_mul_right _ j.isLt) _
def mapBase (a r M base : ℕ) := base+((2*r)*2)*2^width a r M
def markBase (a r M K G base : ℕ) :=mapBase a r M base+2^Nat.clog 2 (K*chunks G M+1)
def roof (a r M K G P base : ℕ) :=markBase a r M K G base+(P+1)*2^Nat.clog 2 (K*chunks G M+1)
private def column (w base n : ℕ) (v : ℕ→ℕ) : NativePhase w :=
  ⟨DescentStaticWordColumn.program w base v n,4+10*n,fun m=>DescentStaticWordColumn.image base v m n,
    @DescentStaticWordColumn.cheap _ _ _ _⟩
def stage (H K G M P a r pitch base w : ℕ) : NativePhase w :=
  let load : NativePhase w:=⟨ROM.mount (combined P a r M pitch) (width a r M) w base,4+10*(((2*r)*2)*2^width a r M),
    ROM.after (combined P a r M pitch) (width a r M) base,ROM.cheap _ _ _ _⟩
  let routers:=column w (mapBase a r M base) (K*chunks G M) («prefix» H K G M pitch)
  let marks:=column w (markBase a r M K G base) ((P+1)*(K*chunks G M)) (stampValue K G M a pitch P)
  (load.seq routers).seq marks

variable {w D : ℕ} (H K G M a r pitch base : ℕ) (m : Memory w)
local notation "P" => breadth D
local notation "n" => K*chunks G M
local notation "S" => stage H K G M P a r pitch base w
local notation "b₁" => mapBase a r M base
local notation "b₂" => markBase a r M K G base
local notation "top" => roof a r M K G P base
local notation "m₁" => ROM.after (combined P a r M pitch) (width a r M) base m
local notation "m₂" => DescentStaticWordColumn.image b₁ («prefix» H K G M pitch) m₁ n
private theorem measures : base≤b₁ ∧ b₁+n≤b₂ ∧ b₂+(P+1)*n≤top :=by
  have sizes:n≤2^Nat.clog 2 (n+1):=(Nat.le_succ n).trans (Nat.le_pow_clog (by decide) _)
  exact ⟨Nat.le_add_right ..,Nat.add_le_add_left sizes _,Nat.add_le_add_left (Nat.mul_le_mul_left _ sizes) _⟩
theorem any (space : top<2^w) :
    (S).Runs m ∧ ∀x,x<base ∨ top≤x→(S).image m x=m x :=by
  obtain ⟨left,middle,right⟩:=measures (D:=D) K G M a r base
  have s₁:b₁<2^w:=by omega
  constructor
  · apply NativePhase.seq_runs
    · apply NativePhase.seq_runs
      · exact (ROM.run (combined P a r M pitch) (width a r M) base m s₁).1
      · exact @DescentStaticWordColumn.mount w b₁ n («prefix» H K G M pitch) m₁ (by omega)
    · exact @DescentStaticWordColumn.mount w b₂ ((P+1)*n) (stampValue K G M a pitch P) m₂ (by omega)
  · intro x hx
    change DescentStaticWordColumn.image b₂ _ m₂ _ x=m x
    rw [DescentStaticWordColumn.frame _ _ _ _ _ (by rcases hx with hx|hx <;> omega),
        DescentStaticWordColumn.frame _ _ _ _ _ (by rcases hx with hx|hx <;> omega)]
    exact ROM.frame _ _ _ _ _ (by change x<base ∨ b₁≤x;rcases hx with hx|hx <;> omega)

theorem installed (f : Port) (p : Fin P) (i : Fin r) :
    Static (table a r M base f i) (choose (a:=a) (gated f) i) M ((S).image m) ∧
    (∀z : Row K G M,(S).image m ((Route.bank K G M b₁).base+(row K G M z).val)=(index H pitch z:Word w)) ∧
    Reads (stampBank K G M b₂ f p) (fun (h : Fin K) (_:Fin G)=>(stamp pitch p f h:Cell a)) M ((S).image m) :=by
  obtain ⟨left,middle,right⟩:=measures (D:=D) K G M a r base
  have low (x : ℕ) (hx : x<b₁) : (S).image m x=m₁ x :=
    (DescentStaticWordColumn.frame _ _ _ _ _ (.inl (by omega))).trans (DescentStaticWordColumn.frame _ _ _ _ _ (.inl hx))
  have mapEq (z : Row K G M) : (S).image m (b₁+(row K G M z).val)=m₂ (b₁+(row K G M z).val) :=
    DescentStaticWordColumn.frame _ _ _ _ _ (.inl ((Nat.add_lt_add_left (row K G M z).isLt _).trans_le middle))
  have static:=ROM.binary_mounted (choose (a:=a) (gated f) i) M (pages a r M) (width a r M) base m
    (pageFit a r M) (pageId (gated f) i) (page_read (gated f) i)
  have previous (side : Fin 2) (j : ℕ) (hj : j<2^width a r M) :
      (S).image m ((ROM.bank (pages a r M) (width a r M) base (pageId (gated f) i side)).base+j)=
        m₁ ((ROM.bank (pages a r M) (width a r M) base (pageId (gated f) i side)).base+j) :=by
    let t:=pageId (gated f) i side
    apply low
    change base+t.val*2^width a r M+j<base+((2*r)*2)*2^width a r M
    calc _ < base+(t.val+1)*2^width a r M :=by rw [Nat.succ_mul t.val];omega
         _ ≤ _ :=Nat.add_le_add_left (Nat.mul_le_mul_right _ t.isLt) _
  refine ⟨⟨?_,?_⟩,fun z=>(mapEq z).trans (Route.installed H K G M pitch b₁ m₁ z),
    stamp_read K G M a pitch b₂ m₂ f p⟩
  · intro j
    refine (previous 0 j.val (j.isLt.trans_le (Nat.pow_le_pow_right (by decide : 0<2)
      (Nat.mul_le_mul_right M (Nat.le_add_right (a*r) a))))).trans ?_
    exact (combine_regular P a r M pitch base w m (gated f) i 0 (Fin.cast (congrArg (fun z:ROM.Page=>2^z.bits) (page_read (gated f) i 0)).symm j)).trans (static.1 j)
  · intro j
    exact (previous 1 j.val j.isLt).trans ((combine_regular P a r M pitch base w m (gated f) i 1 (Fin.cast (congrArg (fun z:ROM.Page=>2^z.bits) (page_read (gated f) i 1)).symm j)).trans (static.2 j))

/-- The same static scan produces the separately packed launch rows at the unused shift-page address. -/
theorem launch_installed (low : Bool) (i : Fin r) (x : Cell ((a*r)*M)) :
    (S).image m ((launchBank a r M base low i).base+x.val)=
      ((launchValue P a r M pitch low i x).val:Word w) :=by
  let j:=pageId low i 0
  have lim:=launch_extent a r M
  let addr:Cell (width a r M):=⟨jump a r M+x.val,(Nat.add_lt_add_left x.isLt _).trans_le lim⟩
  have prior:=ROM.read (combined P a r M pitch) (width a r M) base m j le_rfl addr
  have last : (launchBank a r M base low i).base+x.val<b₁:=
    (Nat.add_lt_add_left x.isLt _).trans_le (launch_before a r M base low i)
  have lowEq : (S).image m ((launchBank a r M base low i).base+x.val)=m₁ ((launchBank a r M base low i).base+x.val) :=
    (DescentStaticWordColumn.frame _ _ _ _ _ (.inl (last.trans_le (Nat.le_add_right b₁ _)))).trans
    (DescentStaticWordColumn.frame _ _ _ _ _ (.inl last))
  rw [lowEq]
  have read : m₁ ((launchBank a r M base low i).base+x.val)=((combined P a r M pitch j).number addr:Word w):=by
    simpa only [launchBank,ROM.bank,addr,j,Nat.add_assoc] using prior
  rw [read]
  have dec : (decide (low.toNat=1))=low :=by cases low <;> rfl
  have result : (combined P a r M pitch j).number addr =
      if 2^(a*r*M)≤addr.val then
        (launchValue P a r M pitch low i ((addr.val-2^(a*r*M):ℕ):Cell ((a*r)*M))).val
      else ROM.point (pages a r M j) addr.val :=by
    let g : Fin 2 := ⟨low.toNat,by cases low <;> decide⟩
    let t : Fin (2*r) := finProdFinEquiv (g,i)
    have outer : finProdFinEquiv.symm j = (t,(0:Fin 2)) := finProdFinEquiv.symm_apply_apply _
    have inner : finProdFinEquiv.symm t = (g,i) := finProdFinEquiv.symm_apply_apply _
    have flag : decide (g.val=1)=low :=dec
    have decodedFlag : decide ((finProdFinEquiv.symm ((finProdFinEquiv.symm j : Fin (2*r) × Fin 2).1) : Fin 2 × Fin r).1.val=1)=low :=by
      rw [outer]
      change decide ((finProdFinEquiv.symm t : Fin 2 × Fin r).1.val=1)=low
      rw [inner]
      exact flag
    simp only [combined,outer,inner,Fin.val_zero,true_and]
    exact congrArg (fun flag : Bool => if 2^(a*r*M)≤addr.val then
      (launchValue P a r M pitch flag i ((addr.val-2^(a*r*M):ℕ):Cell ((a*r)*M))).val
      else ROM.point (pages a r M j) addr.val) decodedFlag
  rw [result]
  by_cases pos:0<a*M
  · simp [addr,jump,pos]
  · have zero:a*M=0:=by omega
    have key:(a*r)*M=0:=by rw [Nat.mul_right_comm,zero,Nat.zero_mul]
    have xzero:x.val=0:=by have h := x.isLt.trans_eq (congrArg (fun k:ℕ=>2^k) key);omega
    have blank : launchValue P a r M pitch low i x=0 :=by
      rw [Nat.mul_eq_zero] at zero
      rcases zero with rfl|rfl
      · have fn : narrow (a:=0) (launchWidth P r pitch low) i=fun _=>0:=by
          funext t;have v: (choose false i t (0:Cell 0)).val=0:=by have :=(choose false i t (0:Cell 0)).isLt;omega
          simp [narrow]
        apply Fin.ext; simp [launchValue,DescentSIMDLookup.table,fn,encode]
      · apply Fin.ext
        have h:= (launchValue P a r 0 pitch low i x).isLt
        have h' := h.trans_eq (congrArg (fun k:ℕ=>2^k) (Nat.mul_zero (launchWidth P r pitch low)))
        exact Nat.eq_zero_of_le_zero (by omega)
    rw [blank]
    have zeroPage : ROM.point (pages a r M j) 0=0 :=by
      rw [show pages a r M j=ROM.binary (choose (a:=a) low i) M 0 from page_read low i 0]
      simp [ROM.point,ROM.binary]
    simp [addr,jump,pos,xzero,key,zeroPage]

end
end Hierarchy.DescentRawCablePanel.DepotRAM.Material.Route.Projection

end OAI
