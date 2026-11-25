import OAI.Hierarchy.DescentPrimitiveBirthDigits
import OAI.Hierarchy.DescentResetPrimitivePage

namespace OAI
/-! # The retained span and receiver shape select actual relay, root and tap opcodes -/
namespace Hierarchy.DescentPrimitiveBirth.Layout
open DescentSIMDLookup DescentPackedZip DescentPackedColony DescentColonies.SplitRAM DescentPackedSumWords
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing BigOperators
noncomputable section
variable (z : DescentPrimitiveBirth.Layout) {w : ℕ}
local notation "M" => z.placement.lanes
abbrev Role :=((Fin z.nodes⊕Fin z.arguments)⊕Fin z.roots)⊕Fin 2
def key : z.Role≃Fin z.gates:=
  ((((finSumFinEquiv : (Fin z.nodes⊕Fin z.arguments)≃Fin (z.nodes+z.arguments)).sumCongr (Equiv.refl _)).trans finSumFinEquiv).sumCongr (Equiv.refl _)).trans finSumFinEquiv

def admitted (n : Fin z.nodes) (cls : Cell z.classBits) (paid : Cell z.paidBits) : Cell z.classBits :=
  if n.val<paid.val then cls else 0

def rootId (cls : Cell z.classBits) : Option (Fin z.roots) :=
  if h:6≤cls.val ∧ cls.val-6<z.roots then some ⟨cls.val-6,h.2⟩ else none

def spanId (first : Cell z.spanBits) : Option (Fin z.arguments) :=
  if h:0<first.val ∧ first.val<z.arguments then some ⟨first.val,h.2⟩ else none

def tag (cls : Cell z.classBits) (more : Cell 1) : Cell z.rootBits :=
  if cls.val=4 then if more=0 then 3 else 5 else if cls.val=5 then 5 else 0

def tagRelay (cls : Cell z.classBits) : Cell 1:=if cls.val=2 then 1 else 0

def law : z.Role→Book.Gate
  | .inl (.inl (.inl n))=>⟨z.classBits,z.paidBits,z.classBits,z.admitted n⟩
  | .inl (.inl (.inr j))=>⟨z.spanBits,z.spanBits,1,fun a b=>if z.spanId a=some j then if b=0 then 0 else 1 else 0⟩
  | .inl (.inr q)=>⟨z.classBits,z.rootBits,z.rootBits,fun c x=>if z.rootId c=some q then x else 0⟩
  | .inr i=>if i=0 then ⟨z.classBits,1,z.rootBits,z.tag⟩ else ⟨z.classBits,0,1,fun c _=>z.tagRelay c⟩

def laws (i : Fin z.gates) :=z.law (z.key.symm i)
def mountOrigin (base w : ℕ) :=Book.install z.laws z.aperture M w (z.lifted base)
def originMem (base : ℕ) (m : Memory w) :=Book.image z.laws z.aperture M (z.lifted base) m
def tables (base : ℕ) (i : z.Role) :=Book.tables z.laws z.aperture M (z.lifted base) (z.key i)
def gate (base : ℕ) (i : z.Role) (l r : Expr) :=(z.tables base i).read l r

def active (base : ℕ) (n : Fin z.nodes) (cls paid : Expr) :=z.gate base (.inl (.inl (.inl n))) cls paid
def first (spans : Fin z.arguments→Expr) :=if h:0<z.arguments then spans ⟨0,h⟩ else .lit 0
def more (base : ℕ) (spans : Fin z.arguments→Expr) :=
  total (fun j=>z.gate base (.inl (.inl (.inr j))) (z.first spans) (spans j)) (List.finRange z.arguments)
def rotations (base : ℕ) (cls : Expr) (roots : Fin z.roots→Expr) :=
  total (fun j=>z.gate base (.inl (.inr j)) cls (roots j)) (List.finRange z.roots)
def fresh (base : ℕ) (n : Fin z.nodes) (cls paid : Expr) (spans : Fin z.arguments→Expr) (roots : Fin z.roots→Expr) :=
  let live:=z.active base n cls paid
  Expr.op .add (z.rotations base live roots) (z.gate base (.inr 0) live (z.more base spans))
def relay (base : ℕ) (n : Fin z.nodes) (cls paid : Expr) :=
  z.gate base (.inr 1) (z.active base n cls paid) (.lit 0)

private theorem width (i:z.Role) : (z.law i).left+(z.law i).right≤z.aperture:=by
  rcases i with ((n|j)|q)|k
  · exact Nat.le_max_left ..
  · exact (Nat.le_max_left ..).trans (Nat.le_max_right ..)
  · exact ((Nat.le_max_left ..).trans (Nat.le_max_right ..)).trans (Nat.le_max_right ..)
  · fin_cases k <;> simp [law,aperture]

theorem originsAny (base : ℕ) (m : Memory w) (space : z.endAddress base<2^w) :
    (z.mountOrigin base w).Exec m (z.originMem base m) (4+10*(z.gates*(2*2^(z.aperture*M)))) ∧
    CheapCode (z.mountOrigin base w) ∧ (∀i,i<z.lifted base ∨ z.endAddress base≤ i→z.originMem base m i=m i) ∧
    ∀i,Static (z.tables base i) (z.law i).eval M (z.originMem base m):=by
  have p:=Book.mount z.laws z.aperture M (z.lifted base) m (fun j=>z.width (z.key.symm j)) space
  refine ⟨p.1,p.2.2.2,p.2.2.1,fun i=>?_⟩
  let reads (j : z.Role) := Static (z.tables base i) (z.law j).eval M (z.originMem base m)
  have stored : reads (z.key.symm (z.key i)) := p.2.1 (z.key i)
  change reads i
  simpa only [Equiv.symm_apply_apply] using stored

def extra (spans : Fin z.arguments→Cell z.spanBits) : Cell 1:=
  let first:=if h:0<z.arguments then spans ⟨0,h⟩ else 0
  (z.spanId first).elim 0 (fun j=>if spans j=0 then 0 else 1)

def raw (n : Fin z.nodes) (cl : Cell z.classBits) (paid : Cell z.paidBits) (spans : Fin z.arguments→Cell z.spanBits)
    (roots : Fin z.roots→Cell z.rootBits) :=
  let live:=z.admitted n cl paid
  (z.rootId live).elim (z.tag live (z.extra spans)) roots

private theorem tables_fit (base : ℕ) (space : z.endAddress base<2^w) (i : z.Role) (a b : Expr)
    (l : a.Fits w (z.endAddress base)) (r : b.Fits w (z.endAddress base)) :
    DescentPackedZip.Fits (z.tables base i) a b (z.law i).left (z.law i).right M (z.endAddress base) w:=by
  have p:=Book.geometry z.laws z.aperture M (z.lifted base) (z.key i) (out:=z.endAddress base) le_rfl space
    (z.width (z.key.symm (z.key i)))
  exact ⟨l,r,p.1,p.2,by simp [tables,Book.tables,laws],by simp [tables,Book.tables,laws]⟩

private theorem term_fit (base : ℕ) (space : z.endAddress base<2^w) (i : z.Role) {a b : Expr}
    (l : a.Fits w (z.endAddress base)) (r : b.Fits w (z.endAddress base)) :
    (z.gate base i a b).Fits w (z.endAddress base):=by
  have p:=z.tables_fit base space i a b l r
  exact ⟨p.apply,p.right,p.shift,p.left⟩

theorem originFits (base : ℕ) (n : Fin z.nodes) (cls paid : Expr) (spans : Fin z.arguments→Expr)
    (roots : Fin z.roots→Expr) (space : z.endAddress base<2^w)
    (clsFit : cls.Fits w (z.lifted base)) (payFit : paid.Fits w (z.lifted base))
    (spanFit : ∀j,(spans j).Fits w (z.lifted base)) (rootFit : ∀j,(roots j).Fits w (z.lifted base)) :
    (z.fresh base n cls paid spans roots).Fits w (z.endAddress base) ∧ (z.relay base n cls paid).Fits w (z.endAddress base):=by
  have mono {e:Expr} (h:e.Fits w (z.lifted base)) : e.Fits w (z.endAddress base) := ProtocolRAMGeneratedWrite.fits_mono e (Nat.le_add_right ..) h
  have h₀:=z.term_fit base space (.inl (.inl (.inl n))) (mono clsFit) (mono payFit)
  have h₁ : (z.first spans).Fits w (z.endAddress base):=by unfold first;split;exact mono (spanFit _);trivial
  have rot:=DescentPrimitiveBirth.totalFits _ (fun j=>z.term_fit base space (.inl (.inr j)) h₀ (mono (rootFit j)))
  have tap:=DescentPrimitiveBirth.totalFits _ (fun j=>z.term_fit base space (.inl (.inl (.inr j))) h₁ (mono (spanFit j)))
  exact ⟨⟨rot,z.term_fit base space (.inr 0) h₀ tap⟩,z.term_fit base space (.inr 1) h₀ trivial⟩

theorem sourceLaw {H G} (base : ℕ) (m : Memory w) (space : z.endAddress base<2^w) (i:z.Role)
    (a b : Expr) (x : Fin H→Fin G→Cell (z.law i).left) (y : Fin H→Fin G→Cell (z.law i).right)
    (blank : (z.law i).eval 0 0=0) (fa : a.Fits w (z.endAddress base)) (fb : b.Fits w (z.endAddress base))
    (xa : Source a x M (z.originMem base m)) (yb : Source b y M (z.originMem base m)) :
    Source (z.gate base i a b) (fun h g=>(z.law i).eval (x h g) (y h g)) M (z.originMem base m):=
  read_data _ _ _ _ (z.tables_fit base space i a b fa fb) _ blank _ ((z.originsAny base m space).2.2.2 i) _ _ xa yb

private theorem blankLaw (i : z.Role) : (z.law i).eval 0 0 = 0 := by
  rcases i with ((n|j)|q)|i
  · change z.admitted n 0 0 = 0
    unfold admitted
    split <;> rfl
  · change (if z.spanId 0 = some j then (if (0 : Cell z.spanBits) = 0 then 0 else 1) else 0) = (0 : Cell 1)
    rw [ite_eq_left rfl]
    split <;> rfl
  · change (if z.rootId 0 = some q then 0 else 0) = (0 : Cell z.rootBits)
    split <;> rfl
  · fin_cases i
    · change z.tag 0 0 = 0
      simp only [tag, Fin.val_zero, Nat.reduceEqDiff, ite_false]
    · change z.tagRelay 0 = 0
      simp only [tagRelay, Fin.val_zero, Nat.reduceEqDiff, ite_false]

theorem originSource {H G} (base : ℕ) (m : Memory w) (space : z.endAddress base<2^w)
    (n : Fin z.nodes) (cls paid : Expr) (spans : Fin z.arguments→Expr) (roots : Fin z.roots→Expr)
    (C : Fin H→Fin G→Cell z.classBits) (P : Fin H→Fin G→Cell z.paidBits)
    (S : Fin z.arguments→Fin H→Fin G→Cell z.spanBits) (R : Fin z.roots→Fin H→Fin G→Cell z.rootBits)
    (fc : cls.Fits w (z.lifted base)) (fp : paid.Fits w (z.lifted base)) (fs : ∀j,(spans j).Fits w (z.lifted base))
    (fr : ∀j,(roots j).Fits w (z.lifted base))
    (rc : Source cls C M m) (rp : Source paid P M m) (rs : ∀j,Source (spans j) (S j) M m)
    (rr : ∀j,Source (roots j) (R j) M m) :
    Source (z.fresh base n cls paid spans roots) (fun h g=>z.raw n (C h g) (P h g) (fun j=>S j h g) (fun j=>R j h g))
        M (z.originMem base m) ∧
      Source (z.relay base n cls paid) (fun h g=>z.tagRelay (z.admitted n (C h g) (P h g))) M (z.originMem base m):=by
  let dst:=z.originMem base m
  let top:=z.endAddress base
  have mono {e : Expr} (h:e.Fits w (z.lifted base)) : e.Fits w (z.endAddress base) := ProtocolRAMGeneratedWrite.fits_mono e (Nat.le_add_right ..) h
  have move {e : Expr} {a : ℕ} {v:Fin H→Fin G→Cell a} (before:e.Fits w (z.lifted base)) (src:Source e v M m) : Source e v M dst:=
    fun i=>(eval_below e _ m dst before (fun j h=>(z.originsAny base m space).2.2.1 j (.inl h))).trans (src i)
  let act:=z.active base n cls paid
  let live:=fun h g=>z.admitted n (C h g) (P h g)
  have actFit:=z.term_fit base space (.inl (.inl (.inl n))) (mono fc) (mono fp)
  have ac : Source act live M dst:=z.sourceLaw base m space (.inl (.inl (.inl n))) _ _ _ _ (z.blankLaw _)
    (mono fc) (mono fp) (move fc rc) (move fp rp)
  have nil₀:=DescentPrimitiveBirth.zero (H:=H) (G:=G) (a:=0) («M»:=M) dst
  have selfRead : Source (z.relay base n cls paid) (fun h g=>z.tagRelay (live h g)) M dst:=by
    exact z.sourceLaw base m space (.inr 1) _ _ _ _ (z.blankLaw _) actFit trivial ac nil₀
  let s₀:=fun h g=>if pos:0<z.arguments then S ⟨0,pos⟩ h g else 0
  have firstFit : (z.first spans).Fits w top:=by unfold first;split;exact mono (fs _);trivial
  have firstData : Source (z.first spans) s₀ M dst:=by
    by_cases pos:0<z.arguments
    · simpa only [first,s₀,dite_eq_left pos] using move (fs ⟨0,pos⟩) (rs ⟨0,pos⟩)
    · simpa only [first,s₀,dite_eq_right pos] using (DescentPrimitiveBirth.zero (a:=z.spanBits) (H:=H) (G:=G) («M»:=M) dst)
  have rank : Source (z.more base spans) (fun h g=>z.extra (fun j=>S j h g)) M dst:=by
    apply DescentPrimitiveBirth.oneHot _ _ (fun h g=>z.spanId (s₀ h g)) (fun j h g=>if S j h g=0 then (0:Cell 1) else 1)
    intro j
    exact z.sourceLaw base m space (.inl (.inl (.inr j))) _ _ _ _ (z.blankLaw _)
       firstFit (mono (fs j)) firstData (move (fs j) (rs j))
  have rot : Source (z.rotations base act roots) (DescentOperandCandidateLookup.selected (fun h g=>z.rootId (live h g)) R) M dst:=by
    apply DescentPrimitiveBirth.oneHot
    intro q
    exact z.sourceLaw base m space (.inl (.inr q)) _ _ _ _ (z.blankLaw _)
       actFit (mono (fr q)) ac (move (fr q) (rr q))
  have moreFit:=DescentPrimitiveBirth.totalFits _ (fun j=>z.term_fit base space (.inl (.inl (.inr j))) firstFit (mono (fs j)))
  have fallback : Source (z.gate base (.inr 0) act (z.more base spans))
      (fun h g=>z.tag (live h g) (z.extra (fun j=>S j h g))) M dst :=
    z.sourceLaw base m space (.inr 0) _ _ _ _ (z.blankLaw _) actFit moreFit ac rank
  refine ⟨?_,selfRead⟩
  intro i
  change (z.rotations base act roots).eval dst _+(z.gate base (.inr 0) act (z.more base spans)).eval dst _=_
  rw [rot i,fallback i,←Nat.cast_add]
  congr 1
  apply DescentOperandFieldJoin.packed_add
  intro h g
  cases hit:z.rootId (live h g) with
  | none=>simp [DescentOperandCandidateLookup.selected,raw,hit,live]
  | some j=>
    have enough : 6≤(live h g).val:=by
      unfold rootId at hit
      split at hit
      · exact ‹_ ∧ _›.1
      · contradiction
    have a : (live h g).val≠4:=by omega
    have b : (live h g).val≠5:=by omega
    simp [DescentOperandCandidateLookup.selected,raw,tag,show z.admitted n (C h g) (P h g)=live h g from rfl,hit,a,b]
end
end Hierarchy.DescentPrimitiveBirth.Layout

end OAI
