import OAI.Hierarchy.DescentPrivateTreeGeometry
import OAI.Hierarchy.DescentPackedPayloadBudget
import OAI.Hierarchy.ProtocolRAMGeneratedWrite

namespace OAI
/-! # Compiling all local arrivals of one private reset root from a bounded word panel -/

namespace Hierarchy.DescentPackedFallbackTree
open DescentSIMDLookup DescentPrivateTreeTemplate DescentTreePrefixIntervals ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Classical Fin.CommRing
noncomputable section

def width (H n : ℕ) := (H+2)*(n+1)
abbrev Panel (H n : ℕ) := Fin n→Option (Fin (2^H))

def port (H : ℕ) : Option (Fin (2^H))→Cell (H+2)
  | none=>0
  | some v=>⟨v.val+1,by have:=v.isLt;have pos:=Nat.two_pow_pos H;rw [pow_succ,pow_succ];omega⟩

def pack (H : ℕ) {n : ℕ} (depth : ℕ) (entries : Panel H n) : Cell (width H n) :=
  encode (H+2) (n+1) (Fin.cons (depth:Cell (H+2)) (fun j=>port H (entries j)))

def contains {H : ℕ} (lo hi : ℕ) (a : Cell (H+2)) : Prop := lo<a.val ∧ a.val≤hi

theorem contains_port {H : ℕ} (lo hi : ℕ) (v : Option (Fin (2^H))) :
    contains lo hi (port H v) ↔ ∃x,v=some x ∧ lo≤x.val ∧ x.val<hi := by
  cases v with
  | none=>simp [contains,port]
  | some v=>simp [contains,port]

def tally {H n : ℕ} (key : Cell (width H n)) (shape : Template) :=
  ∑j : Fin n,if contains shape.lo shape.hi (((encode (H+2) (n+1)).symm key) j.succ) then 1 else 0

def count {H n : ℕ} (t : Panel H n) (x : Template) :=
  ∑j,if ∃v,t j=some v ∧ x.lo≤v.val ∧ v.val<x.hi then 1 else 0

theorem tally_pack {H n : ℕ} (depth : ℕ) (t : Panel H n) (x : Template) :
    tally (pack H depth t) x=count t x := by
  simp [tally,count,pack,contains_port]

def localShape {H n : ℕ} (site : ∀d,Site d→ℕ) (slot : ℕ) (key : Cell (width H n)) :=
  let d:=(((encode (H+2) (n+1)).symm key) 0).val
  DescentPrivateTreeTemplate.lookup H d slot (site d)

def output (H n fieldBits unit slot : ℕ) (j : Fin 5) (site : ∀d,Site d→ℕ)
    (key : Cell (width H n)) : Cell fieldBits :=
  let t:=localShape site slot key
  ((![t.active,t.source,t.target,unit*tally key t,t.active] j:ℕ):Cell fieldBits)

theorem output_pack {H n d : ℕ} (within : d≤H) (p : Panel H n) (unit slot fieldBits : ℕ) (j : Fin 5)
    (site : ∀d,Site d→ℕ) :
    let t:=DescentPrivateTreeTemplate.lookup H d slot (site d)
    output H n fieldBits unit slot j site (pack H d p)=
      ((![t.active,t.source,t.target,unit*count p t,t.active] j:ℕ):Cell fieldBits) := by
  have small : d<2^(H+2) := within.trans_lt ((Nat.lt_two_pow_self (n:=H)).trans_le
    (Nat.pow_le_pow_right (by decide) (by omega)))
  have shape : localShape site slot (pack H d p)=DescentPrivateTreeTemplate.lookup H d slot (site d) := by
    have eqn : ((encode (H+2) (n+1)).symm (pack H d p) 0).val=d := by
      rw [pack,Equiv.symm_apply_apply,Fin.cons_zero,Fin.val_cast_of_lt small]
    exact congrArg (fun z=>DescentPrivateTreeTemplate.lookup H z slot (site z)) eqn
  simp only [output,shape,tally_pack]

/-- Each host uses a single packed row for an entire group of roots. One shared
finite table interprets exactly the original root height and all its arrived local leaves. -/
theorem published {H n w hosts groups M b : ℕ} (g : DescentSIMDLookup.Banks) (out unit slot : ℕ) (j : Fin 5)
    (site : ∀d,Site d→ℕ) (d : Fin hosts→Fin groups→ℕ) (le : ∀v i,d v i≤H)
    (p : Fin hosts→Fin groups→Panel H n) (positive : 0<M)
    (fit : Fits g (width H n) b M hosts groups w out) (m : Memory w)
    (words : PinFrame (M:=M) g (output H n b unit slot j site) (fun v i=>pack H (d v i) (p v i)) m) :
    ∃dst,(DescentSIMDLookup.program g out hosts groups M w).Exec m dst (4+(hosts*chunks groups M)*(2*(DescentSIMDLookup.lookup g).work+4)) ∧
      ∀v i,let t:=DescentPrivateTreeTemplate.lookup H (d v i) slot (site (d v i))
        digit b (lane i positive).val (dst (out+(row hosts groups M (position v i positive)).val)).val=
           ((![t.active,t.source,t.target,unit*count (p v i) t,t.active] j:ℕ):Cell b).val := by
  let f:=output H n b unit slot j site
  let x:=fun v i=>pack H (d v i) (p v i)
  have safe : (DescentSIMDLookup.lookup g).Fits w out:=⟨⟨fit.dictionary,fit.source,trivial⟩,fit.mask,trivial⟩
  let dst:=image out (hosts*chunks groups M) (DescentSIMDLookup.lookup g) m
  have read (p : Row hosts groups M) : dst (out+(row hosts groups M p).val)=((masked f x p:ℕ):Word w) :=
    (ProtocolRAMGeneratedWrite.read_image _ _ _ _ _).trans (lookup_read g out fit f x m words p)
  refine ⟨dst,scan_exec out (hosts*chunks groups M) _ m safe fit.output,?_⟩
  intro v i
  exact (physical_read g out fit f x dst read v i positive).trans
    (congrArg Fin.val (output_pack (le v i) (p v i) unit slot b j site))

theorem tariff (g : DescentSIMDLookup.Banks) (hosts groups H n b W h C : ℕ)
    (wide : 2*max (width H n) b≤h) (physical : W≤C*h) :
    let a:=width H n; let M:=lanes h (max a b)
    (4+(hosts*chunks groups M)*(2*(DescentSIMDLookup.lookup g).work+4))*W≤C*(4*h+44*(hosts*h+4*hosts*groups*max a b)) := by
  apply DescentPackedPayloadBudget.clock physical
  exact (invoice g hosts groups (width H n) b h (lt_of_lt_of_le (by unfold width;positivity) (le_max_left _ _)) wide).1

end
end Hierarchy.DescentPackedFallbackTree

end OAI
