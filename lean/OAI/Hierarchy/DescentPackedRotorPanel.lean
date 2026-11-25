import OAI.Hierarchy.DescentResetPaletteCode
import OAI.Hierarchy.DescentRotorPrivateFields
import OAI.Hierarchy.ProtocolRAMGeneratedWrite
import OAI.Hierarchy.DescentPackedPayloadBudget
import OAI.Hierarchy.ProtocolRAMBinarySpan

namespace OAI
/-! # Issuing a packed panel of relative rotor endpoints and integral cable sizes -/

namespace Hierarchy.DescentPackedRotorPanel
open DescentSIMDLookup DescentResetPaletteCode DescentRotorPrivateFields ProtocolRAM
open Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped BigOperators Classical Fin.CommRing
noncomputable section
variable {n h : ℕ} (G : NonlinearExpanders.Graph n h)
local notation "Q" => DescentCommonPalette.rotor G

def inputBits (r l : ℕ) := (r+1)+l+1
abbrev Live (r l : ℕ) := Cell (r+1) × Cell l

/-- Zero marks an absent root. A live row only carries its relative interval ticket and
measured layer count. The old vertex address and physical unit are shared by the panel. -/
def encodeRoot (r l : ℕ) : Option (Live r l)→Cell (inputBits r l)
  | none=>0
  | some x=>⟨1+(finProdFinEquiv x).val,by
    have small:=(finProdFinEquiv x).isLt
    have pos : 0<2^(r+1)*2^l:=by positivity
    calc
      1 + (finProdFinEquiv x).val < (2^(r+1)*2^l)*2 := by omega
      _ = 2^(inputBits r l) := by
        unfold inputBits
        rw [pow_succ (2 : ℕ) ((r+1)+l), pow_add (2 : ℕ) (r+1) l]⟩

def «fields» (r H C b : ℕ) (s : Bool) (slot label layers : ℕ) : Fin 5→ℕ :=
  match edgeAt G slot with
  | none=>fun _=>0
  | some e=>
    let host (v : (Q).Site) :=
      rom G r H (encoder G r H (finTwoEquiv.symm s).val label (rotorCell G v).val)
    ![1,host ((Q).src e),host ((Q).dst e),layers*price G C b e,1]

def ceiling (r H l C b : ℕ) := max 1 (max (DescentDenseHostOrder.roster G r H).card
  (2^l*max (C*b) ((2+2*h*C)*b)))
def outputBits (r H l C b : ℕ) := ProtocolRAMPurchaseSampler.bits (ceiling G r H l C b)

theorem rom_bound (r H addr : ℕ) : rom G r H addr≤(DescentDenseHostOrder.roster G r H).card := by
  unfold rom
  split
  · exact (Fin.isLt _).le
  · omega

theorem field_bound (r H l C b : ℕ) (s : Bool) (slot : ℕ) (x : Live r l) (j : Fin 5) :
    «fields» G r H C b s slot x.1.val x.2.val j≤ceiling G r H l C b := by
  have one : 1≤ceiling G r H l C b:=Nat.le_max_left _ _
  have rank : ∀addr,rom G r H addr≤ceiling G r H l C b:=fun addr=>(rom_bound G r H addr).trans
    ((Nat.le_max_left _ _).trans (Nat.le_max_right _ _))
  cases he : edgeAt G slot with
  | none=>simp [«fields»,he]
  | some e=>
    have priceBound : price G C b e≤ max (C*b) ((2+2*h*C)*b) := by
      rcases e with e | ⟨v,k⟩
      · exact Nat.le_max_left _ _
      · exact (spine_price G C b v k).le.trans (Nat.le_max_right _ _)
    have cost : x.2.val*price G C b e≤ceiling G r H l C b:=
      (Nat.mul_le_mul x.2.isLt.le priceBound).trans ((Nat.le_max_right _ _).trans (Nat.le_max_right _ _))
    simp only [«fields», he]
    fin_cases j <;> first | exact one | exact rank _ | exact cost

theorem field_fits (r H l C b : ℕ) (s : Bool) (slot : ℕ) (x : Live r l) (j : Fin 5) :
    «fields» G r H C b s slot x.1.val x.2.val j<2^(outputBits G r H l C b) :=
  (field_bound G r H l C b s slot x j).trans_lt (ProtocolRAMPurchaseSampler.lt_span _)

def localOutput (r H l C b : ℕ) (s : Bool) (slot : ℕ) (j : Fin 5) (key : Cell (inputBits r l)) : Cell (outputBits G r H l C b) :=
  if key.val=0 then 0 else
    («fields» G r H C b s slot ((key.val-1)/2^l) ((key.val-1)%2^l) j:Cell (outputBits G r H l C b))

theorem local_read (r H l C b : ℕ) (s : Bool) (slot : ℕ) (j : Fin 5) (x : Option (Live r l)) :
    (localOutput G r H l C b s slot j (encodeRoot r l x)).val=
      x.elim 0 (fun t=>«fields» G r H C b s slot t.1.val t.2.val j) := by
  cases x with
  | none=>simp [encodeRoot,localOutput]
  | some x=>
    have number : (encodeRoot r l (some x)).val=1+(x.2.val+2^l*x.1.val) := rfl
    have nonzero : (encodeRoot r l (some x)).val≠0:=by rw [number];omega
    have untag : (encodeRoot r l (some x)).val-1=x.2.val+2^l*x.1.val := by rw [number]; omega
    have quot : (x.2.val+2^l*x.1.val)/2^l=x.1.val := by
      rw [Nat.add_mul_div_left _ _ (Nat.two_pow_pos _),Nat.div_eq_of_lt x.2.isLt,zero_add]
    have rem : (x.2.val+2^l*x.1.val)%2^l=x.2.val:=by simp [Nat.add_mul_mod_self_left,Nat.mod_eq_of_lt x.2.isLt]
    rw [localOutput, ite_eq_right nonzero, untag, quot, rem]
    exact Fin.val_cast_of_lt (field_fits G r H l C b s slot x j)

/-- Actual native work is one row per packed group chunk. The hidden long host/vertex
prefix and the absolute cable width never appear in the output cell. -/
theorem published {hosts groups M w : ℕ} (g : DescentSIMDLookup.Banks) (r H l C b out slot : ℕ) (s : Bool)
    (j : Fin 5) (x : Fin hosts→Fin groups→Option (Live r l)) (positive : 0<M)
    (fit : Fits g (inputBits r l) (outputBits G r H l C b) M hosts groups w out) (m : Memory w)
    (pins : PinFrame (M:=M) g (localOutput G r H l C b s slot j) (fun v t=>encodeRoot r l (x v t)) m) :
    let count:=hosts*chunks groups M
    let dst:=image out count (lookup g) m
    (program g out hosts groups M w).Exec m dst (4+count*(2*(lookup g).work+4)) ∧
    ∀v i,digit (outputBits G r H l C b) (lane i positive).val (dst (out+(row hosts groups M (position v i positive)).val)).val=
      (x v i).elim 0 (fun t=>«fields» G r H C b s slot t.1.val t.2.val j) := by
  let value:=localOutput G r H l C b s slot j
  let data (v : Fin hosts) (i : Fin groups) := encodeRoot r l (x v i)
  let dst:=image out (hosts*chunks groups M) (lookup g) m
  have safe : (lookup g).Fits w out:=⟨⟨fit.dictionary,fit.source,trivial⟩,fit.mask,trivial⟩
  have atRow (z : Row hosts groups M) : dst (out+(row hosts groups M z).val)=((masked value data z:ℕ):Word w):=
    (ProtocolRAMGeneratedWrite.read_image out (hosts*chunks groups M) (lookup g) m (row hosts groups M z)).trans
      (lookup_read g out fit value data m pins z)
  exact ⟨scan_exec out (hosts*chunks groups M) (lookup g) m safe fit.output,fun v i=>(physical_read g out fit value data dst atRow v i positive).trans
    (local_read G r H l C b s slot j (x v i))⟩

theorem clock (g : DescentSIMDLookup.Banks) (hosts groups r H l C b W arity K : ℕ)
    (wide : 2*max (inputBits r l) (outputBits G r H l C b)≤arity) (word : W≤K*arity) :
    let sz:=max (inputBits r l) (outputBits G r H l C b);let M:=lanes arity sz
    (4+(hosts*chunks groups M)*(2*(lookup g).work+4))*W≤K*(4*arity+44*(hosts*arity+4*hosts*groups*sz)) := by
  apply DescentPackedPayloadBudget.clock word
  have pos : 0 < inputBits r l := Nat.zero_lt_succ _
  exact (invoice g hosts groups (inputBits r l) (outputBits G r H l C b) arity
    (lt_of_lt_of_le pos (le_max_left _ _)) wide).1

end
end Hierarchy.DescentPackedRotorPanel

end OAI
