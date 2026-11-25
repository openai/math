import OAI.Computability.NearSquareRoot.CRTPositionBorrowRows
import OAI.Computability.NearSquareRoot.CRTControlledSizes
import OAI.Computability.NearSquareRoot.CRTControlledTrimmed
import OAI.Computability.NearSquareRoot.CRTControlledResidues
import OAI.Computability.IntegerMultiplication.Staff.Nat
import OAI.Computability.IntegerMultiplication.Strip.Steps

/-! # A compiled residue pass between three contiguous chunks

In MSB order the chunks are source, destination and spectator. The bit numbering
inside each chunk is little-endian. Slots in the guarded row are stored in the
opposite order, which is accounted for by the selector on its input tape.
-/

namespace OAI
namespace Computability
namespace NearSquareRoot

namespace Controlled
open IntegerMultiplication IntegerMultiplication.Packed IntegerMultiplication.Adic
open IntegerMultiplication.Code IntegerMultiplication.Loom IntegerMultiplication.Strip

noncomputable section

abbrev crossWidth (N : ℕ) := N + N + N

def crossPort (N : ℕ) (cj : Fin 3 × Fin N) : Fin (crossWidth N) :=
  ⟨(2-cj.1.val)*N+cj.2.val,by
    obtain ⟨c,j⟩ := cj
    fin_cases c <;> simp [crossWidth] <;> omega⟩

def crossBits {N : ℕ} (y : Block 2 (crossWidth N)) (cj : Fin 3 × Fin N) :=
  prefixBit y (crossPort N cj)

theorem crossPort_surjective (N : ℕ) : Function.Surjective (crossPort N) := by
  intro n
  by_cases lo : n.val < N
  · exact ⟨(2,⟨n,lo⟩),by apply Fin.ext; simp [crossPort]⟩
  by_cases mid : n.val < N+N
  · exact ⟨(1,⟨n-N,by omega⟩),by apply Fin.ext; simp [crossPort]; omega⟩
  have full : n.val < N+N+N := n.isLt
  exact ⟨(0,⟨n-(N+N),by omega⟩),by apply Fin.ext; simp [crossPort,two_mul]; omega⟩

/-- Agreement on all three chunks determines the whole flat input to the next
record-routing pass. -/
theorem crossBits_injective {N : ℕ} : Function.Injective (@crossBits N) := by
  intro x y h
  have p : prefixBit x = prefixBit y := by
    funext n
    obtain ⟨a,rfl⟩ := crossPort_surjective N n
    exact congrFun h a
  have hd : least x = least y := by
    apply List.ext_getElem
    · simp
    · intro j hj hk
      have h₀ : j < crossWidth N := by simpa only [length'] using hj
      exact title_identify (congrFun p ⟨j,h₀⟩)
  exact distinct _ _ (by simpa only [least,List.reverse_inj] using hd)

private def lowRead {N : ℕ} (read : Fin N → Option (Fin N)) (G j : ℕ) :=
  if hj : j < N ∧ j+2*G ≤ N then read ⟨j,hj.1⟩ else none

def crossRead {N : ℕ} (read : Fin N → Option (Fin N)) (G r : ℕ)
    (q : Fin (slots N G r)) : Option (Fin N) :=
  lowRead read G (r+q.rev.val*G)

theorem crossFit {N G r : ℕ} (hG : 0 < G) (fit : r+G ≤ N) :
    r + cap (slots N G r) (G-1) 0 ≤ N := by
  have h₁ : 1 ≤ (N-r)/G := (Nat.le_div_iff_mul_le hG).2 (by omega)
  have h₂ := Nat.div_mul_le_self (N-r) G
  simp only [cap,width,Nat.add_zero,slots,Nat.sub_add_cancel hG,
    Nat.sub_add_cancel h₁]
  omega

private def crossControl {N : ℕ} (read : Fin N → Option (Fin N)) (G r n : ℕ) :=
  let b := n-(N+r)
  if h : N+r ≤ n ∧ b/G < slots N G r ∧ b%G = 0 then
    crossRead read G r (⟨b/G,h.2.1⟩ : Fin _).rev
  else none

private theorem lowRead_of_slot {N : ℕ} (read : Fin N → Option (Fin N)) (G r n : ℕ)
    (h : N+r ≤ n ∧ (n-(N+r))/G < slots N G r ∧ (n-(N+r))%G=0) :
    crossControl read G r n = lowRead read G (n-N) := by
  have eq := Nat.div_add_mod' (n-(N+r)) G
  rw [h.2.2,Nat.add_zero] at eq
  have e : r+(n-(N+r))/G*G = n-N := by omega
  simp [crossControl,h,crossRead,e]

private theorem middleControl {N G r : ℕ} (read : Fin N → Option (Fin N))
    (hg : 0 < G) (hr : r < G) (j : Fin N) :
    crossControl read G r (N+j) = if residuePass G j = r then read j else none := by
  by_cases bound : j.val + 2*G ≤ N
  · simp only [residuePass,ite_eq_left bound]
    by_cases rem : j.val%G = r
    · have eq := Nat.div_add_mod' j.val G
      rw [rem] at eq
      have e : N + j.val - (N+r) = (j.val/G)*G := by omega
      have div : (N+j.val-(N+r))/G = j.val/G := by rw [e,Nat.mul_div_cancel _ hg]
      have mod : (N+j.val-(N+r))%G = 0 := by rw [e]; simp
      have q := residue_slot hg j bound
      rw [rem] at q
      have h := lowRead_of_slot read G r (N+j) ⟨by omega,div ▸ q,mod⟩
      simpa [rem,lowRead,j.isLt,bound] using h
    · rw [ite_eq_right rem]
      unfold crossControl
      dsimp only
      split
      · rename_i h
        have e := Nat.div_add_mod' (N+j.val-(N+r)) G
        rw [h.2.2,Nat.add_zero] at e
        have pos : j.val = r+((N+j.val-(N+r))/G)*G := by omega
        have m := congrArg (· % G) pos
        simp only [Nat.add_mul_mod_self_right,Nat.mod_eq_of_lt hr] at m
        exact (rem m).elim
      · rfl
  · have neq : residuePass G j ≠ r := by simp [residuePass,bound]; omega
    rw [ite_eq_right neq]
    unfold crossControl
    dsimp only
    split
    · rename_i h
      have e := Nat.div_add_mod' (N+j.val-(N+r)) G
      rw [h.2.2,Nat.add_zero] at e
      have pos : r+((N+j.val-(N+r))/G)*G = j.val := by omega
      simp [crossRead,pos,lowRead,bound]
    · rfl

private theorem highControl {N G r : ℕ} (read : Fin N → Option (Fin N)) (n : ℕ)
    (hn : N+N ≤ n) : crossControl read G r n = none := by
  by_cases h : N+r ≤ n ∧ (n-(N+r))/G < slots N G r ∧ (n-(N+r))%G=0
  · rw [lowRead_of_slot read G r n h]
    simp [lowRead,show ¬n-N < N by omega]
  · simp [crossControl,h]

private theorem noFit_pass {N G r : ℕ} (hr : r < G) (no : ¬ r+G ≤ N) (j : Fin N) :
    residuePass G j ≠ r := by
  have noLow : ¬ j.val+2*G ≤ N := by omega
  simp [residuePass,noLow]; omega

/-- The actual trimmed packed row, or the identity when even its leading chunk
does not fit. -/
def crossResidueMask {N G r : ℕ} (hg : 0 < G) (read : Fin N → Option (Fin N))
    (y : Block 2 (crossWidth N)) : Block 2 (crossWidth N) :=
  if h : r+G ≤ N then trimmedMask N N 0 0 r (crossFit hg h) (crossRead read G r) y else y

private theorem sourcePort {N : ℕ} (q : Fin N) :
    wholePrefixPort N N 0 0 q = crossPort N (0,q) := by
  apply Fin.ext
  simp [wholePrefixPort,crossPort,two_mul]

private theorem trimmedControl_bit {N G r : ℕ} (hg : 0 < G) (fit : r+G ≤ N)
    (read : Fin N → Option (Fin N)) (y : Block 2 (crossWidth N)) (n : Fin (crossWidth N)) :
    prefixBit (crossResidueMask (r := r) hg read y) n =
      (prefixBit y n ^^ ((crossControl read G r n).map (fun q => crossBits y (0,q))).getD false) := by
  let z := trimmedMask N N 0 0 r (crossFit hg fit) (crossRead read G r) y
  unfold crossResidueMask
  rw [dite_eq_left fit]
  change prefixBit z n = _
  have eq := trimmedMask_slot N N 0 0 r (crossFit hg fit) (crossRead read G r) y n
  have hk : G-1+1=G := by omega
  simp only [Nat.zero_add,Nat.add_zero,hk,sourcePort] at eq
  change (least z)[n.val]? = _ at eq
  have hlen (x : Block 2 (crossWidth N)) : n.val < (least x).length := by simp
  rw [List.getElem?_eq_getElem (hlen z),List.getElem?_eq_getElem (hlen y)] at eq
  unfold prefixBit crossControl
  dsimp only
  split
  · rename_i e
    rw [dite_eq_left e] at eq
    have th := congrArg title (Option.some.inj eq)
    have digit (v : Bool) : title (maskDigit v) = v := by cases v <;> rfl
    simpa only [digit,crossBits,prefixBit] using th
  · rename_i e
    rw [dite_eq_right e] at eq
    simpa only [Option.map_none,Option.getD_none,Bool.xor_false] using congrArg title (Option.some.inj eq)

/-- The serialized opcode can read a source position more than once. Every
destination still sees the original source chunk because that chunk is read only. -/
theorem crossResidueMask_read {N G r : ℕ} (hg : 0 < G) (hr : r < G)
    (read : Fin N → Option (Fin N)) (y : Block 2 (crossWidth N)) (c : Fin 3) (j : Fin N) :
    crossBits (crossResidueMask (r := r) hg read y) (c,j) =
      if c = 1 then xorFrom (fun j => if residuePass G j = r then read j else none)
        (fun q => crossBits y (0,q)) (fun q => crossBits y (1,q)) j else crossBits y (c,j) := by
  by_cases fit : r+G ≤ N
  · rw [crossBits,trimmedControl_bit hg fit]
    fin_cases c
    · have h : N+N ≤ (crossPort N (0,j)).val := by simp [crossPort,two_mul]
      simp [highControl _ _ h,crossBits]
    · have h : (crossPort N (1,j)).val = N+j := by simp [crossPort]
      change (prefixBit y (crossPort N (1,j)) ^^ ((crossControl read G r (crossPort N (1,j))).map
        (fun q => crossBits y (0,q))).getD false) = _
      rw [h,middleControl _ hg hr]
      by_cases e : residuePass G j = r <;> cases f : read j <;> simp [xorFrom,e,f,crossBits]
    · have h : ¬N+r ≤ (crossPort N (2,j)).val := by simp [crossPort]; omega
      simp [crossControl,h,crossBits]
  · by_cases h : c = 1 <;> simp [crossResidueMask,fit,noFit_pass hr fit,xorFrom,h]

theorem crossResidueMask_bits {N G r : ℕ} (hg : 0 < G) (hr : r < G)
    (g : PositionXor (Fin 3) (Fin N)) (hs : g.src = 0) (hd : g.dst = 1)
    (y : Block 2 (crossWidth N)) :
    crossBits (crossResidueMask (r := r) hg g.read y) = (g.filterPass G r).act (crossBits y) := by
  funext ⟨c,j⟩
  rw [crossResidueMask_read hg hr]
  by_cases h : c = 1 <;> simp [PositionXor.act,PositionXor.filterPass,hd,hs,h,xorFrom]
  cases (if residuePass G j = r then g.read j else none) <;> rfl

theorem PositionXor.act_involutive {C B : Type} [DecidableEq C] (g : PositionXor C B) :
    Function.Involutive g.act := by
  intro w
  funext ⟨c,j⟩
  by_cases h : c = g.dst
  · cases e : g.read j with
    | none => simp [PositionXor.act,h,e]
    | some b =>
      simp only [PositionXor.act,h,ite_true,e,ite_eq_right g.different]
      cases w (g.dst,j) <;> cases w (g.src,b) <;> rfl
  · simp [PositionXor.act,h]

/-- The flat operation is a permutation of every full address, so it can be used
directly as an invertible stage in the physical scheduler. -/
def crossResiduePerm {N G r : ℕ} (hg : 0 < G) (hr : r < G)
    (g : PositionXor (Fin 3) (Fin N)) (hs : g.src = 0) (hd : g.dst = 1) :
    Equiv.Perm (Block 2 (crossWidth N)) :=
  let action := crossResidueMask (r := r) hg g.read
  let inv : Function.Involutive action := fun y => crossBits_injective (by
    change crossBits (crossResidueMask (r := r) hg g.read (crossResidueMask (r := r) hg g.read y)) = _
    rw [crossResidueMask_bits hg hr g hs hd,crossResidueMask_bits hg hr g hs hd]
    exact (g.filterPass G r).act_involutive _)
  ⟨action,action,inv,inv⟩

open IntegerMultiplication.Staff

private abbrev SlotHeader := Tally × Tally × Tally × List Tally
private abbrev SlotInput := SlotHeader × Tally
private def slotIndex (q : SlotInput) := q.1.2.2.1.length + q.2.length * q.1.2.1.length
private def slotCode (q : SlotInput) : Tally :=
  if q.1.1.length < slotIndex q + 2*q.1.2.1.length then q.1.1
  else (q.1.2.2.2.drop (slotIndex q)).headD []

private theorem slotCode_poly : Poly slotCode := by
  let reg : Regime SlotInput := ⟨size,send,Dom.base _⟩
  have num (f : SlotInput → Tally) (h : Poly f) : Realizes reg (fun q => (f q).length) := by
    change Poly (fun q => tally (f q).length)
    simpa only [recover_tally] using h
  have n := num (fun q => q.1.1) (by fun_prop)
  have g := num (fun q => q.1.2.1) (by fun_prop)
  have r := num (fun q => q.1.2.2.1) (by fun_prop)
  have a : Realizes reg slotIndex := r.plus ((num Prod.snd Easy.snd.poly).times g)
  have c := a.plus ((Realizes.fix 2).times g)
  have hb : Poly (fun q : SlotInput => decide (q.1.1.length < slotIndex q + 2*q.1.2.1.length)) := by
    have h := (Regime.Has.pair n c).ez (Iter.small_easy (X := Unit) (Y := Unit))
    change Poly _ at h
    simpa only [Function.comp_def,Iter.small,tally_length] using h
  have cut := ((show Poly (fun q => tally (slotIndex q)) from a).pair
    (show Poly (fun q : SlotInput => q.1.2.2.2) by fun_prop)).compose (easy_cut Easy.identity).poly
  have get := cut.sndCompose.compose (Iter.leader ([] : Tally)).poly
  have sel := Poly.choose hb (show Poly (fun q : SlotInput => q.1.1) by fun_prop) get
  convert sel using 1
  funext q
  by_cases e : q.1.1.length < slotIndex q + 2*q.1.2.1.length <;>
    simp [slotCode,e,cutLists]

private theorem slotCode_valid {N G r : ℕ} (hg : 0 < G) (read : Fin N → Option (Fin N))
    (q : Fin (slots N G r)) :
    slotCode ((tally N,tally G,tally r,List.ofFn fun j => tally (((read j).map Fin.val).getD N)),tally q.rev.val) =
      tally (((crossRead read G r q).map Fin.val).getD N) := by
  unfold slotCode slotIndex crossRead lowRead
  simp only [tally_length]
  by_cases low : r+q.rev.val*G+2*G ≤ N
  · have lt : r+q.rev.val*G < N := by omega
    have both := And.intro lt low
    simp only [ite_eq_right (Nat.not_lt.mpr low),dite_eq_left both,
      List.headD_eq_head?_getD,List.head?_drop,List.getElem?_ofFn,dite_eq_left lt,Option.getD_some]
  · have bad : ¬(r+q.rev.val*G < N ∧ r+q.rev.val*G+2*G ≤ N) := fun h => low h.2
    rw [ite_eq_left (Nat.lt_of_not_ge low),dite_eq_right bad]
    rfl

theorem crossReadHeader {X : Type} {R : Regime X} (N G r : X → ℕ)
    (read : (x : X) → Fin (N x) → Option (Fin (N x))) (hg : ∀ x, 0 < G x)
    (hN : Realizes R N) (hG : Realizes R G) (hr : Realizes R r)
    (tab : R.Has fun x => List.ofFn fun j => tally (((read x j).map Fin.val).getD (N x))) :
    R.Has fun x => List.ofFn fun j => tally (((crossRead (read x) (G x) (r x) j).map Fin.val).getD (N x)) := by
  have si : Realizes R (fun x => slots (N x) (G x) (r x)) :=
    (((hN.minused hr).dividing hG).minused (Realizes.fix 1))
  have q := ((Regime.Has.pair hN (Regime.Has.pair hG (Regime.Has.pair hr tab))).pair
    (Regime.Has.thenDo si (Iter.poly_line.compose Easy.reverse.poly))).thenDo
      (Poly.push ([],[],[],[]) [] slotCode_poly)
  convert q using 2 with x
  simp only [polyPush,Function.comp_apply]
  apply List.ext_getElem
  · simp
  · intro j hj hj'
    have hj₀ : j < slots (N x) (G x) (r x) := by simpa only [List.length_ofFn] using hj
    let ix : Fin (slots (N x) (G x) (r x)) := ⟨j,hj₀⟩
    rw [List.getElem_ofFn]
    change tally (((crossRead (read x) (G x) (r x) ix).map Fin.val).getD (N x)) = _
    rw [← slotCode_valid (r := r x) (hg x) (read x) ix]
    simp only [Iter.lineup,List.getElem_map,List.getElem_reverse,List.getElem_ofFn,
      List.length_ofFn,tally_length,Fin.rev,Fin.val_cast,ix]
    congr 3
    omega

/-- The actual guarded chunk width used on this residue. -/
def crossExtent (N G r : ℕ) := cap (slots N G r) (G-1) 0

theorem crossSparse {N G r k : ℕ} (hg : 0 < G) (fit : r+G ≤ N) (hn : N ≤ k) (guard : guardWidth k ≤ G) :
    (3 * crossExtent N G r + 1) * (32 * slots N G r) ≤ 2 ^ width (G-1) 0 := by
  have he : crossExtent N G r ≤ k := by have := crossFit hg fit; unfold crossExtent; omega
  have hi : slots N G r ≤ k := by have := Nat.div_le_self (N-r) G; unfold slots; omega
  have h := guardWidth_pays he hi
  exact h.trans (Nat.pow_le_pow_right (by decide) (show guardWidth k ≤ width (G-1) 0 by
    unfold width; omega))

/-- All dimensions and selector indices for an occupied pass are manufactured from
the three rulers and the table of the original position gate. -/
theorem crossResidueStage_fit {X : Type} {R : Regime X} {l : X → ℕ}
    (N G r : X → ℕ) (read : (x : X) → Fin (N x) → Option (Fin (N x)))
    (hg : ∀ x, 0 < G x) (fit : ∀ x, r x+G x ≤ N x)
    (hn : Realizes R N) (hG : Realizes R G) (hr : Realizes R r)
    (tab : R.Has fun x => List.ofFn fun j => tally (((read x j).map Fin.val).getD (N x)))
    (sparse : ∀ x, (3 * crossExtent (N x) (G x) (r x) + 1) * (32 * slots (N x) (G x) (r x)) ≤
        2 ^ width (G x-1) 0)
    (ρ : ℝ) (sw : RectInterchange R (fun x => crossExtent (N x) (G x) (r x)) ρ)
    {U : X → Type} (u : (x : X) → Series (U x)) (z : ∀ x, (u x).count ≤ l x) (hρ : 0 ≤ ρ)
    (f : (x : X) → Block 2 (crossWidth (N x)) → U x → Bead) :
    let flat x := line 2 (crossWidth (N x))
    Breeze (Spindle.modes (fun x => crossExtent (N x) (G x) (r x)) (τ := ρ))
      R (fun x => (flat x).count) l (together R.header (cloth flat u f))
      (cloth flat u fun x a => f x (crossResidueMask (r := r x) (hg x) (read x) a)) := by
  let H := fun x => G x-1
  let i := fun x => slots (N x) (G x) (r x)
  have hh : Realizes R H := hG.minused (Realizes.fix 1)
  have si : Realizes R i := ((hn.minused hr).dividing hG).minused (Realizes.fix 1)
  have c : Realizes R (extent H (fun _ => 0) i) :=
    (si.plus (Realizes.fix 1)).times ((hh.plus (Realizes.fix 1)).plus (Realizes.fix 0))
  have sh : R.Has (fun x => signs (H x) 0 (i x)) :=
    Regime.Has.pair hh (Regime.Has.pair (Realizes.fix 0) si)
  have run := trimmedSelectedStage H i N N (fun _ => 0) (fun _ => 0) r ρ u
    (fun x => crossRead (read x) (G x) (r x)) (fun x => crossFit (hg x) (fit x)) c sh sparse
    hn hn (Realizes.fix 0) (Realizes.fix 0) hr sw (crossReadHeader N G r read hg hn hG hr tab) z hρ f
  simpa only [crossResidueMask,dite_eq_left (fit _),extent,crossExtent,H,i,crossWidth,Nat.add_zero] using run

abbrev CrossFits {X : Type} (N G r : X → ℕ) := {x : X // r x + G x ≤ N x}

/-- One fixed P192 program covers every instance, including an empty source,
a short final residue, and the case in which no complete guarded chunk fits. -/
theorem crossResidueStage_atRate {X : Type} {R : Regime X} {l : X → ℕ}
    (N G r : X → ℕ) (read : (x : X) → Fin (N x) → Option (Fin (N x))) (hg : ∀ x, 0 < G x)
    (hn : Realizes R N) (hG : Realizes R G) (hr : Realizes R r)
    (tab : R.Has fun x => List.ofFn fun j => tally (((read x j).map Fin.val).getD (N x)))
    (sparse : ∀ x : CrossFits N G r,
      (3 * crossExtent (N x) (G x) (r x) + 1) * (32 * slots (N x) (G x) (r x)) ≤ 2 ^ width (G x-1) 0)
    (ρ : ℝ) (sw : RectInterchange (R.pull (Subtype.val : CrossFits N G r → X))
      (fun x => crossExtent (N x) (G x) (r x)) ρ)
    {U : X → Type} (u : (x : X) → Series (U x)) (z : ∀ x, (u x).count ≤ l x) (hρ : 0 ≤ ρ)
    (rate : X → ℝ) (positive : ∀ x, 1 ≤ rate x)
    (priced : ∀ x : CrossFits N G r, Spindle.modes (fun y => crossExtent (N y) (G y) (r y)) (τ := ρ) x.val ≤ rate x)
    (f : (x : X) → Block 2 (crossWidth (N x)) → U x → Bead) :
    let flat x := line 2 (crossWidth (N x))
    Breeze rate
      R (fun x => (flat x).count) l (together R.header (cloth flat u f))
      (cloth flat u fun x a => f x (crossResidueMask (r := r x) (hg x) (read x) a)) := by
  let yes : CrossFits N G r → X := Subtype.val
  let no : {x : X // N x < r x + G x} → X := Subtype.val
  let flat x := line 2 (crossWidth (N x))
  have hflat := terminal (p := 2) (by decide) (fun x => crossWidth (N x)) ((hn.plus hn).plus hn)
  have live := cloth_size flat u hflat f z
  obtain ⟨tag,ready,tagged⟩ := hn.below (hr.plus hG)
  have fork := ((Rip.header (l := l) hflat.1 ready).left live).split
  have cov (x : X) : (tag x = false → ∃ y, x = yes y) ∧ (tag x = true → ∃ y, x = no y) := by
    constructor
    · intro ef
      exact ⟨⟨x,Nat.le_of_not_gt (fun h => by simpa [ef] using (tagged x).1 h)⟩,rfl⟩
    · intro et
      exact ⟨⟨x,(tagged x).2 et⟩,rfl⟩
  apply classify_b tag fork.1 no yes cov
  · exact (crossResidueStage_fit (R := R.pull yes) (l := l ∘ yes) (N ∘ yes) (G ∘ yes) (r ∘ yes) (fun x => read x) (fun x => hg x)
      (fun x => x.property) (Task.BT.map hn yes) (Task.BT.map hG yes) (Task.BT.map hr yes)
      (Task.BT.map tab yes) sparse ρ sw (fun x => u x) (fun x => z x) hρ (fun x => f x)).raise priced
  · have idPass := (Breeze.launch fork.2 positive).along_cast no
    convert idPass using 1
    funext x
    change stripe _ (fun a => strip _ (f x.val (crossResidueMask (r := r x.val) (hg x.val) (read x.val) a))) = _
    simp only [crossResidueMask,dite_eq_right (Nat.not_le_of_gt x.property)]
    rfl

theorem crossResidueStage {X : Type} {R : Regime X} {l : X → ℕ}
    (N G r : X → ℕ) (read : (x : X) → Fin (N x) → Option (Fin (N x))) (hg : ∀ x, 0 < G x)
    (hn : Realizes R N) (hG : Realizes R G) (hr : Realizes R r)
    (tab : R.Has fun x => List.ofFn fun j => tally (((read x j).map Fin.val).getD (N x)))
    (sparse : ∀ x : CrossFits N G r,
      (3 * crossExtent (N x) (G x) (r x) + 1) * (32 * slots (N x) (G x) (r x)) ≤ 2 ^ width (G x-1) 0)
    (ρ : ℝ) (sw : RectInterchange (R.pull (Subtype.val : CrossFits N G r → X))
      (fun x => crossExtent (N x) (G x) (r x)) ρ)
    {U : X → Type} (u : (x : X) → Series (U x)) (z : ∀ x, (u x).count ≤ l x) (hρ : 0 ≤ ρ)
    (f : (x : X) → Block 2 (crossWidth (N x)) → U x → Bead) :
    let flat x := line 2 (crossWidth (N x))
    Breeze (Spindle.modes (fun x => crossExtent (N x) (G x) (r x)) (τ := ρ))
      R (fun x => (flat x).count) l (together R.header (cloth flat u f))
      (cloth flat u fun x a => f x (crossResidueMask (r := r x) (hg x) (read x) a)) := by
  exact crossResidueStage_atRate N G r read hg hn hG hr tab sparse ρ sw u z hρ _
    (Spindle.belly _ hρ) (fun _ => le_rfl) f

end
end Controlled

end NearSquareRoot
end Computability
end OAI
