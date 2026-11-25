import OAI.Hierarchy.ProbeStageRowNative
import OAI.Hierarchy.ProbeStageAdviceSize

namespace OAI
/-! # Advice layout and address space for a native subdivision pass -/

namespace Hierarchy.ProbeStage.Native
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM DescriptorExpr PhysicalProcedure
open scoped Fin.CommRing

def lane (e j : ℕ) : Bank := ⟨j*2^e,e⟩
def inputBanks (e : ℕ) : Inputs := ⟨lane e 0,lane e 1,lane e 2,lane e 3,lane e 4,lane e 5⟩
def tableBanks (e : ℕ) : Tables := ⟨lane e 6,lane e 7,lane e 8,lane e 9,lane e 10,lane e 11⟩
def destination (e : ℕ) := 12*2^e

def tableAtIndex {k : ℕ} (f : Fin k → ℕ) (i : ℕ) := if hi : i<k then f ⟨i,hi⟩ else 0

/-- Static values in the six advice banks. They use only dimensions and do
not depend on permutations, colors or ranks. -/
def tableWords (groups m B : ℕ) (pos : 0<B) : Fin 6 → ℕ → ℕ := ![
  tableAtIndex (fun i : Fin groups => blocks m B*i.val),
  tableAtIndex (fun i : Fin groups => B*i.val),
  tableAtIndex (fun i : Fin m => (decode m B pos i).1.val),
  tableAtIndex (fun i : Fin m => (decode m B pos i).2.val),
  tableAtIndex (fun i : Fin B => quota B*i.val),
  tableAtIndex (fun i : Fin (blocks m B) => quota B*i.val)]

/-- Entering data and ranks remain in their dynamic banks. The static
advice occupies exactly six other banks. -/
def withTables {w : ℕ} (e groups m B : ℕ) (pos : 0<B) (mem : Memory w) : Memory w :=
  fun a =>
    let j := a/2^e
    if h : 6≤j ∧ j<12 then (tableWords groups m B pos ⟨j-6,by omega⟩ (a%2^e) : Word w)
    else mem a

private theorem lane_values {w e groups m B : ℕ} (pos : 0<B) (mem : Memory w) (j : Fin 6) (r : ℕ)
    (offset : r < 2^e) : withTables e groups m B pos mem ((6+j.val)*2^e+r) =
      (tableWords groups m B pos j r : Word w) := by
  have nz : 0<2^e := pow_pos (by decide) _
  have a : ((6+j.val)*2^e+r)/2^e = 6+j.val := by
    rw [Nat.mul_comm (6+j.val) (2^e),Nat.mul_add_div nz, Nat.div_eq_of_lt offset, Nat.add_zero]
  have b : ((6+j.val)*2^e+r)%2^e = r := by simp [Nat.add_mod, Nat.mod_eq_of_lt offset]
  simp [withTables,a,b,show 6+j.val<12 by omega]

structure InputCells {n m B groups w : ℕ} {G : Type} (p : Tiles (Fin n) G m) (pos : 0<B)
    (a : Allocation B (leftBlock p pos) (rightBlock p pos)) (encode : G ↪ Fin groups)
    (e : ℕ) (mem : Memory w) : Prop where
  group : ∀ r, mem (0*2^e+r.val) = ((encode (p.group r)).val : Word w)
  input : ∀ r, mem (1*2^e+r.val) = ((p.input r).val : Word w)
  output : ∀ r, mem (2*2^e+r.val) = ((p.output r).val : Word w)
  color : ∀ r, mem (3*2^e+r.val) = ((a.color r).val : Word w)
  enter : ∀ r, mem (4*2^e+r.val) = ((a.enterRank r).val : Word w)
  exit : ∀ r, mem (5*2^e+r.val) = ((a.exitRank r).val : Word w)

private theorem before_table {w e groups m B : ℕ} (pos : 0<B) (mem : Memory w) {j r : ℕ}
    (slot : j<6) (offset : r<2^e) :
    withTables e groups m B pos mem (j*2^e+r) = mem (j*2^e+r) := by
  have nz : 0<2^e := pow_pos (by decide) _
  have a : (j*2^e+r)/2^e=j := by rw [Nat.mul_comm j (2^e),Nat.mul_add_div nz,Nat.div_eq_of_lt offset,Nat.add_zero]
  simp [withTables,a,show ¬6≤j by omega]

theorem fixed_advice_loaded {n m B groups e : ℕ} {G : Type}
    (p : Tiles (Fin n) G m) (pos : 0<B) (a : Allocation B (leftBlock p pos) (rightBlock p pos))
    (encode : G ↪ Fin groups) (mem : Memory (e+5)) (read : InputCells p pos a encode e mem)
    (nr : n≤2^e) (gr : groups≤2^e) (mr : m≤2^e) (br : B≤2^e) (kr : blocks m B≤2^e) :
    Loaded p pos a encode (inputBanks e) (tableBanks e) (withTables e groups m B pos mem) := by
  have wide : 2^e≤2^(e+5) := Nat.pow_le_pow_right (by decide) (by omega)
  have Input {f : Fin n → ℕ} (j : ℕ) (hj : j<6)
      (cells : ∀ r, mem (j*2^e+r.val)=(f r : Word (e+5))) :
      Resident (lane e j) (withTables e groups m B pos mem) f := by
    apply Resident.of_cells _ _ _ nr (nr.trans wide)
    intro r
    exact (before_table pos mem hj (r.isLt.trans_le nr)).trans (cells r)
  have Table {k : ℕ} (kk : k≤2^e) (j : Fin 6) (f : Fin k → ℕ)
      (vals : ∀ i,tableWords groups m B pos j i.val=f i) :
      Resident (lane e (6+j.val)) (withTables e groups m B pos mem) f := by
    apply Resident.of_cells _ _ _ kk (kk.trans wide)
    intro i
    exact (lane_values pos mem j i.val (i.isLt.trans_le kk)).trans (congrArg (fun z : ℕ => (z:Word (e+5))) (vals i))
  refine ⟨Input 0 (by decide) read.group,Input 1 (by decide) read.input,Input 2 (by decide) read.output,
    Input 3 (by decide) read.color,Input 4 (by decide) read.enter,Input 5 (by decide) read.exit,?_,?_,?_,?_,?_,?_⟩
  · exact Table gr 0 _ (fun i => by simp [tableWords,tableAtIndex,i.isLt])
  · exact Table gr 1 _ (fun i => by simp [tableWords,tableAtIndex,i.isLt])
  · exact Table mr 2 _ (fun i => by simp [tableWords,tableAtIndex,i.isLt])
  · exact Table mr 3 _ (fun i => by simp [tableWords,tableAtIndex,i.isLt])
  · exact Table br 4 _ (fun i => by simp [tableWords,tableAtIndex,i.isLt])
  · exact Table kr 5 _ (fun i => by simp [tableWords,tableAtIndex,i.isLt])

private theorem lane_fit (e j : ℕ) (small : j<12) : (lane e j).Fits (e+5) (destination e) := by
  have pow : 0<2^e := pow_pos (by decide) _
  have bound := Nat.mul_le_mul_right (2^e) (show j+1≤12 by omega)
  rw [Nat.succ_mul] at bound
  exact ⟨pow,by change 2^e<2^(e+5);rw [pow_add];omega,bound⟩

theorem field_fits (e : ℕ) (j : Fin 9) :
    (field (inputBanks e) (tableBanks e) j).Fits (e+5) (destination e) := by
  fin_cases j <;>
    simp (disch:=decide) [field,rowAdd,rowCell,inputBanks,tableBanks,Expr.Fits,lane_fit]

/-- The concrete advice and register width make the native memory and
address-fit obligations uniform in the matching. -/
theorem emit_fixed {n m B groups e : ℕ} {G : Type}
    (p : Tiles (Fin n) G m) (pos : 0<B) (a : Allocation B (leftBlock p pos) (rightBlock p pos))
    (encode : G ↪ Fin groups) (mem : Memory (e+5)) (read : InputCells p pos a encode e mem)
    (nr : n≤2^e) (gr : groups≤2^e) (mr : m≤2^e) (br : B≤2^e) (kr : blocks m B≤2^e) :
    let data := withTables e groups m B pos mem
    let ps := passes (inputBanks e) (tableBanks e) (destination e) n
    (program (e+5) ps).Exec data (result ps data) (clock ps) ∧
      ∀ (r : Fin n) (j : Fin 9), result ps data (destination e+j.val*n+r.val) =
        (rowWords p pos a encode r j : Word (e+5)) := by
  let data := withTables e groups m B pos mem
  apply emit p pos a encode (inputBanks e) (tableBanks e) data
    (fixed_advice_loaded p pos a encode mem read nr gr mr br kr) (src:=destination e) _ le_rfl (field_fits e)
  apply columns_safe _ le_rfl
  · intro term member
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp member
    exact field_fits e i
  · simp only [List.length_ofFn,destination,pow_add]
    have nonzero : 0<2^e := pow_pos (by decide) _
    omega

/-- A dyadic phase takes O(2^h) steps on words of h+O_d(1) bits.
The actual row and advice extents are discharged from the subdivision
dimensions; the input cells are precisely the previous parent and rank data. -/
theorem dyadic_emit {h d j : ℕ} (hd : 1≤d) (hj : j≤rounds d) {G : Type}
    (p : Tiles (Fin (2^h)) G (2^widthLog h d j))
    (a : Allocation (radix h d) (leftBlock p (radix_pos h d)) (rightBlock p (radix_pos h d)))
    (encode : G ↪ Fin ((radix h d)^j)) (mem : Memory (roomBits h d+5))
    (read : InputCells p (radix_pos h d) a encode (roomBits h d) mem) :
    let e := roomBits h d
    let data := withTables e ((radix h d)^j) (2^widthLog h d j) (radix h d) (radix_pos h d) mem
    let ps := passes (inputBanks e) (tableBanks e) (destination e) (2^h)
    (program (e+5) ps).Exec data (result ps data) (clock ps) ∧ clock ps ≤ 40+612*2^h ∧
      ∀ (r : Fin (2^h)) (k : Fin 9), result ps data (destination e+k.val*2^h+r.val) =
        (rowWords p (radix_pos h d) a encode r k : Word (e+5)) := by
  obtain ⟨nr,gr,mr,br,kr⟩ := room_extents (h:=h) hd hj
  obtain ⟨exec,result⟩ := emit_fixed p (radix_pos h d) a encode mem read nr gr mr br kr
  refine ⟨exec,?_,result⟩
  exact (clock_bound ..).trans_eq (by ring)

end Hierarchy.ProbeStage.Native

end OAI
