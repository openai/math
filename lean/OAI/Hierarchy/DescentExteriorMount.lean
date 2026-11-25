import OAI.Hierarchy.DescentExteriorShelf
import OAI.Hierarchy.DescentExteriorContent
import OAI.Hierarchy.DescentTerminalScanFacts

namespace OAI
/-! # Readback of the single installed exterior advice and the dynamically filled key bank -/
namespace Hierarchy.DescentExteriorShelf
open DescentExterior DescentExteriorFetch DescentGL Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {j r t e w : ℕ} (origin : ℕ) (M : Fin e→Layout (j+(j+r))) (x : Fin e→Plane j r→Fin t→Bool)
    (z : Hidden e j r t→Bool) (m : Memory w) (loads : Loaded origin M x z m)
local notation "R" => 2^(j+r)
local notation "n" => e*R
local notation "K" => 2^(keyBits j r)
local notation "D" => 2^(2^j*t)
local notation "shelf" => span j r t e
local notation "B" => bank j r t e origin
local notation "I" => Fin n

private theorem keys_le : K≤ shelf :=
  (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)).trans (rom_room j r t e)

private theorem matrices_le : 2^((j+(j+r))*(j+(j+r)))≤ shelf :=
  (Nat.pow_le_pow_right (by decide) (Nat.le_add_right _ _)).trans (keys_le (j:=j) (r:=r) (t:=t) (e:=e))

private theorem tables_le : K*D≤ shelf := by rw [←pow_add]; exact rom_room j r t e

include loads in
theorem key_input : KeyInputs (keyBanks j r t e origin) M m := by
  have index₀ : (0 : Fin 17).val=0 := by decide
  have index₁ : (1 : Fin 17).val=1 := by decide
  have index₂ : (2 : Fin 17).val=2 := by decide
  have index₃ : (3 : Fin 17).val=3 := by decide
  have rr:=row_room j r t e
  refine ⟨fun i=>?_,fun a=>?_,fun k=>?_,fun i=>?_⟩
  · simpa only [keyBanks,columnWords,Matrix.cons_val,padWord_at,index₀] using loads 0 i.val (i.isLt.trans_le rr)
  · have er : e≤n:=Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
    simpa only [keyBanks,columnWords,Matrix.cons_val,padWord_at,index₁] using loads 1 a.val (a.isLt.trans_le (er.trans rr))
  · simpa only [keyBanks,columnWords,Matrix.cons_val,padWord_at,index₂] using
      loads 2 k.val (k.isLt.trans_le (matrices_le (j:=j) (r:=r)))
  · simpa only [keyBanks,columnWords,Matrix.cons_val,padWord_at,index₃] using loads 3 i.val (i.isLt.trans_le rr)

local notation "primed" => image (keyAt j r t e origin) n (joinKey (keyBanks j r t e origin)) m

include loads in
theorem below_key (i : Fin 17) (a : ℕ) (h : a<shelf) :
    primed ((B i.val).base+a)=columnWords M x z i a := by
  have step:=Nat.mul_le_mul_right shelf i.isLt
  rw [Nat.succ_mul] at step
  have less : (B i.val).base+a<keyAt j r t e origin := by change origin+i.val*shelf+a<origin+17*shelf;omega
  exact (DescentTerminalChipRuntime.image_low m (keyAt j r t e origin) n
    (joinKey (keyBanks j r t e origin)) less).trans (loads i a h)

theorem layout_ready (endRoom : origin+19*shelf<2^w) :
    (∀b∈(keyBanks j r t e origin).all,b.Fits w (keyAt j r t e origin)) ∧
    ∀s,Capacity (gatherBanks j r t e origin s) w j r t e (start j r t e origin) := by
  have low : origin+(17+1)*shelf<2^w := by omega
  have hi : origin+(18+1)*shelf<2^w := endRoom
  refine ⟨?_,fun s=>?_⟩
  · intro b hb
    simp [KeyBanks.all,keyBanks] at hb
    rcases hb with eq|eq|eq|eq <;> subst b <;> apply fit_to <;> first | decide | exact low
  · refine ⟨?_,row_room ..,row_room ..,keys_le,keys_le,row_room ..,tables_le⟩
    intro b hb
    simp only [Banks.all,gatherBanks,List.mem_cons,List.not_mem_nil,or_false] at hb
    have hs:=s.isLt
    rcases hb with eq|eq|eq|eq|eq|eq <;> subst b <;> apply fit_to <;> first | exact hi | omega

include loads in
theorem actual_key (endRoom : origin+19*shelf<2^w) (i : I) :
    primed ((B 17).base+i.val)=((encoded M i).val:Word w) := by
  let kb:=keyBanks j r t e origin
  have keyOk:=(layout_ready (j:=j) (r:=r) (t:=t) (e:=e) origin endRoom).1
  have rr:=row_room j r t e
  have er : e≤n:=Nat.le_mul_of_pos_right _ (Nat.two_pow_pos _)
  have one:=key_read kb keyOk rr (er.trans rr) matrices_le rr M m (key_input origin M x z m loads) i
  exact (DescentTerminalChipRuntime.image_at m (keyAt j r t e origin) n (joinKey kb) i).trans one

include loads in
theorem inputs (endRoom : origin+19*shelf<2^w) (s : Fin 3) :
    Inputs (gatherBanks j r t e origin s) s M (passInputs x z s) primed := by
  have frame:=below_key origin M x z m loads
  have rr:=row_room j r t e
  refine ⟨actual_key origin M x z m loads endRoom,fun i=>?_,fun a=>?_,fun a=>?_,fun a v=>?_,fun a b=>?_⟩
  · let starts (v : I) : Word w := (((slab (j:=j) (r:=r) v).val*R:ℕ):Word w)
    have field : columnWords (w:=w) M x z 4=padWord starts := rfl
    have got:=frame 4 i.val (i.isLt.trans_le rr)
    rw [field,padWord_at] at got
    exact got
  · have got:=frame ⟨5+s.val,by have:=s.isLt;omega⟩ _ (a.isLt.trans_le keys_le)
    fin_cases s <;> simpa [columnWords,dir,gatherBanks] using got
  · let offsets (v : Fin K) : Word w := ((v.val*D:ℕ):Word w)
    have field : columnWords (w:=w) M x z 8=padWord offsets := rfl
    have got:=frame 8 a.val (a.isLt.trans_le keys_le)
    rw [field,padWord_at] at got
    exact got
  · let i:I:=finProdFinEquiv (a,rowOrd j r v)
    have addr : i.val=a.val*R+(rowOrd j r v).val := by change _+R*a.val=_;ring
    let raw (p : Fin 3) (u : I) : Word w :=
      ((pack (fun l=>passInputs x z p (slab u) (l,dest u))).val:Word w)
    have field (p : Fin 3) : columnWords (w:=w) M x z ⟨9+p.val,by have:=p.isLt;omega⟩=padWord (raw p) := by
      fin_cases p <;> rfl
    have got:=frame ⟨9+s.val,by have:=s.isLt;omega⟩ i.val (i.isLt.trans_le rr)
    rw [field,padWord_at] at got
    rw [←addr]
    simpa only [gatherBanks,raw,slab,dest,i,Equiv.symm_apply_apply] using got
  · let i:Fin (K*D):=finProdFinEquiv (a,b)
    have addr : i.val=a.val*D+b.val := by change _+D*a.val=_;ring
    have got:=frame ⟨12+s.val,by have:=s.isLt;omega⟩ _ (i.isLt.trans_le tables_le)
    rw [addr] at got
    fin_cases s <;> simpa [columnWords,gatherBanks,permROM_read] using got

include loads in
theorem expected (s : Fin 2) (i : I) :
    primed ((guesses j r t e origin s).base+i.val)=
      ((gathered z (phase s,false,slab i,dest i)).val:Word w) := by
  have h:=below_key origin M x z m loads ⟨15+s.val,by have:=s.isLt;omega⟩ _ (i.isLt.trans_le (row_room ..))
  fin_cases s <;> simpa [guesses,columnWords] using h

end
end Hierarchy.DescentExteriorShelf

end OAI
