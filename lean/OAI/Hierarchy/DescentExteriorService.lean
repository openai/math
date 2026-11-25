import OAI.Hierarchy.DescentExteriorMount
import OAI.Hierarchy.DescentExteriorInitialWires

namespace OAI
/-! # Physical native realization and price of the exterior reindexing -/
namespace Hierarchy.DescentExteriorShelf
open DescentExterior DescentExteriorFetch DescentGL Computability.VPVNP.BurstRAM PrivateRAM ProtocolRAM
open ThreeFlat.RAM PhysicalProcedure DescriptorExpr
open scoped Classical BigOperators Fin.CommRing
noncomputable section

variable {w e j r t : ℕ} (origin : ℕ)
local notation "R" => 2^(j+r)
local notation "n" => e*R
local notation "I" => Fin n
local notation "k" => j+(j+r)
local notation "H" => span j r t e
local notation "keyPos" => keyAt j r t e origin
local notation "first" => start j r t e origin
local notation "kb" => keyBanks j r t e origin
local notation "gg" => gatherBanks j r t e origin
local notation "gb" => guesses j r t e origin

def service (w j r t e origin : ℕ) : Procedure w :=
  flight w (keyAt j r t e origin) (start j r t e origin) (rows j r e)
    (keyBanks j r t e origin) (gatherBanks j r t e origin) (guesses j r t e origin)

/-- The same code and register widths work at every input size. The
layout and the advice reside in data memory. -/
theorem text_bound (w j r t e origin : ℕ) :
    (service w j r t e origin).labels=550 ∧
    (service w j r t e origin).registers=190 ∧ (service w j r t e origin).slots=0 := by
  have work₀ (g : Fin 3→Banks) (b : Fin 2→Bank) : (columns g b 0).work=53 := rfl
  have work₁ (g : Fin 3→Banks) (b : Fin 2→Bank) : (columns g b 1).work=53 := rfl
  have work₂ (g : Fin 3→Banks) (b : Fin 2→Bank) : (columns g b 2).work=43 := rfl
  simp only [service,flight,Procedure.seq,scan,PhysicalInputPhases.writing,
    Term.labels_eq,compile_binds,joinKey_work,work₀,work₁,work₂]
  decide

def Receipt (M : Fin e→Layout k) (x : Fin e→Plane j r→Fin t→Bool) (z : Hidden e j r t→Bool)
    (after : Memory w) : Prop :=
  ((∀s : Fin 2,∀i:I,after (first+s.val*n+i.val)=0) ↔ z=canonical M x) ∧
  ∀i:I,after (first+2*n+i.val)=
    ((pack (fun l=>output (M (slab i)) (projected z true (slab i)) (l,dest i))).val:Word w)

def serviceMemory (m : Memory w) := finalMem keyPos first n kb gg gb m

theorem native_exact (wordPos : 0<w) (wordRoom : 2^j*t≤w)
    (space : origin+22*H<2^w) (M : Fin e→Layout k)
    (x : Fin e→Plane j r→Fin t→Bool) (z : Hidden e j r t→Bool) :
    (service w j r t e origin).Spec (Loaded origin M x z)
      (fun m after=>after=serviceMemory (j:=j) (r:=r) (t:=t) (e:=e) origin m ∧ Receipt origin M x z after)
      (16+364*n) ∧ CheapCode (service w j r t e origin) := by
  have hp : 0<H:=Nat.two_pow_pos _
  have endRoom : origin+19*H<2^w := by omega
  obtain ⟨kfit,cap⟩:=layout_ready (j:=j) (r:=r) (t:=t) (e:=e) origin endRoom
  have keyFits : (joinKey kb).Fits w keyPos := by
    simp only [joinKey,Expr.Fits,kfit (kb).owner (by simp [KeyBanks.all]),
      kfit (kb).matrix (by simp [KeyBanks.all]),kfit (kb).offsets (by simp [KeyBanks.all]),
      kfit (kb).row (by simp [KeyBanks.all]),and_self]
  have guessFit (s : Fin 2) : (gb s).Fits w first :=
    fit_to j r t e origin (i:=15+s.val) (z:=18) (by have:=s.isLt;omega) endRoom
  have guessRows (s : Fin 2) : n≤(gb s).size := row_room j r t e
  have fits (s : Fin 3) : (gather (gg s)).Fits w first := by
    have all:=(cap s).fits
    simp only [gather,Expr.Fits,all (gg s).key (by simp [Banks.all]),
      all (gg s).slab (by simp [Banks.all]),all (gg s).source (by simp [Banks.all]),
      all (gg s).data (by simp [Banks.all]),all (gg s).offsets (by simp [Banks.all]),
      all (gg s).table (by simp [Banks.all]),and_self]
  have ready (s : Fin 3) : (columns gg gb s).Fits w first := by
    fin_cases s
    · exact ⟨fits 0,⟨guessFit 0,trivial⟩,trivial,trivial⟩
    · exact ⟨fits 1,⟨guessFit 1,trivial⟩,trivial,trivial⟩
    · exact fits 2
  have rr : n≤H := row_room j r t e
  have firstRoom : keyPos+n≤first := by change origin+17*H+n≤origin+18*H;omega
  have lastRoom : first+3*n<2^w := by change origin+18*H+3*n<2^w;omega
  refine ⟨?_,DescentExteriorFetch.cheap w keyPos first n kb gg gb⟩
  intro P X A machine pc reg pub exit rom «public» cfg m entry loads
  obtain ⟨cnt,paid,zf,out,ran,stop,eq⟩:=
    DescentExteriorFetch.run keyPos first n kb gg gb keyFits firstRoom ready lastRoom m
      machine pc reg pub exit rom «public» cfg m entry rfl
  refine ⟨cnt,paid,zf,out,ran,stop,eq,?_⟩
  rw [eq]
  refine ⟨zero_columns keyPos first kb gg gb ready M x z m cap (inputs origin M x z m loads endRoom)
    guessFit guessRows (expected origin M x z m loads) wordPos wordRoom,?_⟩
  exact final_row keyPos first kb gg gb ready M x z m cap (inputs origin M x z m loads endRoom)

private theorem retain_receipt {bits clock : ℕ} (program : Procedure bits) (pre : Memory bits→Prop)
    (out : Memory bits→Memory bits) (receipt : Memory bits→Prop)
    (exactRun : program.Spec pre (fun m after=>after=out m ∧ receipt after) clock ∧ CheapCode program) :
    program.Spec pre (fun _ after=>receipt after) clock ∧ CheapCode program :=
  ⟨@Procedure.Spec.mono bits program pre pre (fun m after=>after=out m ∧ receipt after)
    (fun _ after=>receipt after) clock clock exactRun.1 (fun _ h=>h) (fun _ _ h=>h.2) le_rfl,
    exactRun.2⟩

theorem native (wordPos : 0<w) (wordRoom : 2^j*t≤w)
    (space : origin+22*H<2^w) (M : Fin e→Layout k)
    (x : Fin e→Plane j r→Fin t→Bool) (z : Hidden e j r t→Bool) :
    (service w j r t e origin).Spec (Loaded origin M x z) (fun _ after=>Receipt origin M x z after)
      (16+364*n) ∧ CheapCode (service w j r t e origin) :=
  @retain_receipt w (16+364*n) (service w j r t e origin) (Loaded origin M x z)
    (serviceMemory (j:=j) (r:=r) (t:=t) (e:=e) origin) (Receipt origin M x z)
    (native_exact (w:=w) (j:=j) (r:=r) (t:=t) (e:=e) origin wordPos wordRoom space M x z)

/-- The running time is proportional to the number of complete chunk
rows. The working and advice image is shared by every exterior index. -/
theorem invoice (short : tableBits j r t≤w/2) :
    (endAt j r t e origin≤origin+39*n+18*(1+2^(w/2))) ∧
    (Fintype.card (Hidden e j r t)=2*(e*2^k*t)) ∧
    (Fintype.card (Column e j r)=4*n) :=
  ⟨price j r t e origin short,(header_price e j r t).2,(header_price e j r t).1⟩

/-- The unique hidden bit planes and every cell of the temporary memory
are charged at the same word width. -/
theorem bit_invoice (short : tableBits j r t≤w/2) (payload : 2^j*t≤w) :
    Fintype.card (Hidden e j r t)+(endAt j r t e origin-origin)*(w+1) ≤
      60*(n+2^(w/2)+1)*(w+1) := by
  obtain ⟨cells,bits,_⟩:=invoice (e:=e) origin short
  have repr : 2*(e*2^k*t)=2*n*(2^j*t) := by rw [pow_add];ring
  have control : endAt j r t e origin-origin≤39*n+18*(1+2^(w/2)) := by omega
  rw [bits,repr]
  calc
    _ ≤ 2*n*(w+1)+(39*n+18*(1+2^(w/2)))*(w+1) :=
      Nat.add_le_add (Nat.mul_le_mul_left _ (payload.trans (Nat.le_succ w)))
        (Nat.mul_le_mul_right _ control)
    _ = (2*n+(39*n+18*(1+2^(w/2))))*(w+1) := (Nat.add_mul ..).symm
    _ ≤ _ := Nat.mul_le_mul_right _ (by omega)

end
end Hierarchy.DescentExteriorShelf

end OAI
