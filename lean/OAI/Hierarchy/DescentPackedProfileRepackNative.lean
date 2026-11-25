import OAI.Hierarchy.DescentOverlapTariff
import OAI.Hierarchy.DescentNativeBankLookup
import OAI.Hierarchy.DescentStaticWordCheap

namespace OAI
/-! # A native unequal-pitch word transfer with a change of field width -/
namespace Hierarchy.DescentPackedProfileRepack
open DescentSIMDLookup ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM
open ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section

def widen (oldBits newBits pitch raw : ℕ) : ℕ :=
  let input := (encode oldBits pitch).symm (raw:Cell (oldBits*pitch))
  (encode newBits pitch (fun i=>(input i).val)).val

def book (base seats A B b : ℕ) : Bank := ⟨Overlap.endAddress base 1 seats A B b,b*B⟩
def workEnd (base seats A B b : ℕ) := Overlap.endAddress base 1 seats A B b+2^(b*B)

theorem workEnd_affine (base seats A B b : ℕ) :
    workEnd base seats A B b=base+workEnd 0 seats A B b := by
  simp [workEnd,Overlap.endAddress,Overlap.dest,Overlap.dictBase,Nat.add_assoc]

def body (seats B : ℕ) (lut rows : Bank) : Expr :=
  .branch .lt .row (.lit (chunks seats B)) (.lookup lut (.lookup rows .row)) (.lit 0)

variable (base seats A B b d : ℕ) (source raw : Bank)
local notation "lo" => Overlap.endAddress base 1 seats A B b
local notation "pool" => 2^(b*B)
local notation "words" => Overlap.outputBank base 1 seats A B b
local notation "dyad" => book base seats A B b
local notation "move" => body seats B dyad words
local notation "finish" => workEnd base seats A B b
local notation "ov" => Overlap.program base 1 seats A B b
local notation "ix" => Overlap.result base 1 seats A B b source
local notation "cost" => Overlap.ticks base 1 seats A B b source

def program (w : ℕ) :=
  ((ov w source).seq (DescentStaticWordColumn.program w lo (widen b d B) pool)).seq
    (scan w raw.base raw.size move)

def image {w : ℕ} (m : Memory w) :=
  ProtocolRAM.image raw.base raw.size move (DescentStaticWordColumn.image lo (widen b d B) (ix m) pool)

def ticks :=
  (cost+(4+10*pool))+(4+raw.size*(2*(move).work+4))

/-- All three phases contain only the native cheap instruction set, for every layout. -/
theorem cheap (w : ℕ) : CheapCode (program base seats A B b d source raw w) := by
  have repack : CheapCode (ov w source) := by
    apply cheap_seq
    · apply cheap_seq <;> apply DescentOrdinaryAtomFieldRAM.ROM.cheap
    · apply scan_cheap
  intro P R K pc reg pub exit i
  exact cheap_seq (cheap_seq repack (DescentStaticWordColumn.cheap w lo (widen b d B) pool))
    (scan_cheap w raw.base raw.size move) pc reg pub exit i

/-- The constructor runs on every input memory and writes only its scratch and the requested raw bank. -/
theorem any {w : ℕ} (m : Memory w) (prior : source.Fits w base) (apart : finish≤raw.base)
    (room : raw.base+raw.size<2^w) :
    (program base seats A B b d source raw w).Exec m (image base seats A B b d source raw m)
      (ticks base seats A B b source raw) ∧
    (∀q,(q<base ∨ finish≤q)→(q<raw.base ∨ raw.base+raw.size≤q)→image base seats A B b d source raw m q=m q) ∧
    CheapCode (program base seats A B b d source raw w) := by
  have stop : finish<2^w := apart.trans_lt ((Nat.le_add_right ..).trans_lt room)
  have covered:=Overlap.output_fits base 1 seats A B b w ((Nat.le_add_right ..).trans_lt stop)
  have first:=Overlap.any base 1 seats A B b source m prior (covered.2.2.trans_lt ((Nat.le_add_right ..).trans_lt stop))
  have before : lo≤raw.base := (Nat.le_add_right ..).trans apart
  have look : (dyad).Fits w raw.base :=
    ⟨Nat.two_pow_pos _,(Nat.le_add_left ..).trans_lt stop,apart⟩
  have columns : (words).Fits w raw.base := ⟨covered.1.1,covered.1.2.1,covered.1.2.2.trans before⟩
  have fit : (move).Fits w raw.base := ⟨trivial,trivial,⟨look,columns,trivial⟩,trivial⟩
  let mid:=DescentStaticWordColumn.image lo (widen b d B) (ix m) pool
  have lower : base≤lo := by
    calc
      base ≤ Overlap.dictBase base 1 seats A B := Nat.le_add_right _ _
      _ ≤ Overlap.dest base 1 seats A B b := Nat.le_add_right _ _
      _ ≤ lo := Nat.le_add_right _ _
  refine ⟨?_,?_,?_⟩
  · intro P R K machine
    exact Procedure.Exec.then (Procedure.Exec.then first.1 (DescentStaticWordColumn.mount lo pool (widen b d B) (ix m) stop))
      (scan_exec raw.base raw.size move mid fit room) machine
  · intro q scratch dst
    apply (ProtocolRAMGeneratedWrite.frame_image raw.base raw.size move mid q dst).trans
    apply (DescentStaticWordColumn.frame lo pool (widen b d B) (ix m) q (scratch.imp_left (fun h=>h.trans_le lower))).trans
    exact first.2.1 q (scratch.imp_right (fun h=>covered.2.2.trans ((Nat.le_add_right ..).trans h)))
  · intro P R K pc reg pub exit i
    exact cheap base seats A B b d source raw w pc reg pub exit i

/-- One public width-translation book is mounted once for the entire original shelf. -/
theorem tariff (w : ℕ) (oldPos : 0<A) (newPos : 0<B) :
    ticks base seats A B b source raw+7*DescentStaticWordColumn.names (program base seats A B b d source raw w) ≤
      2048*((Overlap.pieces seats A B+1)*(A+1)*2^(b*A)+Overlap.rows 1 seats A+Overlap.rows 1 seats B+1)+
        512*(pool+raw.size+1) := by
  have first:=Overlap.tariff base 1 seats A B b w source oldPos newPos
  have work : (move).work=17 := rfl
  simp only [ticks,program,DescentStaticWordColumn.names_seq,DescentStaticWordColumn.names_mount,
    DescentStaticWordColumn.names_scan,work]
  nlinarith only [first,Nat.two_pow_pos (b*B),Nat.zero_le raw.size]

end
end Hierarchy.DescentPackedProfileRepack

end OAI
