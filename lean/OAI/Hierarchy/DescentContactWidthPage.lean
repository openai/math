import OAI.Hierarchy.DescentStaticUnary

namespace OAI
/-! # Repacking a contact counter into the common metadata digit width -/
namespace Hierarchy.DescentContactWidthPage
open DescentSIMDLookup DescentPackedZip DescentOrdinaryAtomFieldRAM.ROM
open ProtocolRAM Computability.VPVNP.BurstRAM PrivateRAM ThreeFlat.RAM PhysicalProcedure
open scoped Classical Fin.CommRing
noncomputable section
variable {H G M b t w : ℕ}

def recode (t : ℕ) (x : Cell b) : Cell t :=x.val
def law (b t : ℕ) (x : Cell b) (_ : Cell 0) : Cell t:=recode t x
def words (b M : ℕ) :=2*2^(b*M)
def endAddress (floor b M : ℕ) :=floor+words b M
def program (floor b t M w : ℕ) :=mount (binary (law b t) M) (b*M) w floor
def image (floor b t M : ℕ) (m : Memory w) :=after (binary (law b t) M) (b*M) floor m
def expr (floor b t M : ℕ) (src : Expr) :=DescentStaticUnary.query (law b t) M floor src
def clock (b M : ℕ) :=4+10*words b M
def size (b M : ℕ) :=15*(words b M+1)

theorem recode_val (x : Cell b) (fits : x.val<2^t) : (recode t x).val=x.val := Fin.val_cast_of_lt fits

theorem cast (x : Cell b) (wide : b≤t) : (recode t x).val=x.val :=
  recode_val x (x.isLt.trans_le (Nat.pow_le_pow_right (by decide) wide))

theorem any (floor b t M : ℕ) (m : Memory w) (room : endAddress floor b M<2^w) :
    (program floor b t M w).Exec m (image floor b t M m) (clock b M) ∧ CheapCode (program floor b t M w) ∧
    ∀z,z<floor ∨ endAddress floor b M≤z→image floor b t M m z=m z := by
  have p:=DescentStaticUnary.read (H:=0) (G:=0) (M:=M) (law b t) (by simp [law,recode]) floor m room
  exact ⟨p.1,p.2.2.2,p.2.2.1⟩

theorem tariff (floor b t M : ℕ) (m : Memory w) (room : endAddress floor b M<2^w) :
    DescentStaticWordColumn.names (program floor b t M w)=size b M :=
  (DescentOrdinaryAtomFieldRAM.ROM.run (binary (law b t) M) (b*M) floor m room).2

/-- A unary table remains addressable by expressions declared later on the tape. -/
theorem general_fits {a b : ℕ} (F : Cell b→Cell 0→Cell a) (M root floor : ℕ) (src : Expr)
    (held : src.Fits w floor) (before : root+2*2^(b*M)≤floor) (space : floor<2^w) :
    (DescentStaticUnary.query F M root src).Fits w floor:=by
  let p:=binary F M
  have sizes (i : Fin 2) : (p i).bits≤b*M:=by fin_cases i <;> simp [p,binary]
  have stored (i : Fin 2) :=bank_room p (b*M) root floor i (sizes i) before space
  exact ⟨stored 1,trivial,stored 0,held⟩

theorem fits (floor b t M : ℕ) (src : Expr) (prior : src.Fits w floor) (room : endAddress floor b M<2^w) :
    (expr floor b t M src).Fits w (endAddress floor b M) :=by
  exact general_fits _ _ _ _ src (ProtocolRAMGeneratedWrite.fits_mono src (Nat.le_add_right ..) prior) le_rfl room

theorem posted (floor b t M : ℕ) (m : Memory w) (room : endAddress floor b M<2^w)
    (src : Expr) (x : Fin H→Fin G→Cell b) (prior : src.Fits w floor) (read : Source src x M m) :
    Source (expr floor b t M src) (fun h g=>recode t (x h g)) M (image floor b t M m) :=by
  have p:=DescentStaticUnary.read (H:=H) (G:=G) (M:=M) (law b t) (by simp [law,recode]) floor m room
  exact (p.2.1 src x prior read).2

/-- After subsequent jobs, the same immutable expression still reads the attained count
when the table and its preceding sources are covered by the retained memory frame. -/
theorem retained (floor b t M : ℕ) (m dst : Memory w) (room : endAddress floor b M<2^w)
    (src : Expr) (x : Fin H→Fin G→Cell b) (prior : src.Fits w floor) (read : Source src x M m)
    (keep : ∀u,u<endAddress floor b M→dst u=image floor b t M m u) :
    Source (expr floor b t M src) (fun h g=>recode t (x h g)) M dst :=by
  intro q
  exact (ProtocolRAM.eval_below _ _ _ _ (fits floor b t M src prior room) keep).trans (posted floor b t M m room src x prior read q)

end
end Hierarchy.DescentContactWidthPage

end OAI
