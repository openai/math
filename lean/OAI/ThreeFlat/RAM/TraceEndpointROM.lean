import OAI.ThreeFlat.Diagonal.TracePairLeafReady

namespace OAI
/-! # One common public register layout for all initial history atoms -/

namespace ThreeFlat.RAM.TraceEndpointROM
open Computability.VPVNP.BurstRAM DescriptorExpr TraceBucketAtom Diagonal.TraceBitHeader
open scoped Fin.CommRing

/-- Original literal bank, public header description (11 used slots), and
three geometry fields. The spare public slots are identically zero. -/
def params := (1+bankSize)+(125+3)
def rawSlot (i : Fin (1+bankSize)) : Fin params := i.castAdd (125+3)
def oracleSlot (i : Fin 11) : Fin params := Fin.natAdd (1+bankSize) ((i.castLE (by decide : 11≤125)).castAdd 3)
def dimSlot (i : Fin 3) : Fin params := Fin.natAdd (1+bankSize) (Fin.natAdd 125 i)

def data {W : ℕ} (s : Layout) (original : Fin 1→Word W) (config : Fin 11→Word W) (S T low : ℕ) :
    Fin params→Word W :=
  Fin.append (publicData s original) <| Fin.append (fun j : Fin 125 => if h : j.val<11 then config ⟨_,h⟩ else 0)
    ![(S : Word W),(2*T : ℕ),(2*2^low : ℕ)]

private theorem firstBank {α : Type*} {n k : ℕ} (first : Fin n→α) (rest : Fin k→α) :
    (Fin.append first rest) ∘ (fun i => i.castAdd k) = first :=
  funext (Fin.append_left first rest)

set_option maxRecDepth 8192 in
theorem data_raw {W : ℕ} (s : Layout) (original : Fin 1→Word W) (config : Fin 11→Word W) (S T low : ℕ) :
    data s original config S T low ∘ rawSlot = publicData s original :=
  firstBank (n:=1+bankSize) (k:=125+3) (publicData s original)
    (Fin.append (fun j : Fin 125 => if h : j.val<11 then config ⟨_,h⟩ else 0)
      ![(S : Word W),(2*T : ℕ),(2*2^low : ℕ)])

theorem data_oracle {W : ℕ} (s : Layout) (original : Fin 1→Word W) (config : Fin 11→Word W)
    (S T low : ℕ) (i : Fin 11) : data s original config S T low (oracleSlot i)=config i := by
  simp [data,oracleSlot,i.isLt]

theorem data_dims {W : ℕ} (s : Layout) (original : Fin 1→Word W) (config : Fin 11→Word W) (S T low : ℕ) :
    data s original config S T low ∘ dimSlot = ![(S : Word W),(2*T : ℕ),(2*2^low : ℕ)] := by
  funext i
  change data s original config S T low (dimSlot i)=(![(S:Word W),(2*T:ℕ),(2*2^low:ℕ)] i)
  simp only [data,dimSlot,Fin.append_right]

def program (W : ℕ) (oracle : Term W params 1) : Term W params 4 :=
  endpointProgram W rawSlot oracle (dimSlot 0) (dimSlot 1) (dimSlot 2)

theorem program_size (W : ℕ) (oracle : Term W params 1) (small : oracle.binds≤200) :
    (program W oracle).binds≤1000300 := by
  exact (endpointProgram_size W rawSlot oracle (dimSlot 0) (dimSlot 1) (dimSlot 2)).trans (by omega)


end ThreeFlat.RAM.TraceEndpointROM

end OAI
