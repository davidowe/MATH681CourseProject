import Mathlib

namespace SetTheory

namespace PGame

namespace Hex

/-
Set up the board as follows:
Include the black and white border points in the black and white fields of the board
The RepBorder points can be any point of the border of the corresponding side
The winning condition checks whether the border rep points are reachable from each other
Example empty 3x3 board:

    B B
   E E E W
  W E E E W
   W E E E
      B B

def HexEmptyTxTBoard : Board :=
  {
    empty := [(0,0), (1,0), (2,0), (0,1), (1,1), (2,1), (0,2), (1,2), (2,2)]
    black := [(1,-1), (2,-1), (0,3), (1,3)]
    white := [(-1,1), (-1,2), (3,0), (3,1)]
  }

def HexEmptyTxTRepBorder ; RepBorder :=
  {
    N := (1,-1)
    E := (3,0)
    S := (0,3)
    W := (-1,1)
  }
-/

open SimpleGraph

structure HexBoard where
  empty : Finset (ℤ × ℤ)
  black : Finset (ℤ × ℤ)
  white : Finset (ℤ × ℤ)
  N : {x // x ∈ black}
  S : {x // x ∈ black}
  E : {x // x ∈ white}
  W : {x // x ∈ white}
deriving DecidableEq

def GetHexGraph (pieces : Finset (ℤ × ℤ)) [Fintype pieces] [DecidableEq pieces] : SimpleGraph {x // x ∈ pieces} :=
  {
    Adj := fun a b => (a ≠ b) ∧ ( (a.1.1+1 = b.1.1) ∧ (a.1.2 = b.1.2)   ∨ -- E
                                  (a.1.1-1 = b.1.1) ∧ (a.1.2 = b.1.2)   ∨ -- W
                                  (a.1.1 = b.1.1)   ∧ (a.1.2+1 = b.1.2) ∨ -- N
                                  (a.1.1 = b.1.1)   ∧ (a.1.2-1 = b.1.2) ∨ -- S
                                  (a.1.1+1 = b.1.1) ∧ (a.1.2+1 = b.1.2) ∨ -- NE
                                  (a.1.1-1 = b.1.1) ∧ (a.1.2-1 = b.1.2)   -- SW
                                )
  }

instance (pieces : Finset (ℤ × ℤ)) : DecidableRel (GetHexGraph pieces).Adj := by
  intro a b
  unfold GetHexGraph
  exact And.decidable

def moveLeft (hb : HexBoard) (m : ℤ × ℤ) : HexBoard :=
  {
    empty :=
    if (GetHexGraph hb.black).Reachable hb.N hb.S then
      Finset.empty
    else
      hb.empty.erase m

    black := insert m hb.black
    white := hb.white
    N :=  {val := hb.N.val, property := by
            refine Finset.mem_insert_of_mem hb.N.property
          }
    S :=  {val := hb.S.val, property := by
            refine Finset.mem_insert_of_mem hb.S.property
          }
    E :=  {val := hb.E.val, property := by
            exact Finset.coe_mem hb.E
          }
    W :=  {val := hb.W.val, property := by
            exact Finset.coe_mem hb.W
          }
  }

def moveRight (hb : HexBoard) (m : ℤ × ℤ) : HexBoard :=
  {
    empty :=
    if (GetHexGraph hb.white).Reachable hb.E hb.W then
      Finset.empty
    else
      hb.empty.erase m

    black := hb.black
    white := insert m hb.white
    N :=  {val := hb.N.val, property := by
            exact Finset.coe_mem hb.N
          }
    S :=  {val := hb.S.val, property := by
            exact Finset.coe_mem hb.S
          }
    E :=  {val := hb.E.val, property := by
            refine Finset.mem_insert_of_mem hb.E.property
          }
    W :=  {val := hb.W.val, property := by
            refine Finset.mem_insert_of_mem hb.W.property
          }
  }

theorem leftMoveEmptyOrErase (hb : HexBoard) (m : ℤ × ℤ)
    : ((moveLeft hb m).empty = Finset.empty) ∨ ((moveLeft hb m).empty = hb.empty.erase m) := by
  unfold moveLeft
  exact ite_eq_or_eq (Reachable (GetHexGraph hb.black) hb.N hb.S) Finset.empty (Finset.erase hb.empty m)

theorem rightMoveEmptyOrErase (hb : HexBoard) (m : ℤ × ℤ)
    : ((moveRight hb m).empty = Finset.empty) ∨ ((moveRight hb m).empty = hb.empty.erase m) := by
  unfold moveRight
  exact ite_eq_or_eq (Reachable (GetHexGraph hb.white) hb.E hb.W) Finset.empty (Finset.erase hb.empty m)

#check Finset.card
#check Finset.empty

theorem leftMoveSmaller (hb : HexBoard) (m : {x // x ∈ hb.empty})
    : Finset.card (moveLeft hb m).empty < Finset.card hb.empty := by
  cases leftMoveEmptyOrErase hb m with
  | inl h => {
    rw [h, Finset.empty, Finset.mk_zero, Finset.card_empty, Finset.card_pos]
    constructor
    case inl.w := m.val
    exact m.property
  }
  | inr h => {
    rw [h]
    exact Finset.card_erase_lt_of_mem m.property
  }

theorem rightMoveSmaller (hb : HexBoard) (m : {x // x ∈ hb.empty})
    : Finset.card (moveRight hb m).empty < Finset.card hb.empty := by
  cases rightMoveEmptyOrErase hb m with
  | inl h => {
    rw [h, Finset.empty, Finset.mk_zero, Finset.card_empty, Finset.card_pos]
    constructor
    case inl.w := m.val
    exact m.property
  }
  | inr h => {
    rw [h]
    exact Finset.card_erase_lt_of_mem m.property
  }

instance hexState : State HexBoard where
  turnBound hb := hb.empty.card
  l hb := Finset.image (moveLeft hb) hb.empty
  r hb := Finset.image (moveRight hb) hb.empty

  left_bound := by
    simp
    intro s t a b h1 h2
    rw [←h2]
    exact leftMoveSmaller s {val := (a,b), property := h1}

  right_bound := by
    simp
    intro s t a b h1 h2
    rw [←h2]
    exact rightMoveSmaller s {val := (a,b), property := h1}

def ExHexBoard : HexBoard :=
  {
    empty := [(0,0), (1,0), (2,0), (0,1), (1,1), (2,1), (0,2), (1,2), (2,2)].toFinset
    black := [(1,-1), (2,-1), (0,3), (1,3), (1,1), (1,0)].toFinset
    white := [(-1,1), (-1,2), (3,0), (3,1), (0,0), (0,1), (2,0), (2,1)].toFinset
    N := {val := (1,-1), property := by apply Finset.insert_eq_self.mp rfl}
    E := {val := (3,0), property := by apply Finset.insert_eq_self.mp rfl}
    S := {val := (0,3), property := by apply Finset.insert_eq_self.mp rfl}
    W := {val := (-1,1), property := by apply Finset.insert_eq_self.mp rfl}
  }

def hex (hb : HexBoard) : PGame := PGame.ofState hb

instance shortlinClobber (hb : HexBoard) : Short (hex hb) := by
  dsimp [hex]
  infer_instance

--#eval decide (hex ExHexBoard ≈ 0)

end Hex

/-
Future work:
Define Decidable star, up, down
Chop, cut cake, hackenbush, Y, toads and frogs
Define adj groups, needed for hex, can be used to split up domineering positions
Possible proofs:
  square chomp = star
  Cannot draw in Hex
  Zermello's theorem
Create a more efficient program for determining game value
Create function which outputs actual game value instead of just deciding equality
Temperature, hot games
-/
