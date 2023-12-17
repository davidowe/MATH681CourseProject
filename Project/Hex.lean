import Mathlib

namespace SetTheory

namespace PGame

namespace Hex

/-

CGT implementation of Hex.
Hex is a partisan game played on a four-sided board made up of hexagons,
where the black tries to connect the top of the board to the bottom,
and white tries to connect the left side of the board to the right.

The legal moves for each player in Hex is simply the empty points on the board,
however the terminal condition of the game is complicated.
In most CGT example games, the game is played until there are no moves left at which point
the last player to have moved wins.
In Hex, the terminal condition is connected the sides of the board rather than just running
out of move.
Fortunately, we can represent the special termination condition when generating the legal
moves after a move is played.
If no side connected is made, the legal moves are all the empty points on the board.
If a side connection is found, then there are no legal moves.
I used the SimpleGraph library in mathlib to check for side connections.

Set up the board as follows:
Index the points on the board by the top-left to bottom-right diagonal column × the horizontal row
Include black and white border points in the black and white fields of the board
Make sure to include enough border points such that it is possible to connect any border point
to every other point on the board
The N S E W points can be any point of the border of the corresponding side (N for North etc.)
The winning condition checks whether N and S or E and W are reachable from each other through
their respective coloured pieces
Example empty 3x3 board including border points:

     B B
   ⬡ ⬡ ⬡ W
  W ⬡ ⬡ ⬡ W
   W ⬡ ⬡ ⬡
       B B

def EmptyThreeByThree : HexBoard :=
  {
    empty := [(0,0), (1,0), (2,0), (0,1), (1,1), (2,1), (0,2), (1,2), (2,2)]
    black := [(0,-1), (1,-1), (1,3), (2,3)]
    white := [(-1,0), (-1,1), (3,1), (3,2)]
    N := (1,3)
    S := (0,-1)
    E := (3,1)
    W := (-1,0)
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

-- Construct a Graph with the vertexes as the pieces of a given color,
-- and the edges determined by the six adjacencies of a hexagon
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

-- Prove that the adjacency relation is Decidable
instance (pieces : Finset (ℤ × ℤ)) : DecidableRel (GetHexGraph pieces).Adj := by
  intro a b
  unfold GetHexGraph
  exact And.decidable

-- To move, erase the empty point the player is moving at,
-- add the corresponding coloured piece to the board,
-- and then check whether the game is over by checking if the appropriate sides
-- are reachable from each other.
-- If the game is over, remove all empty points as no one should make moves on a terminal position
def moveBlack (hb : HexBoard) (m : ℤ × ℤ) : HexBoard :=
  {
    empty :=
    if (GetHexGraph hb.black).Reachable hb.N hb.S then
      Finset.empty
    else
      hb.empty.erase m

    black := insert m hb.black -- place the newly moved piece
    white := hb.white

    -- Carry over the representative border points, along with their property that they
    -- exist in the black or white pieces Finset
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

def moveWhite (hb : HexBoard) (m : ℤ × ℤ) : HexBoard :=
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

-- A move will either erase a single empty point, or erase all empty points if the position is terminal
theorem blackMoveEmptyOrErase (hb : HexBoard) (m : ℤ × ℤ)
    : ((moveBlack hb m).empty = Finset.empty) ∨ ((moveBlack hb m).empty = hb.empty.erase m) := by
  unfold moveBlack
  exact ite_eq_or_eq (Reachable (GetHexGraph hb.black) hb.N hb.S) Finset.empty (Finset.erase hb.empty m)

theorem whiteMoveEmptyOrErase (hb : HexBoard) (m : ℤ × ℤ)
    : ((moveWhite hb m).empty = Finset.empty) ∨ ((moveWhite hb m).empty = hb.empty.erase m) := by
  unfold moveWhite
  exact ite_eq_or_eq (Reachable (GetHexGraph hb.white) hb.E hb.W) Finset.empty (Finset.erase hb.empty m)

-- A move will always decrease the number of empty points on the board
theorem blackMoveSmaller (hb : HexBoard) (m : {x // x ∈ hb.empty})
    : Finset.card (moveBlack hb m).empty < Finset.card hb.empty := by
  cases blackMoveEmptyOrErase hb m with
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

theorem whiteMoveSmaller (hb : HexBoard) (m : {x // x ∈ hb.empty})
    : Finset.card (moveWhite hb m).empty < Finset.card hb.empty := by
  cases whiteMoveEmptyOrErase hb m with
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

-- Instantiate a Hex state on the HexBoard
instance hexState : State HexBoard where
  turnBound hb := hb.empty.card -- The turn bound is the number of empty points
  l hb := Finset.image (moveBlack hb) hb.empty
  r hb := Finset.image (moveWhite hb) hb.empty

  left_bound := by -- Neatly proved by out earlier theorems
    simp
    intro s t a b h1 h2
    rw [←h2]
    exact blackMoveSmaller s {val := (a,b), property := h1}

  right_bound := by
    simp
    intro s t a b h1 h2
    rw [←h2]
    exact whiteMoveSmaller s {val := (a,b), property := h1}

def hex (hb : HexBoard) : PGame := PGame.ofState hb

instance shortlinClobber (hb : HexBoard) : Short (hex hb) := by
  dsimp [hex]
  infer_instance

/-
     B B
   ⬡ ⬡ ⬡ W
  W ⬡ ⬡ ⬡ W
   W ⬡ ⬡ ⬡
       B B
-/
def EmptyThreeByThree : HexBoard :=
  {
    empty := {(0,0), (1,0), (2,0), (0,1), (1,1), (2,1), (0,2), (1,2), (2,2)}
    black := {(0,-1), (1,-1), (1,3), (2,3)}
    white := {(-1,0), (-1,1), (3,1), (3,2)}
    N := {val := (1,3), property := by apply Finset.insert_eq_self.mp rfl}
    S := {val := (0,-1), property := by apply Finset.insert_eq_self.mp rfl}
    E := {val := (3,1), property := by apply Finset.insert_eq_self.mp rfl}
    W := {val := (-1,0), property := by apply Finset.insert_eq_self.mp rfl}
  }

-- You can fill in the board with black and white pieces and evaluate:
/-
     B B
   ⬡ ⬡ ⬡ W
  W W B B W
   W W ⬡ ⬡
       B B
-/
def ex1 : HexBoard :=
  {
    empty := {(1,0), (2,0), (0,2), (1,2), (2,2)}
    black := {(0,-1), (1,-1), (1,3), (2,3), (1,1), (2,1)}
    white := {(-1,0), (-1,1), (3,1), (3,2), (0,0), (0,1)}
    N := {val := (1,3), property := by apply Finset.insert_eq_self.mp rfl}
    S := {val := (0,-1), property := by apply Finset.insert_eq_self.mp rfl}
    E := {val := (3,1), property := by apply Finset.insert_eq_self.mp rfl}
    W := {val := (-1,0), property := by apply Finset.insert_eq_self.mp rfl}
  }

-- Unfortunetly, the SimpleGraph.Reachable implementation in Mathlib is incredibly inefficient to
-- compute, as it enumerates every possible walk between two points
-- This makes hex evaluation very slow (but it will eventually finish)
#eval hex ex1 ≈ 0
#eval hex ex1 < 0
#eval hex ex1 > 0
#eval hex ex1 ⧏ 0

#eval hex EmptyThreeByThree ≈ 0
#eval hex EmptyThreeByThree < 0
#eval hex EmptyThreeByThree > 0
#eval hex EmptyThreeByThree ⧏ 0

-- Future work could include implementing a more efficient pathfinding algorithm for determining
-- whether two points are reachable from each other

end Hex
