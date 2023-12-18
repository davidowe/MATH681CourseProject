import Mathlib
namespace SetTheory
namespace PGame
namespace Chomp

/-
CGT implementation of the game of Chomp.
Chomp is a two player impartial game played with a set of contiguous points.
Games typically start out on rectangular boards such as:
⬜⬜⬜⬜
⬜⬜⬜⬜
🟩⬜⬜⬜
Where the bottom right point is 'poisoned' and can never be removed.
A player makes a move by choosing a point to remove, which results in every
point above or to the right of the move to also be removed.
For example:
Player 1 moves on the point (1,1):
⬜
⬜
🟩⬜⬜⬜
Player 2 moves at (0,1):
🟩⬜⬜⬜
Player 1 moves at (1,0) and wins, as the last player to make a move wins
and there are no legal moves left in the game.

In the implementation of Chomp, I used a Finset of (ℤ × ℤ) points to
represent the points on the board, and the poisoned square was excluded as
it is not a legal move.
To implement the rules of Chomp, I used the Finset.filter function to
remove any points above or to the right of a move.
-/

-- The board representation as a Finset of points
@[reducible]
def Board := Finset (ℕ × ℕ)
deriving Inhabited

@[simp]
def Move := (ℕ × ℕ)

-- Filter for points to the left or below a move
@[simp]
def moveFilterFunc (m : Move) (x : Move) : Prop := x.1 < m.1 ∨ x.2 < m.2

-- Prove this is Decidable
instance mffDecidable (m : Move) (x : Move) : Decidable (moveFilterFunc m x) := by
  simp
  exact Or.decidable

-- A move in Chomp removes an points above or the the right of a move (including the move)
@[simp]
def makeMove (b : Board) (m : Move) : Board := Finset.filter (moveFilterFunc m) b

-- Prove that a board's points after a move is a subset of the board's points before a move
theorem move_ssubset {b : Board} {m : Move} (h : m ∈ b) :
  makeMove b m ⊂ b := by
  simp
  apply Finset.filter_ssubset.2
  apply Exists.intro
  case w := m
  apply And.intro
  exact h
  simp

-- Show that every move makes the number of possible moves smaller
theorem move_smaller {b : Board} {m : Move} (h : m ∈ b) :
  Finset.card (makeMove b m) < Finset.card b := by
  simp
  refine Finset.card_lt_card ?h
  exact move_ssubset h

-- Instantiate a Chomp state on boards
instance chompState : State Board where
  turnBound s := s.card -- An upper bound for the number of turns remaining
  l s := s.image (makeMove s) -- All possible states after Left makes a move
  r s := s.image (makeMove s) -- All possible states after Right makes a move
  left_bound m := by -- Prove that a move by Left decreases the turn bound
    simp
    simp at m
    apply Exists.elim m
    intro a b
    apply Exists.elim b
    intro c d
    have d0 := d.1
    have d1 := d.2
    rw [←d1]
    apply move_smaller
    exact d0
  right_bound m := by -- Prove that a move by Right decreases the turn bound
    simp
    simp at m
    apply Exists.elim m
    intro a b
    apply Exists.elim b
    intro c d
    have d0 := d.1
    have d1 := d.2
    rw [←d1]
    apply move_smaller
    exact d0

-- Make a Chomp game from a board position
def Chomp (b : Board) : PGame := PGame.ofState b

-- Chomp is a short game (finite sized boards always have a finite turn bound)
instance shortChomp (b : Board) : Short (Chomp b) := by
  dsimp [Chomp]
  infer_instance

-- Some example Chomp positions to evaluate
-- We exclude the "poisoned" (0,0) square, as players cannot play on it

def TwoByTwo : Board := {(0,1), (1,1),
                                (1,0)}

def ThreeByThree : Board := {(0,2),(1,2),(2,2),
                             (0,1),(1,1),(2,1),
                                   (1,0),(2,0)}

def FourByFour : Board := {(0,3),(1,3),(2,3),(3,3),
                           (0,2),(1,2),(2,2),(3,2),
                           (0,1),(1,1),(2,1),(3,1),
                                 (1,0),(2,0),(3,0)}

def SymTwoL : Board := {(0,2),
                        (0,1),
                              (1,0), (2,0)}

-- Showing the value / outcome of the two by two chomp board
#eval Chomp TwoByTwo ≈ 0
#eval Chomp TwoByTwo > 0
#eval Chomp TwoByTwo < 0
#eval Chomp TwoByTwo ⧏ 0
#eval 0 ⧏ Chomp TwoByTwo
-- This shows that this board is fuzzy with zero, and is therefore a first player win
-- The ‖ operator in Mathlib is not Decidable for some reason, but G ‖ 0 ↔ G ⧏ 0 ∧ 0 ⧏ G

-- Three by three positions take longer to evaluate, future work on this
-- could include speeding up game evaluation
#eval Chomp ThreeByThree ≈ 0
#eval Chomp ThreeByThree ⧏ 0

-- Example second player win position
#eval Chomp SymTwoL ≈ 0

-- You can also compare games directly
#eval Chomp TwoByTwo ≈ Chomp SymTwoL
#eval Chomp TwoByTwo ⧏ Chomp SymTwoL

end Chomp
