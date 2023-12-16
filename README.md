# MATH 681 - Combinatorial Game Theory Implementations
By Owen Randall

# Combinatorial Game Theory (CGT)

CGT was first introduced by John Conway in *On Numbers and Games* [1] where the structure of a combinatoral game was first formalized. 
An interesting property of this formalization is that we are now able to attribute values to game positions, which describe the outcome of optimal play on the position.
Using these values, a partial ordering of games can be constructed, and arithmetic can be performed to determine the values of compositions of games.

Typically the games studied by CGT have the following properties:
1. There are two players.
2. Moves are sequential (players take turns making moves rather than moving simultaneously).
3. Both players have perfect information (the entire game state is known, there are no elements of chance).
4. The player who makes the last move in the game wins.

Many popular games conform to these requirements such as chess, hex, connect 4, othello, gomoku, checkers, etc.
Even some games which do not conform to these rules can use CGT to analyze positions, for example Go does not satisfy 4. in general, but CGT has been used to analyze Go endgame results [2].

Here is some basic terminology and notation used in CGT:
- Player 1 = Left = Black = X
- Player 2 = Right = White = O
- Partisan games are games where players have access to different legal moves or their moves have different effects on the game state (any game that assign different coloured pieces to each player among others)
- Impartial games are games where players both have access to the same set of legal moves (e.g. nim, chomp, hackenbush, etc.)
- G = {GL_1, GL_2, ... | GR_1, GR_2, ...} is the notation for a game G where Left can move to game GL_1 or GL_2 etc. and Right can move to GR_1 or GR_2 etc.

The value of a game corresponds to the outcome of the game if both players play optimally.
- If G = 0, the second player wins.
- If G > 0, Left wins as the first or second player.
- If G < 0, Right wins as the first or second player.
- If G ‖ 0, (pronounced G is fuzzy with 0) the first player wins.

Addition on games is defined as:\
G + H = {GL_1+H, GL_2+H, ... | GR_1+H, GR_2+H, ...}\
Negation on games is defined as:\
-G = {-GR_1, -GR_2, ... | -GL_1, -GL_2, ...}\
Multiplication and division are also defined, but that is out of scope for this project

But in practice, many games can be simplified to numerical values where the normal rules of addition and negation apply.
Examples:
- {|} = 0
- {n|} = n+1 where n >= 0
- {|n} = n-1 where n <= 0
- {n|n+1} = (2n+1)/2 where n >= 0
- {n-1|n} = (2n-1)/2 where n <= 0

This makes CGT useful in practice for analysis of games which decompose into independent sub-games. 
For example, assume that the expression b^d approximates the search tree size required to solve a game G, where b is the average branching factor of the tree and d is the average depth of the leaf nodes.
Now lets say this game decomposes into two equal independent subgames, CGT analysis allows us to cut the search tree size down from b^d to 2*(b/2)^d, and that is assuming there are no more game decompositions to be made.
A good practical example of CGT analysis exponentially outpreforming traditional search was made in the PhD thesis of U of A Professor Martin Mueller [3].

There is much more to CGT, such as temperature, infinitesimals, tracendentals, ordinals and more, but none of this is necessary knowledge to understand the basics of CGT.

# Games Implemented

Looking through the existing CGT library in Mathlib, I saw that there was only one game implemented so far, which is understandable as the library is quite small at this point.
There are comments throughout several files in the library calling stating that the future work for this library should be to implement more games (specifically hex was mentioned), so I knew this would be my course project.
The existing game is called Domineering, a partisan game where players take turn placing 2x1 or 1x2 dominoe pieces until no legal moves are remaining.
This is a commonly used game for teaching CGT as you can easily construct various numbers for example:
(⬜ represents an empty square of a domineering board)

⬜\
⬜ = 1

⬜⬜ = -1

⬜\
⬜\
⬜⬜ = {-1,0|1} = 1/2

⬜\
⬜⬜ = {0|0} = * (pronounced star, is fuzzy with 0)

I wanted to implement more challenging games than Domineering for my course project, but I figured I should start off with an easy game.
The first game implemented is an impartial game called Chomp, where players take turns removing chunks of the board until there is nothing left.
The game normally starts out as a rectangular board.
A move consists of choosing any point on the board, and the move causes that point, and every point above or to the right of the move to disapear.
There is an initial 'poisoned square' as the bottom left point on the board which neither player can make a move on.
Example 3x4 game:

⬜⬜⬜⬜\
⬜⬜⬜⬜\
🟩⬜⬜⬜

Player 1 moves at (1,1):

⬜\
⬜\
🟩⬜⬜⬜

Player 2 moves at (0,1):

🟩⬜⬜⬜

Player 1 moves at (1,0) and wins.

In the implementation of Chomp, I used a Finset of (ℤ × ℤ) points to represent the points on the board, and the poisoned square was excluded as it is not a legal move.
To implement the rules of Chomp, I used the Finset.filter functionality to remove any points above or to the right of a move.

The next game implemented is Linear Clobber, a one dimensional variation of the game Clobber. Linear Clobber is a partisan game where the game starts with all the black and white stones already placed on the board.
Players then make moves by 'clobbering' the opponent stones, where they move on of their stones onto an adjacent opponent stone, capturing it.

Example game:\
◯⬤◯⬤◯⬤\
Black moves:\
\_◯◯⬤◯⬤\
White moves:\
\_◯◯\_⬤⬤\
White wins as there are no legal moves left for black.

This is an interesting game for CGT analysis as games tend to decompose into independent subgames very quickly, giving a large adge to using CGT analysis over traditional search.
Another interesting property of Clobber is that it is an all-small game [4], which means that the value of any position in Clobber is infinitesimal.
I chose Linear Clobber over normal 2d Clobber because the implementation would be very similar, but much shorter and less tedious.
I am in the midst of completing a paper proving that any position of the form (◯⬤)^n ‖ 0, where n > 0 and n ≠ 3.

The implementation of Linear Clobber was much more difficult than chomp or domineering, as the legal moves depend not on the empty points of the board, but rather on adjacent stones of opposite color.
This means we need to keep track of the white and black stones, and modify the configuration of both when moves are made.
The positions of pieces are stored as a Finset of integers, and moves are represented by an integer pair (ℤ × ℤ), where the first integer is the direction of the move (-1 for left, 1 for right), and the second integer is the position of the stone being moved.
I then implemented a black move by erasing the stone being moved from the black stones, inserting a stone at the position the stone would be moved to, and removing the white stone at the point where the black stone moved to (vice-versa for white moves).
Proving turn bounds and shortness were difficult due to these complicated rules so I needed to implement many lemmas and theorems in order to break up the problem into smaller chunks.

Hex is the final game implemented in this course project, and was specifically requested by the comments in the existing CGT library.
Hex is a partisan game played on a four-sided board made up of hexagons, where the black tries to connect the top of the board to the bottom, and white tries to connect the left side of the board to the right. 

Example empty 3x3 board:\
⬡ ⬡ ⬡\
&nbsp;&nbsp;⬡ ⬡ ⬡\
&nbsp;&nbsp;&nbsp;&nbsp;⬡ ⬡ ⬡\
This would be considered a win for black as there is a connection from top to bottom via adjacent black stones:\
⬡ ⬤ ◯\
&nbsp;&nbsp;◯ ⬤ ⬤\
&nbsp;&nbsp;&nbsp;&nbsp;⬡ ◯ ⬤

The legal moves for each player in Hex is simply the empty points on the board, however the terminal condition of the game is complicated. In all the games implemented up to this point, the game is played until there are no moves left at which point the last player to have moved wins. In Hex, the terminal condition is connected the sides of the board rather than just running out of move. Fortunately, we can represent the special termination condition when generating the legal moves after a move is played. If no side connected is made, the legal moves are all the empty points on the board. If a side connection is found, then there are no legal moves. I used the SimpleGraph library in mathlib to check for side connections which was a very interesting learning experience.

# Bibliography

1. Conway, John H. 1976. On Numbers and Games. London: Academic Press.
2. Berlekamp, Elwyn & Wolfe, David. 1994. Mathematical Go - chilling gets the last point. 10.1201/9781439863558. 
3. Mueller, Martin. 1999. Decomposition search: a combinatorial games approach to game tree search, with applications to solving go endgames. In Proceedings of the 16th international joint conference on Artifical intelligence - Volume 1 (IJCAI'99). 578–583.
4. Albert, Michael & Grossman, J.P. & Nowakowski, Richard & Wolfe, David. 2005. An introduction to Clobber. Integers. 5. 
5. Demer, Eric & Selinger, Peter & Wang, Kyle. 2021. All passable games are realizable as monotone set coloring games.