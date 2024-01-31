package ProgrammingProject.model;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.List;


/**
 * Represents a game of Dots and Boxes, managing the players, the game board, and the game state.
 */

public class DotsAndBoxesGame implements Game {

    private Board board;
    private final Player[] players;
    private int currentPlayer;

    /**
     * Constructs a new game with the specified players and board dimension.
     *
     * @param players Array of two players participating in the game.
     * @param DIM     Dimension of the square game board.
     */
    /*@
      @ requires players != null && players.length == 2;
      @ requires DIM > 0;
      @ ensures getBoard().getDIM() == DIM;
      @ ensures getCurrentPlayer() == 0;
      @*/

    public DotsAndBoxesGame(Player[] players, int DIM){
        this.players = players;
        this.currentPlayer = 0;
        this.board = new Board(DIM);
    }

    /**
     * Returns the index of the current player.
     *
     * @return The index of the current player in the players array.
     */
    /*@ pure @*/
    public int getCurrentPlayer(){
        return currentPlayer;
    }

    /**
     * Determines the line color associated with a given player.
     *
     * @param player The player whose line color is to be determined.
     * @return The line color of the specified player.
     */
    /*@
      @ requires player != null;
      @ ensures player == players[0] ==> \result == Line.BLUE;
      @ ensures player != players[0] ==> \result == Line.RED;
      @*/
    public Line getLine(Player player){
        if (player == players[0]){
            return Line.BLUE;
        }
        return Line.RED;
    }

    /**
     * Returns the game board.
     *
     * @return The current state of the game board.
     */
    /*@ pure @*/
    public Board getBoard(){return board;}

    /**
     * Checks if the game is over.
     *
     * @return True if the game is over, otherwise false.
     */
    /*@
      @ ensures \result == board.gameOver();
      @*/
    @Override
    public boolean gameOver() {
        return board.gameOver();
    }

    /**
     * Returns the player whose turn it is.
     *
     * @return The current player.
     */
    /*@ pure @*/
    @Override
    public Player getTurn() {
        return players[currentPlayer];
    }

    /**
     * Determines the winner of the game.
     *
     * @return The winning player, or null if there is no winner yet or if it's a draw.
     */
    /*@
      @ ensures !board.hasWinner() ==> \result == null;
      @ ensures board.getScore(Line.BLUE) > board.getScore(Line.RED) ==> \result == players[0];
      @ ensures board.getScore(Line.RED) > board.getScore(Line.BLUE) ==> \result == players[1];
      @ ensures board.getScore(Line.RED) == board.getScore(Line.BLUE) ==> \result == null;
      @*/

    @Override
    public Player getWinner() {
        if (!board.hasWinner()) {
            return null; // No winner yet
        }
        int scorePlayer1 = board.getScore(Line.BLUE);
        int scorePlayer2 = board.getScore(Line.RED);

        if (scorePlayer1 > scorePlayer2) {
            return players[0];
        } else if (scorePlayer2 > scorePlayer1) {
            return players[1];
        }
        return null; // It's a draw if scores are equal
    }

    /**
     * Generates a list of valid moves that can be made by the current player.
     *
     * @return A list of all valid moves for the current player.
     */
    /*@
      @ ensures \result != null;
      @ ensures (\forall int i; i >= 0 && i < \result.size(); validMove(\result.get(i)) && \result.get(i).getLine() == getLine(getTurn()));
      @*/

    @Override
    public List<DotsAndBoxesMove> getValidMoves() {
        List<DotsAndBoxesMove> validMoves = new ArrayList<>();
        int dimension = board.getDIM();

        // Loop through each dot on the board to check potential moves
        for (int i = 0; i < dimension * dimension; i++) {
            int row = i / dimension;
            int col = i % dimension;

            // Check for horizontal line: Ensures the line doesn't wrap around the right edge of the board
            if (col < dimension - 1) {
                int end = i + 1; // The dot next to the current dot horizontally
                // If there's no line between these two dots, it's a valid move
                if (board.getLine(i, end) == Line.EMPTY) {
                    validMoves.add(new DotsAndBoxesMove(getLine(getTurn()), i, end));
                }
            }

            // Check for vertical line: Ensures the line doesn't go beyond the bottom edge of the board
            if (row < dimension - 1) {
                int end = i + dimension; // The dot directly below the current dot
                // If there's no line between these two dots, it's a valid move
                if (board.getLine(i, end) == Line.EMPTY) {
                    validMoves.add(new DotsAndBoxesMove(getLine(getTurn()), i, end));
                }
            }
        }

        return validMoves; // Return the list of all valid moves
    }

    /**
     * Creates a deep copy of the current game state.
     *
     * @return A new DotsAndBoxesGame instance with the same state as this one.
     */
    /*@
      @ ensures \result != null && \result instanceof DotsAndBoxesGame;
      @ ensures \result.getBoard().equals(board.deepCopy()) && \result.getCurrentPlayer() == currentPlayer;
      @*/

    public DotsAndBoxesGame deepCopy(){
        Player[] playersCopy = Arrays.copyOf(this.players, this.players.length);
        DotsAndBoxesGame copy = new DotsAndBoxesGame(playersCopy, this.board.getDIM());
        copy.currentPlayer = this.currentPlayer;
        copy.board = this.board.deepCopy();
        return copy;
    }

    /**
     * Checks if a given move is valid according to the game rules.
     *
     * @param move The move to be checked.
     * @return True if the move is valid, otherwise false.
     */
    /*@
      @ requires move != null;
      @ ensures \result == (\exists int start, end;
                           start == ((DotsAndBoxesMove)move).getStart() &&
                           end == ((DotsAndBoxesMove)move).getEnd();
                           board.isValidDot(start) && board.isValidDot(end) &&
                           board.getLine(start, end) == Line.EMPTY);
      @*/


    @Override
    public boolean validMove(Move move) {
        if (!(move instanceof DotsAndBoxesMove)) {
            return false; // Early return if move is not an instance of DotsAndBoxesMove
        }

        DotsAndBoxesMove dotsAndBoxesMove = (DotsAndBoxesMove) move;
        int start = dotsAndBoxesMove.getStart();
        int end = dotsAndBoxesMove.getEnd();
        int dimension = board.getDIM();
        int boardSize = dimension * dimension;

        // Check if start and end are within the board's boundaries
        if (start < 0 || start >= boardSize || end < 0 || end >= boardSize) {
            return false;
        }

        // Determine the type of move (horizontal or vertical)
        int difference = Math.abs(start - end);
        if (difference == 1) {
            // Horizontal move: check for wrapping around the right edge
            return isHorizontalMoveValid(start, end, dimension);
        } else if (difference == dimension) {
            // Vertical move
            return board.getLine(start, end) == Line.EMPTY;
        }
        return false;
    }

    /**
     * Executes a move if it is valid, updating the game state accordingly.
     *
     * @param move The move to be executed.
     */
    /*@
      @ requires move != null && validMove(move);
      @ ensures (\old(isValidDotsAndBoxesMove(move)) ==>
                (\exists int start, end;
                 start == ((DotsAndBoxesMove)move).getStart() &&
                 end == ((DotsAndBoxesMove)move).getEnd();
                 board.getLine(start, end) != Line.EMPTY));
      @*/

    @Override
    public void doMove(Move move) {
        if (isValidDotsAndBoxesMove(move)) {
            DotsAndBoxesMove dotsAndBoxesMove = (DotsAndBoxesMove) move;

            if (dotsAndBoxesMove.getIndex() == 0) {
                setLineAndCheckSquare(dotsAndBoxesMove.getStart(), dotsAndBoxesMove.getEnd(), dotsAndBoxesMove.getLine());
            } else {
                List<Integer> linePoints = board.getPoints(dotsAndBoxesMove.getIndex());
                dotsAndBoxesMove.setStart(linePoints.get(0));
                dotsAndBoxesMove.setEnd(linePoints.get(1));
                setLineAndCheckSquare(dotsAndBoxesMove.getStart(), dotsAndBoxesMove.getEnd(), dotsAndBoxesMove.getLine());
            }
        }
    }

    /**
     * Checks whether a move is a valid Dots and Boxes move according to the game rules.
     *
     * @param move The move to be checked.
     * @return True if the move is a valid Dots and Boxes move, false otherwise.
     */
    /*@
      @ requires move != null;
      @ ensures \result == move instanceof DotsAndBoxesMove && validMove(move);
      @*/

    public boolean isValidDotsAndBoxesMove(Move move) {
        return move instanceof DotsAndBoxesMove && validMove(move);
    }

    /**
     * Sets a line on the board between two points and checks if a square is completed.
     * Updates the current player if no square is completed.
     *
     * @param start The start point of the line.
     * @param end The end point of the line.
     * @param line The line color to be set.
     */
    /*@
      @ requires board.isValidDot(start) && board.isValidDot(end) && (line == Line.BLUE || line == Line.RED);
      @ requires board.getLine(start, end) == Line.EMPTY;
       ensures board.getLine(start, end) == line;
       ensures board.checkSquare(start, end) || currentPlayer != \old(currentPlayer);
      */
    private void setLineAndCheckSquare(int start, int end, Line line) {
        board.doMove(start, end, line);
        if (!board.checkSquare(start, end)) {
            currentPlayer = (currentPlayer + 1) % 2;
        }
    }
    /**
     * Validates a horizontal move between two points, ensuring it does not wrap around the board.
     *
     * @param start     The start point of the horizontal line.
     * @param end       The end point of the horizontal line.
     * @param dimension The dimension of the board.
     * @return True if the move is valid, false if it wraps around the edge of the board.
     */
    /*@
      @ requires board.isValidDot(start) && board.isValidDot(end);
      @ ensures \result == ((start % dimension != dimension - 1) && board.getLine(start, end) == Line.EMPTY);
      @*/


    private boolean isHorizontalMoveValid(int start, int end, int dimension) {
        if ((start % dimension) == (dimension - 1)) {
            return false; // Invalid if wrapping around the right edge
        }
        return board.getLine(start, end) == Line.EMPTY;
    }

    /**
     * Provides a string representation of the game's current state, including player scores, whose turn it is, and valid moves.
     *
     * @return A string detailing the current state of the game.
     */
    /*@
      @ ensures \result != null;
      @*/

    @Override
    public String toString(){
        if (getLine(getTurn()) == Line.BLUE){
            return String.format(players[currentPlayer] + "'s score: " + board.getScore(Line.BLUE) + "\n" + players[currentPlayer + 1] + "'s score: " + board.getScore(Line.RED) + "\n" + "\u001B[34m" + players[currentPlayer] +  "'s turn\n" + "\u001B[0m"  +  "\n" + players[currentPlayer] + "'s valid moves are: " + getValidMoves() + "\n\n"  + getBoard() + "\n" + "What is your move in format [start-number]?\n" );
        }
        return String.format(players[currentPlayer - 1] + "'s score: " + board.getScore(Line.BLUE) + "\n" + players[currentPlayer] + "'s score: " + board.getScore(Line.RED) + "\n" + "\u001B[31m" + players[currentPlayer] +  "'s turn\n" + "\u001B[0m"  +  "\n" + players[currentPlayer] + "'s valid moves are: " + getValidMoves() + "\n\n"  + getBoard() + "\n" + "What is your move in format [start-number]?\n" );
    }

}
