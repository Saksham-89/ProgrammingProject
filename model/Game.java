package ProgrammingProject.model;

import java.util.List;


/**
 * Defines the common behavior for a game, including methods to check game state,
 * determine turns, evaluate and execute moves.
 */

public interface Game {
    /**
     * Checks if the game is over.
     *
     * @return True if the game has ended, false otherwise.
     */
    /*@ pure @*/

    boolean gameOver();
    /**
     * Returns the player whose turn it is.
     *
     * @return The current player.
     */
    /*@ pure @*/

    Player getTurn();

    /**
     * Determines the winner of the game.
     *
     * @return The player who won the game, or null if there is no winner yet or the game is a draw.
     */
    /*@ pure @*/

    Player getWinner();

    /**
     * Generates a list of all valid moves that can be made by the current player.
     *
     * @return A list of valid moves for the current player.
     */
    /*@
      @ ensures \result != null;
      @ ensures (\forall int i; i >= 0 && i < \result.size(); validMove(\result.get(i)));
      @*/

    List<? extends Move> getValidMoves();

    /**
     * Checks if a given move is valid according to the game rules.
     *
     * @param move The move to be checked.
     * @return True if the move is valid, false otherwise.
     */
    /*@
      @ requires move != null;
      @ ensures \result ==> (\exists Move validMove; validMove.equals(move); getValidMoves().contains(validMove));
      @*/

    boolean validMove(Move move);

    /**
     * Executes a move, updating the game state accordingly.
     *
     * @param move The move to be executed.
     */
    /*@
      @ requires move != null && validMove(move);
      @ ensures gameOver() || getTurn() != \old(getTurn());
      @*/

    void doMove(Move move);
}
