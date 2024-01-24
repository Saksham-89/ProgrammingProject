package ProgrammingProject;

import java.util.List;

/**
 * Represents a game of Dots and Boxes.
 * This class manages the game state, including the game board, the current player, and each player's score.
 */

public class DotsAndBoxesGame {

    private Board board;
    private int currentPlayer;
    private int player1Score;
    private int player2Score;

    /**
     * Constructs a new Dots and Boxes game.
     * Initializes the game board and sets player 1 as the starting player.
     */

    public DotsAndBoxesGame() {
        board = new Board();
        currentPlayer = 1; // Player 1 starts
        player1Score = 0;
        player2Score = 0;
    }

    /**
     * Checks if the game is over.
     * @return true if all fields on the board are filled, false otherwise.
     */

    public boolean isGameOver() {
        // Check if all fields on the board are filled
        for (int field = 0; field < Board.DIM * Board.DIM; field++) {
            if (!board.isFilled(field)) {
                return false; // Found an unfilled field, the game is not over
            }
        }
        return true; // All fields are filled, the game is over
    }

    /**
     * Retrieves a list of valid moves.
     * @return a list of integers representing valid move positions.
     */

    public List<Integer> getValidMoves() {
        return board.getValidMoves();
    }

    /**
     * Checks if a move is valid.
     * @param field the field to check for validity.
     * @return true if the move is valid, false otherwise.
     */

    public boolean isValidMove(int field) {
        return board.isField(field) && !board.isFilled(field);
    }

    /**
     * Executes a move in the game.
     * Updates the board, checks for completed boxes, switches players, and logs scores.
     * @param field the field where the move is to be made.
     */

    public void doMove(int field) {
        if (isValidMove(field)) {
            board.fill(field);
            checkForBoxes();
            switchPlayer();
            logScores();
        }
    }

    /**
     * Logs the current scores of both players.
     */
    private void logScores() {
        System.out.println("Current Scores:");
        System.out.println("Player 1: " + player1Score);
        System.out.println("Player 2: " + player2Score);
    }

    /**
     * Retrieves the current game board.
     * @return the current state of the game board.
     */

    public Board getBoard() {
        return board;
    }

    /**
     * Retrieves the current player.
     * @return the number representing the current player.
     */

    public int getCurrentPlayer(){
        return currentPlayer;
    }

    /**
     * Creates a deep copy of this game instance.
     * @return a new DotsAndBoxesGame instance with the same state as the current game.
     */

    public DotsAndBoxesGame deepCopy() {
        DotsAndBoxesGame copy = new DotsAndBoxesGame();
        copy.board = board.deepCopy();
        copy.currentPlayer = currentPlayer;
        copy.player1Score = player1Score;
        copy.player2Score = player2Score;
        return copy;
    }

    /**
     * Checks the board for completed boxes and updates the current player's score.
     */

    private void checkForBoxes() {
        for (int row = 0; row < Board.DIM - 1; row++) {
            for (int col = 0; col < Board.DIM - 1; col++) {
                int boxTopLeft = row * Board.DIM + col;

                // Check if the box is completed
                if (board.isFilled(boxTopLeft) &&
                        board.isFilled(boxTopLeft + 1) &&
                        board.isFilled(boxTopLeft + Board.DIM) &&
                        board.isFilled(boxTopLeft + Board.DIM + 1)) {

                    // Update the player's score
                    if (currentPlayer == 1) {
                        player1Score++;
                    } else {
                        player2Score++;
                    }
                }
            }
        }
    }

    /**
     * Switches the current player.
     */

    private void switchPlayer() {
        currentPlayer = (currentPlayer == 1) ? 2 : 1;
    }

    /**
     * Retrieves the score of player 1.
     * @return the score of player 1.
     */

    public int getPlayer1Score() {
        return player1Score;
    }

    /**
     * Retrieves the score of player 2.
     * @return the score of player 2.
     */

    public int getPlayer2Score() {
        return player2Score;
    }
}
