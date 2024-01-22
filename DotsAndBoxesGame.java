package ProgrammingProject;

import java.util.List;

public class DotsAndBoxesGame {

    private Board board;
    private int currentPlayer;
    private int player1Score;
    private int player2Score;

    public DotsAndBoxesGame() {
        board = new Board();
        currentPlayer = 1; // Player 1 starts
        player1Score = 0;
        player2Score = 0;
    }

    public boolean isGameOver() {
        // Check if all fields on the board are filled
        for (int field = 0; field < Board.DIM * Board.DIM; field++) {
            if (!board.isFilled(field)) {
                return false; // Found an unfilled field, the game is not over
            }
        }
        return true; // All fields are filled, the game is over
    }

    public List<Integer> getValidMoves() {
        return board.getValidMoves();
    }

    public boolean isValidMove(int field) {
        return board.isField(field) && !board.isFilled(field);
    }

    public void doMove(int field) {
        if (isValidMove(field)) {
            board.fill(field);
            checkForBoxes();
            switchPlayer();
            logScores();
        }
    }
    private void logScores() {
        System.out.println("Current Scores:");
        System.out.println("Player 1: " + player1Score);
        System.out.println("Player 2: " + player2Score);
    }

    public Board getBoard() {
        return board;
    }

    public int getCurrentPlayer(){
        return currentPlayer;
    }

    public DotsAndBoxesGame deepCopy() {
        DotsAndBoxesGame copy = new DotsAndBoxesGame();
        copy.board = board.deepCopy();
        copy.currentPlayer = currentPlayer;
        copy.player1Score = player1Score;
        copy.player2Score = player2Score;
        return copy;
    }

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

    private void switchPlayer() {
        currentPlayer = (currentPlayer == 1) ? 2 : 1;
    }

    public int getPlayer1Score() {
        return player1Score;
    }

    public int getPlayer2Score() {
        return player2Score;
    }
}
